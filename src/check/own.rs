//! The ownership pass (milestone 3): moves, borrows, mutability, class and task captures.
//!
//! Runs after type checking, over each function body, using the types the checker recorded.
//! Every value carries the set of *loans* (borrows) it holds; a loan stays live while any
//! binding holding it may still be used, and every access to a place is checked against the
//! live loans that conflict with it (§4.1). Liveness uses the program's structure: a later use
//! is reachable from a point unless they are in different arms of the same branch, and a loop
//! makes every use of a binding declared outside it reachable (its back edge).

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::env::{FnId, Program, Typed};
use super::types::*;
use crate::diag::{Span, SpanMap, SpanSet};
use crate::syntax::ast::{self, Expr, ExprKind, Pattern, PatternKind, Stmt, TagArgs, TagPatArgs};

type VarId = usize;
type LoanId = usize;
/// A closure being checked: the bindings it captures from outside, and the strongest use its
/// body makes of each.
type LambdaFrame = (HashSet<VarId>, HashMap<VarId, (Use, Span)>);

/// What a closure is for, where that changes how it captures (§6.1).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    Plain,
    /// The body of `Io.scope`: its tasks may borrow what is outside it.
    ScopeBody,
    /// A task given to `spawn` or `fork`: it moves in what is declared inside its scope.
    Task,
}

/// A position in the program's structure: the chain of enclosing constructs, each with the
/// index of the child taken.
type Chain = Vec<(u32, Node, u32)>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Node {
    Seq,
    Branch,
    Loop,
}

#[derive(Clone, Debug)]
struct Var {
    name: String,
    ty: Ty,
    mutable: bool,
    /// Where it was declared, for the loop rule.
    chain: Chain,
    param: bool,
    /// A value lent with no place of its own (§5.6), which has no name to report.
    temp: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Path {
    root: VarId,
    fields: Vec<String>,
}

impl Path {
    fn overlaps(&self, other: &Path) -> bool {
        self.root == other.root && self.fields.iter().zip(&other.fields).all(|(a, b)| a == b)
    }
}

#[derive(Clone, Debug)]
struct Loan {
    path: Path,
    mutable: bool,
    span: Span,
    /// A borrow-typed parameter's own loan from the caller: it flows with the parameter's value
    /// (for the return check) but never conflicts inside the function.
    external: bool,
    /// A `mut` loan of an element of a list, which lends the whole list.
    element: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Use {
    /// The value is moved (or copied, if `Copy`).
    Move,
    /// The value is lent `readonly`.
    Read,
    /// The value is lent `mut`.
    Mut,
}

#[derive(Clone, Default, Debug)]
struct Val {
    loans: BTreeSet<LoanId>,
}

/// Flow-sensitive state: which places are moved, and which loans each binding holds.
#[derive(Clone, Default, Debug, PartialEq)]
struct State {
    moved: BTreeSet<Path>,
    holds: HashMap<VarId, BTreeSet<LoanId>>,
}

impl State {
    fn join(&mut self, other: &State) {
        self.moved.extend(other.moved.iter().cloned());
        for (v, ls) in &other.holds {
            self.holds.entry(*v).or_default().extend(ls.iter().copied());
        }
    }
}

pub fn check_function(p: &mut Program, fid: FnId) {
    let Some(typed) = p.typed.get(&fid).cloned() else { return };
    let Some(fdecl) = p.fn_decl(fid) else { return };
    let Some(body) = fdecl.body else { return };
    p.note = p.spec_notes.get(&fid).cloned();
    let module = p.fns[fid].module;
    let ret_ty = p.fns[fid].scheme.ret.clone();
    let sources = result_sources(p, &p.fns[fid].scheme);
    let send_params = send_params(p, &p.fns[fid].scheme.tparams);
    let mut o = Own {
        p,
        module,
        typed,
        vars: Vec::new(),
        scopes: vec![HashMap::new()],
        uses: HashMap::new(),
        resolved: HashMap::new(),
        loans: Vec::new(),
        state: State::default(),
        chain: Vec::new(),
        next_node: 0,
        temps: Vec::new(),
        deferred: Vec::new(),
        made: Vec::new(),
        want: None,
        reported: HashSet::new(),
        lambdas: Vec::new(),
        escaping: false,
        resumes: HashMap::new(),
        cont_args: HashMap::new(),
        dead_args: HashMap::new(),
        lent_args: HashMap::new(),
        lambda_params: HashSet::new(),
        iterating: false,
        next_role: Role::Plain,
        roles: Vec::new(),
        task_moved: HashMap::new(),
        move_sites: BTreeMap::new(),
        lending_element: false,
        dying_holds: HashMap::new(),
        handling: Vec::new(),
        sites: HashMap::new(),
        ret_ty,
        sources,
        send_params,
        collecting: true,
        closure_modes: HashMap::new(),
        var_modes: HashMap::new(),
        moves: SpanMap::default(),
        captured_moves: SpanMap::default(),
        arm_binds: HashMap::new(),
        arm_moves: HashSet::new(),
        lending: false,
        lent_arms: SpanSet::default(),
    };
    // Pass 1 collects every use of every binding, with its position; pass 2 checks.
    for pass in 0..2 {
        o.collecting = pass == 0;
        o.scopes = vec![HashMap::new()];
        o.state = State::default();
        o.loans.clear();
        o.chain.clear();
        o.next_node = 0;
        o.temps.clear();
        o.deferred.clear();
        o.made.clear();
        for (i, (name, ty)) in o.typed.params.clone().into_iter().enumerate() {
            let id = o.declare_var(&name, ty.clone(), true, true, usize::MAX - i);
            // A parameter whose type can hide a borrow carries one too, so a `from` that leaves
            // it out is checked against what the body returns (§4.2).
            if o.p.class(&ty) == 2 || hides_borrows(&ty, o.p, &o.send_params) {
                o.loans.push(Loan { path: Path { root: id, fields: Vec::new() }, mutable: false, span: body.span, external: true, element: false });
                let l = o.loans.len() - 1;
                o.state.holds.insert(id, [l].into_iter().collect());
            }
        }
        o.escaping = true;
        // A result that is a borrow lends what the body ends with, as an argument would (§4.2).
        let how = o.result_use();
        let v = o.block(&body, how);
        o.escaping = false;
        if !o.collecting {
            o.check_return(&v, body.tail.as_ref().map_or(body.span, |e| e.span));
            if let Some(t) = &body.tail {
                let ret = o.ret_ty.clone();
                o.check_mode(t, &ret, "returned");
            }
        }
    }
    o.p.note = None;
    let moves = std::mem::take(&mut o.moves);
    let captured = std::mem::take(&mut o.captured_moves);
    let lent_arms = std::mem::take(&mut o.lent_arms);
    if let Some(t) = o.p.typed.get_mut(&fid) {
        t.moves = moves;
        t.captured_moves = captured;
        t.lent_arms = lent_arms;
    }
}

struct Own<'p> {
    p: &'p mut Program,
    module: usize,
    typed: Typed,
    vars: Vec<Var>,
    scopes: Vec<HashMap<String, VarId>>,
    /// Pass 1's record of each binding's uses, by the position in source order they occur.
    uses: HashMap<VarId, Vec<(usize, Chain)>>,
    /// Which binding each identifier refers to, by its span (filled in pass 1).
    resolved: HashMap<Span, VarId>,
    loans: Vec<Loan>,
    state: State,
    chain: Chain,
    next_node: u32,
    /// Loans held by values being evaluated (arguments in flight, the iterated generator).
    temps: Vec<BTreeSet<LoanId>>,
    /// Loans held by `defer`s, live to the end of their block (§5.6).
    deferred: Vec<BTreeSet<LoanId>>,
    /// The temporaries made by the statements being checked, innermost last: each ends with its
    /// statement, or its block's value (§5.6).
    made: Vec<VarId>,
    /// The type the value of the block about to be checked is wanted as.
    want: Option<Ty>,
    reported: HashSet<(Span, String)>,
    /// Closures being checked, innermost last.
    lambdas: Vec<LambdaFrame>,
    /// Set while evaluating a value that escapes (returned, or stored in a first-class value): a
    /// closure there captures by move (§4.3).
    escaping: bool,
    /// For each continuation binding, the outer bindings its handler's body and arms use, and
    /// whether any of them changes each: calling it re-enters them (§5.3).
    resumes: HashMap<VarId, Vec<(VarId, bool)>>,
    /// For each continuation binding, its arm's parameters that may hold a borrow, with the loan
    /// each holds on itself: they borrow from where the operation was performed, which may end
    /// once the continuation resumes it (§5.3).
    cont_args: HashMap<VarId, Vec<(VarId, LoanId)>>,
    /// Parameters of arms that do not resume and may hold a borrow, with their operation: the
    /// body they borrow from has unwound before such an arm runs (§5.3).
    dead_args: HashMap<VarId, String>,
    /// Arm parameters that may hold a borrow, with their operation, for diagnostics.
    lent_args: HashMap<VarId, String>,
    /// Closures' parameters: what a closure yields may borrow them, as a function's may borrow
    /// its parameters.
    lambda_params: HashSet<VarId>,
    /// Set while a `for…of` evaluates a generator call it iterates: the items it yields carry
    /// the call's sources' borrows, as a result would (§5.5).
    iterating: bool,
    /// The role of the closure about to be checked, and of each being checked, innermost last.
    next_role: Role,
    roles: Vec<Role>,
    /// Bindings a task moved in only because they are declared inside its scope, with where.
    task_moved: HashMap<VarId, Span>,
    /// Where each place was first moved, for what a later use of it reports.
    move_sites: BTreeMap<Path, Span>,
    /// Whether the place being lent `mut` is reached for one of its elements.
    lending_element: bool,
    /// What the bindings of the block being ended held.
    dying_holds: HashMap<VarId, BTreeSet<LoanId>>,
    /// The `handle`s whose bodies are being checked, innermost last: the effect each handles,
    /// and the loans live across any point where the body may perform it, which the body holds
    /// while suspended there (§5.3).
    handling: Vec<(usize, BTreeSet<LoanId>)>,
    /// Variable ids by declaration site, so they are the same in both passes and in every
    /// traversal of a loop body.
    sites: HashMap<(usize, String), VarId>,
    ret_ty: Ty,
    /// The parameters this function's result may borrow from (§4.2).
    sources: Vec<String>,
    /// Type parameters declared `extends Send`, by symbol id.
    send_params: Vec<u32>,
    collecting: bool,
    /// Each closure's mode, by its span, from what its body does with its captures (§4.3), with
    /// the capture that decided it; and the mode of bindings initialized with a closure.
    closure_modes: HashMap<Span, (FnMode, String)>,
    var_modes: HashMap<VarId, (FnMode, String)>,
    /// Each move out of a binding: the moving expression, and the field path moved.
    moves: SpanMap<Vec<String>>,
    /// The bindings each closure moves in, by the closure's span.
    captured_moves: SpanMap<Vec<(String, Ty)>>,
    /// The bindings a `match` arm on an owned place makes, with the arm's pattern; and the arms
    /// that move one, found in pass 1. Only those take the place (§4.1).
    arm_binds: HashMap<VarId, Span>,
    arm_moves: HashSet<Span>,
    /// Set while binding the pattern of an arm that borrows what it binds.
    lending: bool,
    /// Arms that borrow an owned place `mut`, to change what they bind in place, by pattern.
    lent_arms: SpanSet,
}

impl<'p> Own<'p> {
    fn err(&mut self, span: Span, msg: impl Into<String>) {
        if self.collecting {
            return;
        }
        let msg = msg.into();
        if self.reported.insert((span, msg.clone())) {
            self.p.error(self.module, span, msg);
        }
    }

    fn ty_of(&self, e: &Expr) -> Ty {
        self.typed.exprs.get(&e.span).cloned().unwrap_or(Ty::Error)
    }

    fn show(&self, t: &Ty) -> String {
        format!("{}", Show(t, &*self.p))
    }

    // ---- structure and liveness ----

    fn enter(&mut self, kind: Node, child: u32) -> u32 {
        self.next_node += 1;
        let id = self.next_node;
        self.chain.push((id, kind, child));
        id
    }

    fn leave(&mut self) {
        self.chain.pop();
    }

    fn set_child(&mut self, child: u32) {
        if let Some(last) = self.chain.last_mut() {
            last.2 = child;
        }
    }

    fn declare_var(&mut self, name: &str, ty: Ty, mutable: bool, param: bool, site: usize) -> VarId {
        let var = Var { name: name.to_string(), ty, mutable, chain: self.chain.clone(), param, temp: false };
        let id = match self.sites.get(&(site, name.to_string())) {
            Some(id) => {
                self.vars[*id] = var;
                *id
            }
            None => {
                self.vars.push(var);
                self.sites.insert((site, name.to_string()), self.vars.len() - 1);
                self.vars.len() - 1
            }
        };
        self.scopes.last_mut().expect("scope").insert(name.to_string(), id);
        self.state.holds.remove(&id);
        self.state.moved.retain(|p| p.root != id);
        id
    }

    fn lookup(&self, name: &str) -> Option<VarId> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    fn record_use(&mut self, v: VarId, at: Span) {
        if self.collecting {
            self.uses.entry(v).or_default().push((at.start, self.chain.clone()));
            self.resolved.insert(at, v);
        }
    }

    /// Whether a use at `(upos, uchain)` can happen after the point `(pos, chain)`.
    fn reachable(&self, var: &Var, pos: usize, chain: &Chain, upos: usize, uchain: &Chain) -> bool {
        // A loop enclosing both, which does not enclose the binding's declaration, can carry the
        // binding round to an earlier use.
        let common = chain.iter().zip(uchain).take_while(|(a, b)| a.0 == b.0).count();
        for (id, kind, _) in &chain[..common] {
            if *kind == Node::Loop && !var.chain.iter().any(|(d, _, _)| d == id) {
                return true;
            }
        }
        if upos <= pos {
            return false;
        }
        // Different arms of one branch are never both executed.
        if common < chain.len() && common < uchain.len() {
            let (a, b) = (&chain[common], &uchain[common]);
            if a.0 == b.0 && a.1 == Node::Branch && a.2 != b.2 {
                return false;
            }
        }
        true
    }

    /// Whether binding `v` may be used after the current point (pass 1's uses).
    fn live_after(&self, v: VarId, pos: usize) -> bool {
        let Some(uses) = self.uses.get(&v) else { return false };
        let var = &self.vars[v];
        uses.iter().any(|(upos, uchain)| self.reachable(var, pos, &self.chain, *upos, uchain))
    }

    /// The loans live at `pos`: held by values in flight, by `defer`s, or by a binding that may
    /// still be used.
    fn live_loans(&self, pos: usize, except: &BTreeSet<LoanId>) -> BTreeSet<LoanId> {
        let mut live: BTreeSet<LoanId> = self.temps.iter().chain(&self.deferred).flatten().copied().collect();
        for (v, ls) in &self.state.holds {
            if self.live_after(*v, pos) {
                live.extend(ls.iter().copied());
            }
        }
        live.retain(|l| !except.contains(l));
        live
    }

    /// Checks an access to `path` (a write if `write`, else a read; a borrow of mode `mode`)
    /// against the live loans.
    fn access(&mut self, path: &Path, write: bool, at: Span, except: &BTreeSet<LoanId>) {
        self.access_from(path, write, at, at.start, except);
    }

    /// `access`, for an access made at source position `pos`, reported at `at`.
    fn access_from(&mut self, path: &Path, write: bool, at: Span, pos: usize, except: &BTreeSet<LoanId>) {
        if self.collecting {
            return;
        }
        for l in self.live_loans(pos, except) {
            let loan = self.loans[l].clone();
            if loan.external || !loan.path.overlaps(path) {
                continue;
            }
            if loan.mutable || write {
                if self.vars[path.root].temp {
                    self.err(at, "this pass through the loop makes this value again, dropping the one made on an earlier pass, which is still borrowed: bind it with `const` before the loop");
                    return;
                }
                let name = self.path_name(path);
                let how = if loan.mutable { "lent `mut`" } else { "lent `readonly`" };
                let what = if write { "changed" } else { "used" };
                let (line, col) = crate::diag::line_col(&self.p.modules[self.module].source, loan.span.start);
                // Lending one element lends the list: two at once need a method that proves them apart.
                let hint = if loan.element || (write && self.lending_element) {
                    "; an element lent `mut` lends its whole list: to change two at once, `xs.swap(i, j)` exchanges them and `xs.splitAt(k)` lends two parts apart"
                } else {
                    ""
                };
                self.err(at, format!("`{name}` cannot be {what} here: it was {how} at {line}:{col}, and that borrow is still in use{hint}"));
                return;
            }
        }
    }

    fn path_name(&self, path: &Path) -> String {
        let mut s = self.vars[path.root].name.clone();
        for f in &path.fields {
            s.push('.');
            s.push_str(f);
        }
        s
    }

    fn new_loan(&mut self, path: Path, mutable: bool, span: Span) -> LoanId {
        self.loans.push(Loan { path, mutable, span, external: false, element: false });
        self.loans.len() - 1
    }

    // ---- places ----

    /// The place an expression denotes, if it is one: a binding, or fields of one.
    fn place(&self, e: &Expr) -> Option<Path> {
        match &e.kind {
            // Pass 1 has not resolved it yet where it is first met: the scope at hand does.
            ExprKind::Ident(name) => self.resolved.get(&e.span).copied().or_else(|| self.lookup(name)).map(|v| Path { root: v, fields: Vec::new() }),
            ExprKind::Field { target, name } => {
                let mut p = self.place(target)?;
                p.fields.push(name.name.clone());
                Some(p)
            }
            // Indexing borrows the whole collection; a tuple's element is a place of its own.
            ExprKind::Index { target, index } => {
                let mut p = self.place(target)?;
                let mut t = self.ty_of(target);
                while let Ty::Borrow(_, inner) = t {
                    t = *inner;
                }
                if let (ExprKind::Int(i), Ty::Tuple(_)) = (&index.kind, &t) {
                    p.fields.push(i.clone());
                }
                Some(p)
            }
            ExprKind::BorrowMut(inner) => self.place(inner),
            _ => None,
        }
    }

    fn is_tuple(&self, e: &Expr) -> bool {
        let mut t = self.ty_of(e);
        while let Ty::Borrow(_, inner) = t {
            t = *inner;
        }
        matches!(t, Ty::Tuple(_))
    }

    /// Whether the place is reached through a borrow or a region reference, so nothing can be
    /// moved out of it.
    fn behind_reference(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Ident(_) => {
                matches!(self.ty_of(e), Ty::Borrow(..)) || self.is_ref(&self.ty_of(e))
            }
            ExprKind::Field { target, .. } | ExprKind::Index { target, .. } => {
                let t = self.ty_of(target);
                matches!(t, Ty::Borrow(..)) || self.is_ref(&t) || self.behind_reference(target)
            }
            _ => false,
        }
    }

    fn is_ref(&self, t: &Ty) -> bool {
        matches!(t, Ty::Named(d, _) if self.p.known.get("Ref") == Some(d))
    }

    /// Whether a value of this type could hold a borrow (§4.2).
    fn may_hold(&self, t: &Ty) -> bool {
        if self.p.class(t) == 2 {
            return true;
        }
        hides_borrows(t, self.p, &self.send_params)
    }

    // ---- uses of places ----

    /// Moves, copies or lends the place `path` (denoted by `e`), returning the loans the result
    /// holds.
    /// Whether `root` is captured by the closure whose body is being checked.
    fn captured(&self, root: VarId) -> bool {
        self.lambdas.last().is_some_and(|(outer, _)| outer.contains(&root))
    }

    /// Records a closure body's use of a captured binding; the strongest use decides how the
    /// closure captures it (§4.3).
    fn record_capture(&mut self, root: VarId, how: Use, at: Span) {
        let rank = |u: Use| match u {
            Use::Read => 0,
            Use::Mut => 1,
            Use::Move => 2,
        };
        let ty = self.vars[root].ty.clone();
        // A by-value use of a `Copy` (or borrowed) value reads it: closures capture by reference.
        let how = if how == Use::Move && (self.p.is_copy(&ty) || matches!(ty, Ty::Borrow(..))) { Use::Read } else { how };
        if let Some((_, uses)) = self.lambdas.last_mut() {
            let entry = uses.entry(root).or_insert((how, at));
            if rank(how) > rank(entry.0) {
                *entry = (how, at);
            }
        }
    }

    fn use_place(&mut self, e: &Expr, path: Path, how: Use) -> Val {
        let ty = self.ty_of(e);
        self.use_place_as(e, path, how, ty)
    }

    /// `use_place`, for a value of type `ty`: a match arm's move of its scrutinee is made at the
    /// arm's pattern, where no expression's type is recorded.
    fn use_place_as(&mut self, e: &Expr, path: Path, how: Use, ty: Ty) -> Val {
        let at = e.span;
        if let Some(op) = self.dead_args.get(&path.root).cloned() {
            let name = self.vars[path.root].name.clone();
            self.err(at, format!("`{name}` cannot be used: an arm that does not resume runs after the body has unwound, and `{name}` may borrow from it (give `{op}` an owned parameter type, or resume)"));
        }
        if self.captured(path.root) {
            self.record_capture(path.root, how, at);
            // The closure owns what it moved in, so a move inside its body is the closure's to
            // record, for its drop flags.
            let var_ty = self.vars[path.root].ty.clone();
            if how == Use::Move && !self.collecting && !self.p.is_copy(&var_ty) && !matches!(var_ty, Ty::Borrow(..)) && !self.p.is_copy(&ty) {
                self.moves.insert(at, path.fields.clone());
            }
            if how == Use::Move && self.collecting && !self.p.is_copy(&var_ty) && !matches!(var_ty, Ty::Borrow(..))
                && let Some(arm) = self.arm_binds.get(&path.root)
            {
                self.arm_moves.insert(*arm);
            }
            return Val { loans: self.state.holds.get(&path.root).cloned().unwrap_or_default() };
        }
        let none = BTreeSet::new();
        // Using something moved.
        if let Some(m) = self.state.moved.iter().find(|m| m.overlaps(&path) || path.overlaps(m)).cloned() {
            let name = self.path_name(&path);
            let what = if m == path { format!("`{name}` was moved") } else { format!("`{}` was moved", self.path_name(&m)) };
            let why = match self.task_moved.get(&m.root) {
                Some(span) => {
                    let (line, col) = crate::diag::line_col(&self.p.modules[self.module].source, span.start);
                    format!(": the task at {line}:{col} moved it in, since it is declared inside the task's scope (declare it before `Io.scope` to lend it to the tasks instead)")
                }
                None => String::new(),
            };
            // Where it was moved, unless a task took it.
            let what = match self.move_sites.get(&m) {
                // The same code, on an earlier pass through a loop.
                Some(site) if why.is_empty() && site.start == at.start => format!("{what} here on an earlier pass through the loop"),
                Some(site) if why.is_empty() => {
                    let (line, col) = crate::diag::line_col(&self.p.modules[self.module].source, site.start);
                    format!("{what} at {line}:{col}")
                }
                _ => what,
            };
            self.err(at, format!("{what} and cannot be used here{why}"));
        }
        let held: BTreeSet<LoanId> = self.state.holds.get(&path.root).cloned().unwrap_or_default();
        match how {
            Use::Move => {
                let copy = self.p.is_copy(&ty);
                self.access(&path, !copy, at, &none);
                if !copy {
                    if self.behind_reference(e) {
                        let shown = self.show(&ty);
                        self.err(at, format!("cannot move a `{shown}` out of a borrow; it is not `Copy`"));
                    } else if !path.fields.is_empty() && self.has_drop_ancestor(&path) {
                        self.err(at, format!("cannot move `{}` out of a value whose type implements `Drop`", self.path_name(&path)));
                    } else if !self.collecting {
                        // A continuation moved may be resumed or dropped wherever it goes.
                        if path.fields.is_empty() {
                            self.check_lent(path.root, at, Some(self.vars[path.root].name.clone()));
                        }
                        self.state.moved.insert(path.clone());
                        self.move_sites.entry(path.clone()).or_insert(at);
                        // Where a value leaves its binding, the evaluator stops owning it there (§5.6).
                        self.moves.insert(at, path.fields.clone());
                    } else if let Some(arm) = self.arm_binds.get(&path.root) {
                        self.arm_moves.insert(*arm);
                    }
                }
                Val { loans: held }
            }
            Use::Read => {
                self.access(&path, false, at, &none);
                let l = self.new_loan(path, false, at);
                let mut loans = held;
                loans.insert(l);
                Val { loans }
            }
            Use::Mut => {
                self.check_mutable(&path, e);
                self.access(&path, true, at, &none);
                let l = self.new_loan(path, true, at);
                self.loans[l].element = self.lending_element;
                let mut loans = held;
                loans.insert(l);
                Val { loans }
            }
        }
    }

    /// An arm's parameters that may hold a borrow borrow from the code that performed the
    /// operation, which resuming the continuation `k` lets run on and dropping it unwinds: none may
    /// be used after `k` is resumed at `at`, or, when `moved` names it, given up there (§5.3).
    fn check_lent(&mut self, k: VarId, at: Span, moved: Option<String>) {
        if self.collecting {
            return;
        }
        for (param, l) in self.cont_args.get(&k).cloned().unwrap_or_default() {
            let holders: Vec<VarId> = self.state.holds.iter().filter(|(_, ls)| ls.contains(&l)).map(|(h, _)| *h).collect();
            if let Some(h) = holders.into_iter().find(|h| self.live_after(*h, at.end)) {
                let (pn, hn) = (self.vars[param].name.clone(), self.vars[h].name.clone());
                let what = if pn == hn { format!("`{pn}`") } else { format!("`{hn}`, which borrows `{pn}`,") };
                match &moved {
                    None => self.err(at, format!("{what} is used after this resumes the code that lent `{pn}`, which may end it")),
                    Some(kn) => self.err(at, format!("{what} is used after `{kn}` is given up here, which may resume or drop the code that lent `{pn}`")),
                }
            }
        }
    }

    fn has_drop_ancestor(&self, path: &Path) -> bool {
        // The root's type, and every field type on the way, must not implement Drop.
        let mut t = self.vars[path.root].ty.clone();
        for f in &path.fields {
            if let Ty::Named(d, _) = &t
                && self.p.has_drop(*d) {
                    return true;
                }
            t = field_type(self.p, &t, f).unwrap_or(Ty::Error);
        }
        false
    }

    /// Mutation through `path` requires a `let` binding, or a `mut` borrow on the way (§4.1).
    /// Whether `path` may be changed; true if the change writes through a `mut` borrow.
    fn check_mutable(&mut self, path: &Path, e: &Expr) -> bool {
        let var = self.vars[path.root].clone();
        match &var.ty {
            Ty::Borrow(true, _) => return true,
            Ty::Borrow(false, _) => {
                self.err(e.span, format!("cannot change `{}` through a `readonly` borrow", self.path_name(path)));
                return false;
            }
            _ => {}
        }
        // Through a field that is itself a borrow or a region reference.
        let mut t = var.ty.clone();
        for f in &path.fields {
            t = field_type(self.p, &t, f).unwrap_or(Ty::Error);
            match &t {
                Ty::Borrow(true, _) => return true,
                Ty::Borrow(false, _) => {
                    self.err(e.span, format!("cannot change `{}` through a `readonly` borrow", self.path_name(path)));
                    return false;
                }
                t if self.is_ref(t) => {
                    self.err(e.span, format!("cannot change `{}`: region data changes only through a `Cell`", self.path_name(path)));
                    return false;
                }
                _ => {}
            }
        }
        if !var.mutable {
            self.err(e.span, format!("cannot change `{}`: it is declared `const`", var.name));
        }
        false
    }

    // ---- statements and blocks ----

    fn block(&mut self, b: &ast::Block, how: Use) -> Val {
        let want = self.want.take();
        self.scopes.push(HashMap::new());
        let id = self.enter(Node::Seq, 0);
        let _ = id;
        let deferred_depth = self.deferred.len();
        let mut child = 0;
        let escaping = std::mem::replace(&mut self.escaping, false);
        for stmt in &b.stmts {
            child += 1;
            self.set_child(child);
            let mark = self.made.len();
            match stmt {
                Stmt::Let { mutable, pat, init, .. } => {
                    // A binding of a borrow type borrows its initializer; otherwise it takes it.
                    let how = match (&pat.kind, self.typed.bindings.get(&pat.span)) {
                        (PatternKind::Bind(_), Some(bt)) => {
                            let bt = bt.clone();
                            self.arg_use(&bt, &self.ty_of(init))
                        }
                        _ => Use::Move,
                    };
                    let v = self.expr(init, how);
                    self.bind_pattern(pat, &v, *mutable);
                    if let PatternKind::Bind(name) = &pat.kind
                        && let Some(m) = self.closure_mode(init)
                            && let Some(id) = self.lookup(name) {
                                self.var_modes.insert(id, m);
                            }
                }
                Stmt::Defer(e) => {
                    // A `defer` holds everything it borrows until the block ends (§5.6).
                    let first_loan = self.loans.len();
                    let v = self.expr(e, Use::Read);
                    let mut held = v.loans;
                    held.extend(first_loan..self.loans.len());
                    self.deferred.push(held);
                }
                Stmt::Expr(e) => {
                    self.expr(e, Use::Move);
                }
            }
            // The statement's temporaries end with it, unless what it binds may hold them: then
            // they end with the block, as the binding does (§5.6).
            match stmt {
                Stmt::Let { pat, init, .. } if self.p.class(&self.bound_ty(pat, init)) == 2 => {
                    let made: Vec<VarId> = self.made.drain(mark..).collect();
                    let scope = self.scopes.last_mut().expect("scope");
                    for t in made {
                        scope.insert(format!(" temporary {t}"), t);
                    }
                }
                Stmt::Let { span, .. } => self.end_temps(mark, None, span.end, &Val::default(), "is dropped at the end of its statement"),
                Stmt::Defer(e) | Stmt::Expr(e) => self.end_temps(mark, None, e.span.end, &Val::default(), "is dropped at the end of its statement"),
            }
        }
        child += 1;
        self.set_child(child);
        self.escaping = escaping;
        let v = match &b.tail {
            Some(e) => {
                let how = match &want {
                    Some(w) => self.part_use(w, e, how),
                    None => how,
                };
                self.expr(e, how)
            }
            None => Val::default(),
        };
        self.deferred.truncate(deferred_depth);
        self.leave();
        // Bindings going out of scope release what they hold, and must not be borrowed by
        // anything that outlives them: the block's value, or a binding used later (§4.2).
        if let Some(scope) = self.scopes.pop() {
            self.dying_holds.clear();
            for var in scope.values() {
                if let Some(ls) = self.state.holds.remove(var) {
                    self.dying_holds.insert(*var, ls);
                }
            }
            let dying: HashSet<VarId> = scope.values().copied().collect();
            self.check_outlives(&dying, b, &v);
        }
        v
    }

    /// Whether dropping a value of this type runs code — a `Drop` impl, here or in a part — which
    /// may read what the value borrows.
    fn drop_runs_code(&self, t: &Ty) -> bool {
        fn go(p: &Program, t: &Ty, inside: &mut Vec<Ty>) -> bool {
            match t {
                Ty::Named(d, args) => {
                    if p.has_drop(*d) {
                        return true;
                    }
                    if inside.contains(t) {
                        return false;
                    }
                    inside.push(t.clone());
                    args.iter().any(|a| matches!(a, GArg::Ty(t) if go(p, t, inside)))
                        || p.struct_fields(*d, args).unwrap_or_default().iter().any(|(_, t)| go(p, t, inside))
                }
                Ty::Tuple(ts) => ts.iter().any(|t| go(p, t, inside)),
                Ty::Record(r) | Ty::Union(r) => r.labels.values().any(|t| go(p, t, inside)),
                Ty::Array(t, _) => go(p, t, inside),
                _ => false,
            }
        }
        go(self.p, t, &mut Vec::new())
    }

    fn check_outlives(&mut self, dying: &HashSet<VarId>, b: &ast::Block, v: &Val) {
        self.check_outlives_at(dying, b.tail.as_deref(), b.span.end, v, "goes out of scope at the end of its block");
    }

    /// No borrow of a binding in `dying`, which ends at `end`, may outlive it: not in `v`, the
    /// value `tail` gives, nor in a binding used after `end`. `ends` says how the binding ends.
    fn check_outlives_at(&mut self, dying: &HashSet<VarId>, tail: Option<&Expr>, end: usize, v: &Val, ends: &str) {
        if self.collecting || dying.is_empty() {
            return;
        }
        let on_dying = |o: &Self, l: &LoanId| !o.loans[*l].external && dying.contains(&o.loans[*l].path.root);
        // A function's own body is the return check's to judge.
        if self.scopes.len() > 1
            && let Some(tail) = tail
            && self.may_hold(&self.ty_of(tail))
            && let Some(l) = v.loans.iter().find(|l| on_dying(self, l)).copied()
        {
            let root = self.loans[l].path.root;
            let name = self.shown_root(root);
            let msg = match self.lent_args.get(&root) {
                Some(op) => format!("this value borrows {name}, which the code that performed `{op}` lent only to this arm"),
                None => format!("this value borrows {name}, which {ends}"),
            };
            self.err(tail.span, msg);
        }
        // Bindings are dropped in reverse order of declaration: one whose destructor runs code
        // must not borrow a binding declared after it, which is gone by then (§5.6).
        let mut dying_sorted: Vec<VarId> = dying.iter().copied().collect();
        dying_sorted.sort();
        for &h in &dying_sorted {
            let Some(ls) = self.dying_holds.get(&h).cloned() else { continue };
            let moved = self.state.moved.iter().any(|m| m.root == h && m.fields.is_empty());
            if moved || !self.drop_runs_code(&self.vars[h].ty.clone()) {
                continue;
            }
            if let Some(l) = ls.iter().find(|l| {
                let loan = &self.loans[**l];
                !loan.external && loan.path.root > h && dying.contains(&loan.path.root)
            }) {
                let loan = self.loans[*l].clone();
                let (hn, an) = (self.vars[h].name.clone(), self.vars[loan.path.root].name.clone());
                self.err(loan.span, format!("`{hn}` borrows `{an}` here, but `{an}` is dropped before `{hn}`'s destructor runs, since it is declared after it: declare `{an}` first"));
            }
        }
        let holders: Vec<(VarId, BTreeSet<LoanId>)> = self.state.holds.iter().map(|(h, ls)| (*h, ls.clone())).collect();
        for (h, ls) in holders {
            if let Some(l) = ls.iter().find(|l| on_dying(self, l)).copied()
                && self.live_after(h, end)
            {
                let loan = self.loans[l].clone();
                let holder = self.vars[h].name.clone();
                let msg = if self.vars[loan.path.root].temp {
                    format!("`{holder}` borrows a temporary here, which {ends}, and `{holder}` is used after that: give `{holder}` an owned type, or bind the value with `const` first")
                } else {
                    let name = self.vars[loan.path.root].name.clone();
                    format!("`{holder}` borrows `{name}` here, and is used after `{name}` goes out of scope")
                };
                self.err(loan.span, msg);
            }
        }
    }

    fn bind_pattern(&mut self, pat: &Pattern, v: &Val, mutable: bool) {
        match &pat.kind {
            PatternKind::TagAt { .. } => {}
            PatternKind::Bind(name) => {
                let ty = self.typed.bindings.get(&pat.span).cloned().unwrap_or(Ty::Error);
                let id = self.declare_var(name, ty.clone(), mutable, false, pat.span.start);
                if self.lending || self.may_hold(&ty) {
                    self.state.holds.insert(id, v.loans.clone());
                }
            }
            PatternKind::Wild | PatternKind::Lit(_) => {}
            PatternKind::Tuple(ps) | PatternKind::Or(ps) => {
                for p in ps {
                    self.bind_pattern(p, v, mutable);
                }
            }
            PatternKind::Record { fields, .. } => {
                for (name, sub) in fields {
                    match sub {
                        Some(p) => self.bind_pattern(p, v, mutable),
                        None => {
                            let fake = Pattern { kind: PatternKind::Bind(name.name.clone()), span: name.span };
                            self.bind_pattern(&fake, v, mutable);
                        }
                    }
                }
            }
            PatternKind::Tag { args, .. } => match args {
                TagPatArgs::None => {}
                TagPatArgs::Tuple(ps) => {
                    for p in ps {
                        self.bind_pattern(p, v, mutable);
                    }
                }
                TagPatArgs::Record(fs) => {
                    for (name, sub) in fs {
                        match sub {
                            Some(p) => self.bind_pattern(p, v, mutable),
                            None => {
                                let fake = Pattern { kind: PatternKind::Bind(name.name.clone()), span: name.span };
                                self.bind_pattern(&fake, v, mutable);
                            }
                        }
                    }
                }
            },
        }
    }

    // ---- expressions ----

    fn expr(&mut self, e: &Expr, how: Use) -> Val {
        // Only these positions pass "escaping" on to their direct value.
        let passes_escape = matches!(
            e.kind,
            ExprKind::Lambda { .. }
                | ExprKind::Block(_)
                | ExprKind::If { .. }
                | ExprKind::Match { .. }
                | ExprKind::Try { .. }
                | ExprKind::Region { .. }
                | ExprKind::Unsafe(_)
                | ExprKind::Return(_)
                | ExprKind::Record { .. }
                | ExprKind::Tag { .. }
                | ExprKind::List(_)
        );
        if !passes_escape && self.escaping {
            return self.contained(|o| o.expr(e, how));
        }
        if how != Use::Move && self.lends_temporary(e) {
            let v = self.value(e, how);
            return self.temporary(e, v, how);
        }
        self.value(e, how)
    }

    /// Whether lending `e` lends a temporary: a value with no place of its own, not a borrow
    /// already (§5.6).
    fn lends_temporary(&self, e: &Expr) -> bool {
        let fresh = !matches!(
            e.kind,
            ExprKind::Ident(_)
                | ExprKind::Field { .. }
                | ExprKind::FieldAt { .. }
                | ExprKind::TagAt { .. }
                | ExprKind::Index { .. }
                | ExprKind::BorrowMut(_)
                | ExprKind::Str(_)
                | ExprKind::TypeRef(_)
                | ExprKind::Return(_)
                | ExprKind::Throw(_)
                | ExprKind::Break
                | ExprKind::Continue
                | ExprKind::Comptime(_)
        );
        fresh && !matches!(self.ty_of(e), Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str | Prim::Void | Prim::Never) | Ty::Error)
    }

    /// A value lent with no place of its own: a binding with no name, lent, which ends with the
    /// statement it is made in, or the value of the block it is made in, unless what a `let` binds
    /// may hold it (§5.6).
    fn temporary(&mut self, e: &Expr, v: Val, how: Use) -> Val {
        let ty = self.ty_of(e);
        let key = (e.span.start, format!(" temporary {}", e.span.end));
        let id = match self.sites.get(&key) {
            Some(id) => *id,
            None => {
                self.vars.push(Var { name: "a temporary".to_string(), ty: Ty::Error, mutable: true, chain: Vec::new(), param: false, temp: true });
                self.sites.insert(key, self.vars.len() - 1);
                self.vars.len() - 1
            }
        };
        // Made again by a later pass through a loop, it replaces the one made before.
        let path = Path { root: id, fields: Vec::new() };
        self.access(&path, true, e.span, &BTreeSet::new());
        self.vars[id] = Var { name: "a temporary".to_string(), ty: ty.clone(), mutable: true, chain: self.chain.clone(), param: false, temp: true };
        self.state.moved.retain(|p| p.root != id);
        if self.may_hold(&ty) {
            self.state.holds.insert(id, v.loans.clone());
        } else {
            self.state.holds.remove(&id);
        }
        self.made.push(id);
        let l = self.new_loan(path, how == Use::Mut, e.span);
        let mut loans = v.loans;
        loans.insert(l);
        Val { loans }
    }

    /// The temporaries made since `mark` end at `end`: nothing may still borrow them, nor the value
    /// `tail` gives, `v` (§5.6).
    fn end_temps(&mut self, mark: usize, tail: Option<&Expr>, end: usize, v: &Val, ends: &str) {
        let made: Vec<VarId> = self.made.drain(mark..).collect();
        if made.is_empty() {
            return;
        }
        self.dying_holds.clear();
        for t in &made {
            if let Some(ls) = self.state.holds.remove(t) {
                self.dying_holds.insert(*t, ls);
            }
        }
        let dying: HashSet<VarId> = made.into_iter().collect();
        self.check_outlives_at(&dying, tail, end, v, ends);
        // Reported if anything still borrows them, they are gone.
        for ls in self.state.holds.values_mut() {
            ls.retain(|l| !dying.contains(&self.loans[*l].path.root));
        }
    }

    /// A block whose value is the value of `whole`, a branch or a body of it.
    fn block_as(&mut self, b: &ast::Block, how: Use, whole: &Expr) -> Val {
        self.want = Some(self.ty_of(whole));
        self.block(b, how)
    }

    /// How a part whose value is the value of a whole of type `whole` — a branch's, an arm's, a
    /// block's — is used: an owned value where the whole is a borrow is lent, in a temporary.
    fn part_use(&self, whole: &Ty, part: &Expr, how: Use) -> Use {
        let lends = |t: &Ty| matches!(t, Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str));
        let pt = self.ty_of(part);
        if how != Use::Move || !lends(whole) || lends(&pt) || matches!(pt, Ty::Prim(Prim::Void | Prim::Never) | Ty::Error) {
            return how;
        }
        if matches!(whole, Ty::Borrow(true, _)) { Use::Mut } else { Use::Read }
    }

    /// What a `let` binds: a name's declared type, or the value a pattern takes apart.
    fn bound_ty(&self, pat: &Pattern, init: &Expr) -> Ty {
        match (&pat.kind, self.typed.bindings.get(&pat.span)) {
            (PatternKind::Bind(_), Some(t)) => t.clone(),
            _ => self.ty_of(init),
        }
    }

    /// The name of what a loan is on, for a diagnostic.
    fn shown_root(&self, root: VarId) -> String {
        let var = &self.vars[root];
        if var.temp { var.name.clone() } else { format!("`{}`", var.name) }
    }

    fn value(&mut self, e: &Expr, how: Use) -> Val {
        match &e.kind {
            ExprKind::TypeRef(_) | ExprKind::FieldAt { .. } | ExprKind::TagAt { .. } => Val::default(),
            ExprKind::Ident(name) => {
                let Some(v) = self.lookup(name) else { return Val::default() };
                self.record_use(v, e.span);
                let path = Path { root: v, fields: Vec::new() };
                self.use_place(e, path, how)
            }
            ExprKind::Field { target, name } => {
                // Evaluate the base for its uses, then use the field place.
                match self.place(e) {
                    Some(path) => {
                        self.record_base_uses(target);
                        self.use_place(e, path, how)
                    }
                    None => {
                        let v = self.expr(target, Use::Read);
                        let _ = name;
                        v
                    }
                }
            }
            // A tuple's element by a constant index is a place, like a field.
            ExprKind::Index { target, index } if matches!(index.kind, ExprKind::Int(_)) && self.is_tuple(target) => match self.place(e) {
                Some(path) => {
                    self.record_base_uses(target);
                    self.use_place(e, path, how)
                }
                None => self.expr(target, Use::Read),
            },
            ExprKind::Index { target, index } => {
                let iv = self.expr(index, Use::Move);
                let _ = iv;
                let ranged = matches!(index.kind, ExprKind::Range { .. });
                let base_how = if how == Use::Mut { Use::Mut } else { Use::Read };
                let outer = std::mem::replace(&mut self.lending_element, how == Use::Mut);
                let v = self.expr(target, base_how);
                self.lending_element = outer;
                if how == Use::Move && !ranged {
                    let ty = self.ty_of(e);
                    if !self.p.is_copy(&ty) {
                        let shown = self.show(&ty);
                        self.err(e.span, format!("cannot move a `{shown}` out of an indexed place; it is not `Copy`"));
                    }
                }
                v
            }
            ExprKind::BorrowMut(inner) => self.expr(inner, Use::Mut),
            ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Byte(_) | ExprKind::Str(_) | ExprKind::Bool(_) => Val::default(),
            ExprKind::Template(pieces) => {
                for p in pieces {
                    if let ast::TemplatePiece::Expr(x) = p {
                        self.expr(x, Use::Read);
                    }
                }
                Val::default()
            }
            ExprKind::Tag { args, .. } => match args {
                TagArgs::None => Val::default(),
                TagArgs::Tuple(items) => self.collect(items.iter()),
                TagArgs::Record(fields) => self.field_inits(fields),
            },
            ExprKind::Record { fields, .. } => self.field_inits(fields),
            ExprKind::List(items) => self.collect(items.iter()),
            ExprKind::Range { lo, hi } => {
                for b in lo.iter().chain(hi.iter()) {
                    self.expr(b, Use::Read);
                }
                Val::default()
            }
            ExprKind::Unary { operand, .. } => {
                self.expr(operand, Use::Read);
                Val::default()
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expr(lhs, Use::Read);
                self.expr(rhs, Use::Read);
                Val::default()
            }
            ExprKind::Cast { expr, .. } => {
                self.expr(expr, Use::Read);
                Val::default()
            }
            ExprKind::Assign { op, target, value } => {
                // Into a place that is not a borrow, a borrow is read, not moved. A binding that
                // holds a `mut` borrow is assigned through: the place is what it refers to; so is a
                // field that holds one, given a value rather than another borrow.
                let place_ty = match self.ty_of(target) {
                    Ty::Borrow(true, inner) if matches!(target.kind, ExprKind::Ident(_)) || !matches!(self.ty_of(value), Ty::Borrow(..)) => *inner,
                    t => t,
                };
                let how = self.arg_use(&place_ty, &self.ty_of(value));
                let v = self.expr(value, how);
                match self.place(target) {
                    Some(path) if self.captured(path.root) => {
                        self.record_base_uses(target);
                        self.record_capture(path.root, Use::Mut, target.span);
                    }
                    Some(path) => {
                        self.record_base_uses(target);
                        let none = BTreeSet::new();
                        if self.check_mutable(&path, target) && self.p.class(&self.ty_of(value)) == 2 {
                            // The borrow would outlive the loan the caller gave this one (§4.2).
                            let name = self.path_name(&path);
                            self.err(value.span, format!("cannot store a borrow in `{name}`: it would outlive the call, since `{name}` is reached through a `mut` borrow"));
                        }
                        // The place is written once the value is computed: a borrow the value used
                        // last has ended by then.
                        self.access_from(&path, true, target.span, e.span.end, &none);
                        if *op != "=" {
                            // Compound assignment reads the place first.
                            if self.state.moved.contains(&path) {
                                self.err(target.span, format!("`{}` was moved and cannot be used here", self.path_name(&path)));
                            }
                        } else if !self.collecting {
                            // Assignment reinitializes a moved place.
                            self.state.moved.retain(|m| !m.overlaps(&path));
                        }
                        let ty = self.vars[path.root].ty.clone();
                        // Assigned through, a binding holding a `mut` borrow keeps the borrow.
                        let through = matches!(ty, Ty::Borrow(true, _));
                        if path.fields.is_empty() && self.may_hold(&ty) && !through {
                            // A binding assigned anew holds only the new value's loans; one
                            // assigned on several paths holds the union, where the paths join (§4.1).
                            self.state.holds.insert(path.root, v.loans.clone());
                        } else if !path.fields.is_empty() && !v.loans.is_empty() {
                            self.state.holds.entry(path.root).or_default().extend(v.loans.iter().copied());
                        }
                    }
                    None => {
                        self.expr(target, Use::Mut);
                    }
                }
                Val::default()
            }
            ExprKind::Call { callee, args, .. } => {
                let v = self.call(e, callee, args);
                self.note_perform(e);
                v
            }
            ExprKind::Lambda { params, body } => self.lambda(e, params, body),
            ExprKind::Block(b) => self.block_as(b, how, e),
            ExprKind::If { cond, then, otherwise } => {
                self.contained(|o| o.expr(cond, Use::Read));
                self.enter(Node::Branch, 0);
                let before = self.state.clone();
                let a = self.block_as(then, how, e);
                let after_then = std::mem::replace(&mut self.state, before);
                self.set_child(1);
                let b = match otherwise {
                    Some(o) => {
                        let how = self.part_use(&self.ty_of(e), o, how);
                        self.expr(o, how)
                    }
                    None => Val::default(),
                };
                // A branch that never finishes (it throws, returns, breaks) does not meet the other.
                let else_diverges = otherwise.as_deref().is_some_and(diverges);
                if else_diverges && !block_diverges(then) {
                    self.state = after_then;
                } else if !block_diverges(then) {
                    self.state.join(&after_then);
                }
                self.leave();
                Val { loans: a.loans.union(&b.loans).copied().collect() }
            }
            ExprKind::While { cond, body } => {
                self.enter(Node::Loop, 0);
                // Twice: the second iteration sees what the first left behind (§4.1).
                for _ in 0..2 {
                    let before = self.state.clone();
                    let mark = self.made.len();
                    self.expr(cond, Use::Read);
                    self.block(body, Use::Move);
                    self.end_temps(mark, None, body.span.end, &Val::default(), "is dropped at the end of each pass through the loop");
                    self.state.join(&before);
                }
                self.leave();
                Val::default()
            }
            ExprKind::For { pat, iter, body, .. } => {
                // What the iterated value borrows stays borrowed for the whole loop (§4.1).
                let first_loan = self.loans.len();
                self.iterating = matches!(iter.kind, ExprKind::Call { .. });
                let mut iv = self.expr(iter, Use::Read);
                self.iterating = false;
                // What the iterated value holds stays borrowed for the whole loop; a temporary
                // it was made from (`self.sigs[i].iter().cloned().collect()`) does not.
                self.temps.push(iv.loans.clone());
                // A generator's items borrow what it holds, never the generator itself: they are
                // results of its producer (§5.5). A collection's elements borrow the collection.
                if self.is_gen(&self.ty_of(iter)) {
                    let place = self.place(iter);
                    iv.loans.retain(|l| {
                        let loan = &self.loans[*l];
                        let itself = Some(&loan.path) == place.as_ref() || (self.vars[loan.path.root].temp && loan.span == iter.span);
                        *l < first_loan || !itself
                    });
                }
                self.enter(Node::Loop, 0);
                for _ in 0..2 {
                    let before = self.state.clone();
                    self.scopes.push(HashMap::new());
                    self.bind_pattern(pat, &iv, false);
                    let mark = self.made.len();
                    self.block(body, Use::Move);
                    self.end_temps(mark, None, body.span.end, &Val::default(), "is dropped at the end of each pass through the loop");
                    // The loop variables end with the iteration, and release what they held.
                    if let Some(scope) = self.scopes.pop() {
                        for var in scope.values() {
                            self.state.holds.remove(var);
                        }
                    }
                    self.state.join(&before);
                }
                self.leave();
                self.temps.pop();
                Val::default()
            }
            ExprKind::Match { scrutinee, arms } => {
                let whole = self.ty_of(e);
                // A place that cannot be moved from is matched through a borrow of it: its parts
                // bind as borrows (§4.1).
                if let Some(m) = self.typed.lent_scrutinees.get(&scrutinee.span).copied() {
                    // Through a `mut` borrow it is lent `mut` only if an arm changes what it binds;
                    // reading it is all the others need, and the code around may read it too.
                    let m = m && arms.iter().any(|a| self.arm_changes(a));
                    let sv = self.contained(|o| o.expr(scrutinee, if m { Use::Mut } else { Use::Read }));
                    return self.match_arms(arms, sv, how, &whole);
                }
                // A borrow matched is lent on, `mut` only if an arm changes what it binds.
                if let Ty::Borrow(m, _) = self.ty_of(scrutinee) {
                    let m = m && arms.iter().any(|a| self.arm_changes(a));
                    let sv = self.contained(|o| o.expr(scrutinee, if m { Use::Mut } else { Use::Read }));
                    return self.match_arms(arms, sv, how, &whole);
                }
                // A place matched is moved only by the arms that move an owned part they bind; the
                // others borrow it, and it may still be used after them (§4.1).
                let place = self.place(scrutinee).filter(|_| !self.behind_reference(scrutinee));
                let per_arm = place.is_some() && how_for_scrutinee(arms) == Use::Move;
                let first = self.loans.len();
                let read = if per_arm { self.contained(|o| o.expr(scrutinee, Use::Read)) } else { Val::default() };
                let sv = if per_arm {
                    let mut v = read.clone();
                    v.loans.retain(|l| *l < first);
                    v
                } else {
                    self.contained(|o| o.expr(scrutinee, how_for_scrutinee(arms)))
                };
                self.enter(Node::Branch, 0);
                let before = self.state.clone();
                let mut joined: Option<State> = None;
                let mut out = BTreeSet::new();
                for (i, arm) in arms.iter().enumerate() {
                    self.set_child(i as u32);
                    self.state = before.clone();
                    // Already moved, it was reported where the scrutinee was read.
                    let path = place.clone().filter(|p| !self.state.moved.iter().any(|m| m.overlaps(p) || p.overlaps(m)));
                    let takes = per_arm && self.takes_owned(&arm.pat) && self.arm_moves.contains(&arm.pat.span);
                    if takes && !self.collecting && self.destructures_drop(&arm.pat, &self.ty_of(scrutinee)) {
                        self.err(arm.pat.span, "this arm moves what it binds out of a value whose type implements `Drop`, which is dropped whole: bind the value itself, or only read its parts");
                    }
                    // An arm that changes a part it binds, in place, borrows the place `mut`.
                    let lends_mut = per_arm && !takes && self.arm_mutates(arm);
                    if let (true, Some(path)) = (takes, path) {
                        let at = Expr { kind: scrutinee.kind.clone(), span: arm.pat.span };
                        let ty = self.ty_of(scrutinee);
                        self.use_place_as(&at, path, Use::Move, ty);
                    }
                    self.scopes.push(HashMap::new());
                    // An arm that takes nothing borrows what it binds from the place.
                    let mut bound = if per_arm && !takes { read.clone() } else { sv.clone() };
                    if lends_mut && let Some(path) = place.clone() {
                        self.check_mutable(&path, scrutinee);
                        self.access(&path, true, scrutinee.span, &read.loans);
                        let l = self.new_loan(path, true, scrutinee.span);
                        bound.loans.insert(l);
                        if !self.collecting {
                            self.lent_arms.insert(arm.pat.span);
                        }
                    }
                    self.lending = per_arm && !takes;
                    self.bind_pattern(&arm.pat, &bound, lends_mut);
                    self.lending = false;
                    if per_arm && self.collecting {
                        let mut ids = Vec::new();
                        bind_spans(&arm.pat, &mut ids);
                        for span in ids {
                            if let Some(v) = self.sites.iter().find(|((site, _), _)| *site == span.start).map(|(_, v)| *v) {
                                self.arm_binds.insert(v, arm.pat.span);
                            }
                        }
                    }
                    if let Some(g) = &arm.guard {
                        self.guard(g, &arm.pat);
                    }
                    let how = self.part_use(&whole, &arm.body, how);
                    let v = self.expr(&arm.body, how);
                    // An arm that takes the place owns what it binds and drops it when it ends.
                    if takes && let Some(scope) = self.scopes.last() {
                        let dying: HashSet<VarId> = scope.values().copied().collect();
                        self.check_outlives_at(&dying, Some(&arm.body), arm.body.span.end, &v,
                            "this arm owns, having taken the whole place to move a part, and drops when it ends");
                    }
                    out.extend(v.loans);
                    if let Some(scope) = self.scopes.pop() {
                        for var in scope.values() {
                            self.state.holds.remove(var);
                        }
                    }
                    if diverges(&arm.body) {
                        continue;
                    }
                    match &mut joined {
                        None => joined = Some(self.state.clone()),
                        Some(j) => j.join(&self.state),
                    }
                }
                self.state = joined.unwrap_or(before);
                self.leave();
                Val { loans: out }
            }
            ExprKind::Try { body, pat, handler } => {
                self.enter(Node::Branch, 0);
                let before = self.state.clone();
                let a = self.block_as(body, how, e);
                let after_body = std::mem::replace(&mut self.state, before);
                // The catch arm runs after the body unwound: its borrows are released (§5.2), but
                // its moves may have happened.
                self.state.moved.extend(after_body.moved.iter().cloned());
                self.set_child(1);
                self.scopes.push(HashMap::new());
                self.bind_pattern(pat, &Val::default(), false);
                let b = self.block_as(handler, how, e);
                self.scopes.pop();
                self.state.join(&after_body);
                self.leave();
                Val { loans: a.loans.union(&b.loans).copied().collect() }
            }
            ExprKind::Throw(v) => {
                self.expr(v, Use::Move);
                Val::default()
            }
            ExprKind::Yield(v) => {
                let val = self.escape(|o| o.expr(v, Use::Move));
                self.check_yield(&val, v);
                self.note_perform(e);
                Val::default()
            }
            ExprKind::Return(v) => {
                if let Some(v) = v {
                    let how = self.result_use();
                    let val = self.escape(|o| o.expr(v, how));
                    self.check_return(&val, v.span);
                    let ret = self.ret_ty.clone();
                    self.check_mode(v, &ret, "returned");
                }
                Val::default()
            }
            ExprKind::Break | ExprKind::Continue => Val::default(),
            ExprKind::Region { body, .. } => self.block_as(body, how, e),
            // `unsafe` vouches for raw pointers and foreign code, not for ownership.
            ExprKind::Unsafe(body) => self.block_as(body, how, e),
            ExprKind::Handle { body, arms, .. } => {
                // The outer bindings that resuming can reach: those the body or any arm uses.
                let mut reach: Vec<(String, Span)> = Vec::new();
                walk_block(body, &HashSet::new(), &mut reach);
                for arm in arms {
                    let mut bound: HashSet<String> = arm.params.iter().map(|p| p.name.clone()).collect();
                    if let Some(k) = &arm.resumes {
                        bound.insert(k.name.clone());
                    }
                    walk_block(&arm.body, &bound, &mut reach);
                }
                let mut changed = HashSet::new();
                block_changes(body, &mut changed);
                for arm in arms {
                    block_changes(&arm.body, &mut changed);
                }
                let mut reached: Vec<(VarId, bool)> = Vec::new();
                for (name, _) in &reach {
                    if let Some(v) = self.lookup(name)
                        && !reached.iter().any(|(r, _)| *r == v) {
                            reached.push((v, changed.contains(name)));
                        }
                }
                let handled = self.typed.handled.get(&e.span).copied();
                if let Some(d) = handled {
                    self.handling.push((d, BTreeSet::new()));
                }
                let mark = self.made.len();
                let v = self.block_as(body, how, e);
                self.end_temps(mark, body.tail.as_deref(), body.span.end, &v, "is dropped when the `handle`'s body ends");
                let across = if handled.is_some() { self.handling.pop().map(|f| f.1).unwrap_or_default() } else { BTreeSet::new() };
                let mut loans = v.loans.clone();
                for arm in arms {
                    self.scopes.push(HashMap::new());
                    // An operation's arguments are lent by the code that performed it: one that
                    // may hold a borrow lives only until the arm resumes or ends (§5.3).
                    let mut lent = Vec::new();
                    for p in &arm.params {
                        let ty = self.typed.bindings.get(&p.span).cloned().unwrap_or(Ty::Error);
                        let holds = self.may_hold(&ty);
                        let id = self.declare_var(&p.name, ty, false, false, p.span.start);
                        if !holds {
                            continue;
                        }
                        if arm.resumes.is_none() {
                            self.dead_args.insert(id, arm.op.name.clone());
                        } else {
                            let l = self.new_loan(Path { root: id, fields: Vec::new() }, false, p.span);
                            self.state.holds.insert(id, [l].into_iter().collect());
                            self.lent_args.insert(id, arm.op.name.clone());
                            lent.push((id, l));
                        }
                    }
                    if let Some(k) = &arm.resumes {
                        // The continuation holds whatever the body held where it was suspended (§5.3).
                        let id = self.declare_var(&k.name, Ty::Error, false, false, k.span.start);
                        self.state.holds.insert(id, v.loans.union(&across).copied().collect());
                        self.resumes.insert(id, reached.clone());
                        self.cont_args.insert(id, lent);
                    }
                    // What an arm gives back is the `handle` expression's value.
                    let mark = self.made.len();
                    let av = self.block_as(&arm.body, how, e);
                    self.end_temps(mark, arm.body.tail.as_deref(), arm.body.span.end, &av, "is dropped when the arm ends");
                    loans.extend(av.loans.iter().copied());
                    if let Some(scope) = self.scopes.pop() {
                        for var in scope.values() {
                            self.state.holds.remove(var);
                        }
                        let dying: HashSet<VarId> = scope.values().copied().collect();
                        self.check_outlives(&dying, &arm.body, &av);
                    }
                }
                // A continuation that leaves its arm may be resumed wherever it goes, so it holds no
                // borrow: the body borrows nothing it needs past an operation, the operation lends
                // nothing to the arm, and the arms use nothing of the code around (§5.3).
                if arms.iter().any(|a| a.resumes.as_ref().is_some_and(|k| escapes(&a.body, &k.name))) {
                    if !v.loans.is_empty() || !across.is_empty() {
                        let k = arms.iter().find_map(|a| a.resumes.as_ref().filter(|k| escapes(&a.body, &k.name))).unwrap();
                        self.err(k.span, format!("`{}` leaves its arm, so it may hold no borrow, but the `handle`'s body borrows from the code around it past an operation", k.name));
                    }
                    for arm in arms {
                        let Some(k) = &arm.resumes else { continue };
                        if !escapes(&arm.body, &k.name) {
                            continue;
                        }
                        for p in &arm.params {
                            let ty = self.typed.bindings.get(&p.span).cloned().unwrap_or(Ty::Error);
                            if self.may_hold(&ty) {
                                self.err(p.span, format!("`{}` lends its arguments, so its continuation `{}` cannot leave the arm", arm.op.name, k.name));
                            }
                        }
                        // Nor does what passes into and out of the body refer into a region, which
                        // could end before the continuation is resumed.
                        let kt = self.typed.bindings.get(&k.span).cloned().unwrap_or(Ty::Error);
                        let params_region = arm.params.iter().any(|p| {
                            self.typed.bindings.get(&p.span).is_some_and(mentions_any_region)
                        });
                        if mentions_any_region(&kt) || params_region {
                            self.err(k.span, format!("`{}` leaves its arm, so what its operation passes and the `handle` gives may refer into no region", k.name));
                        }
                    }
                    // What the body uses of the code around may refer into no region either.
                    let mut body_uses: Vec<(String, Span)> = Vec::new();
                    walk_block(body, &HashSet::new(), &mut body_uses);
                    for (name, span) in body_uses {
                        if let Some(var) = self.lookup(&name)
                            && mentions_any_region(&self.vars[var].ty) {
                                self.err(span, format!("`{name}` refers into a region, so this `handle`'s body cannot use it: its continuation leaves its arm"));
                            }
                    }
                    let mut arm_uses: Vec<(String, Span)> = Vec::new();
                    for arm in arms {
                        let mut bound: HashSet<String> = arm.params.iter().map(|p| p.name.clone()).collect();
                        if let Some(k) = &arm.resumes {
                            bound.insert(k.name.clone());
                        }
                        walk_block(&arm.body, &bound, &mut arm_uses);
                    }
                    for (name, span) in arm_uses {
                        if self.lookup(&name).is_some() {
                            self.err(span, format!("`{name}` cannot be used here: this `handle`'s continuation leaves its arm, and may be resumed after `{name}` is gone"));
                        }
                    }
                }
                Val { loans }
            }
            ExprKind::Comptime(inner) => self.expr(inner, how),
        }
    }

    /// Records the uses of the binding at the root of a field or index chain, without using it.
    fn record_base_uses(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Ident(name) => {
                if let Some(v) = self.lookup(name) {
                    self.record_use(v, e.span);
                }
            }
            ExprKind::Field { target, .. } | ExprKind::Index { target, .. } | ExprKind::BorrowMut(target) => {
                self.record_base_uses(target)
            }
            _ => {
                self.expr(e, Use::Read);
            }
        }
    }

    fn collect<'e>(&mut self, items: impl Iterator<Item = &'e Expr>) -> Val {
        let mut loans = BTreeSet::new();
        for it in items {
            let how = self.slot_use(it);
            loans.extend(self.escape(|o| o.expr(it, how)).loans);
        }
        Val { loans }
    }

    /// Evaluates something that escapes; see `escaping`.
    fn escape(&mut self, f: impl FnOnce(&mut Self) -> Val) -> Val {
        let saved = std::mem::replace(&mut self.escaping, true);
        let v = f(self);
        self.escaping = saved;
        v
    }

    /// Evaluates something that does not escape.
    fn contained(&mut self, f: impl FnOnce(&mut Self) -> Val) -> Val {
        let saved = std::mem::replace(&mut self.escaping, false);
        let v = f(self);
        self.escaping = saved;
        v
    }

    fn field_inits(&mut self, fields: &[ast::FieldInit]) -> Val {
        let mut loans = BTreeSet::new();
        for f in fields {
            match &f.value {
                Some(v) => {
                    let how = self.slot_use(v);
                    loans.extend(self.escape(|o| o.expr(v, how)).loans)
                }
                None => {
                    let e = Expr { kind: ExprKind::Ident(f.name.name.clone()), span: f.name.span };
                    let how = self.slot_use(&e);
                    loans.extend(self.expr(&e, how).loans);
                }
            }
        }
        Val { loans }
    }

    /// How a part of a literal is used: an owned value put where a borrow is wanted is lent;
    /// anything else, a borrow included, is passed on.
    fn slot_use(&self, e: &Expr) -> Use {
        let ty = self.ty_of(e);
        match self.typed.slots.get(&e.span) {
            Some(t) if !matches!(ty, Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str)) => self.arg_use(t, &ty),
            _ => Use::Move,
        }
    }

    // ---- calls ----

    /// How an argument is used, given the parameter type and the argument's own type.
    fn arg_use(&self, param: &Ty, arg_ty: &Ty) -> Use {
        // A `readonly` borrow passed where one is wanted is copied, with what it holds: nothing
        // borrows the binding it was read from.
        let shared = |t: &Ty| matches!(t, Ty::Borrow(false, _) | Ty::Slice(_) | Ty::Prim(Prim::Str));
        if shared(param) && shared(arg_ty) {
            return Use::Move;
        }
        match param {
            Ty::Borrow(true, _) => Use::Mut,
            Ty::Borrow(false, _) | Ty::Slice(_) | Ty::Prim(Prim::Str) => Use::Read,
            // A borrow read into an owned place that holds no borrow copies what it refers to
            // (the checker has required that to be `Copy`); the borrow itself stays.
            p if matches!(arg_ty, Ty::Borrow(..)) && !matches!(p, Ty::Param(_) | Ty::Var(_)) && self.p.class(p) == 1 => Use::Read,
            _ => Use::Move,
        }
    }

    fn call(&mut self, e: &Expr, callee: &Expr, args: &[Expr]) -> Val {
        let fid = self.typed.calls.get(&e.span).copied();
        let scheme = fid.map(|f| self.p.fns[f].scheme.clone());
        // The parameters as instantiated at this call: `push(x)` on a `Vec<i64>` takes an `i64`;
        // a function value's come from its type.
        let mut params: Vec<(String, Ty)> = match (&scheme, self.typed.targs.get(&e.span)) {
            (Some(s), Some(args)) if args.len() == s.tparams.len() => {
                s.params.iter().map(|(n, t)| (n.clone(), super::env::subst_params(t, &s.tparams, args))).collect()
            }
            (Some(s), _) => s.params.clone(),
            // An effect operation's, as the checker instantiated them.
            (None, _) if self.typed.op_params.contains_key(&e.span) => {
                self.typed.op_params[&e.span].iter().map(|t| (String::new(), t.clone())).collect()
            }
            (None, _) => {
                let mut t = self.ty_of(callee);
                while let Ty::Borrow(_, inner) = t {
                    t = *inner;
                }
                match t {
                    Ty::Fn(f) => f.params.iter().map(|p| (String::new(), p.clone())).collect(),
                    _ => Vec::new(),
                }
            }
        };
        let ret = self.ty_of(e);
        // Only a generator call — one whose result is `void`, its items yielded — lends its
        // sources to its items; a call that returns a collection gives back what it returns.
        let yields = std::mem::replace(&mut self.iterating, false) && matches!(ret, Ty::Prim(Prim::Void));
        let mut arg_vals: Vec<(Option<String>, Val)> = Vec::new();
        let mut receiver_loan: Option<(LoanId, Path, Span)> = None;
        // The borrows of argument places this call takes, which its result holds only if its
        // declared type can hold a borrow itself (§4.2).
        let mut lent_here: BTreeSet<LoanId> = BTreeSet::new();
        self.temps.push(BTreeSet::new());
        let has_self = params.first().is_some_and(|(n, _)| n == "self");
        // The receiver of a method call, borrowed in two phases (§4.1).
        if let (true, ExprKind::Field { target, .. }) = (has_self, &callee.kind) {
            let (_, self_ty) = params.remove(0);
            let want = self.arg_use(&self_ty, &self.ty_of(target));
            if let Some(path) = self.place(target).filter(|p| self.captured(p.root)) {
                self.record_capture(path.root, want, target.span);
            }
            let first = if want == Use::Mut { Use::Read } else { want };
            let before = self.loans.len();
            let v = self.expr(target, first);
            if let Some(path) = self.place(target) {
                lent_here.extend((before..self.loans.len()).filter(|l| self.loans[*l].path == path));
            }
            if want == Use::Mut
                && let Some(path) = self.place(target) {
                    // The receiver's own fresh loan, not an external one it already held.
                    if let Some(l) = v.loans.iter().copied().filter(|l| self.loans[*l].path == path && !self.loans[*l].external).max() {
                        receiver_loan = Some((l, path, target.span));
                    }
                }
            if let Some(t) = self.temps.last_mut() {
                t.extend(v.loans.iter().copied());
            }
            arg_vals.push((Some("self".into()), v));
        } else if let Some(reach) = self.place(callee).and_then(|p| self.resumes.get(&p.root).cloned()) {
            // Resuming runs the rest of the body, and may re-enter the arms: it uses everything
            // they use, so no borrow of those may be live across it (§5.3).
            let none = BTreeSet::new();
            for (v, write) in reach {
                let path = Path { root: v, fields: Vec::new() };
                self.access(&path, write, callee.span, &none);
            }
            // The operation's arguments end with the code that performed them, which resuming
            // lets run on.
            let k = self.place(callee).map(|p| p.root);
            if let Some(k) = k {
                self.check_lent(k, e.span, None);
            }
            // What resuming gives back may hold what the body held, never the continuation: it
            // is used up by the call.
            let mut v = self.expr(callee, Use::Read);
            if let Some(k) = k {
                v.loans.retain(|l| self.loans[*l].path.root != k);
            }
            arg_vals.push((None, v));
        } else if !matches!(callee.kind, ExprKind::Ident(_) | ExprKind::Field { .. }) || scheme.is_none() {
            // Calling a function value: it is used — used up, if it may be called only once —
            // and what it captured flows on, but not the borrow taken to call it.
            let once = match self.ty_of(callee) {
                Ty::Fn(f) => f.mode == FnMode::Once,
                Ty::Named(d, _) => self.p.known.get("Cont") == Some(&d),
                _ => false,
            };
            let v = self.expr(callee, if once { Use::Move } else { Use::Read });
            let callee_root = self.place(callee).map(|p| p.root);
            let held: BTreeSet<LoanId> =
                v.loans.into_iter().filter(|l| Some(self.loans[*l].path.root) != callee_root).collect();
            arg_vals.push((None, Val { loans: held }));
        }
        let role = self.closure_role(fid);
        let mut mut_args: Vec<(LoanId, Path, Expr)> = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let at = self.ty_of(a);
            let how = match params.get(i) {
                Some((_, p)) => self.arg_use(p, &at),
                None => Use::Move,
            };
            if matches!(a.kind, ExprKind::Lambda { .. }) {
                self.next_role = role;
            }
            // Two phases, as for a receiver: a `mut` argument that is a place is lent `readonly`
            // while the later arguments are evaluated, and `mut` only for the call itself, so
            // `replace(mut self.effects, self.fresh())` holds (§4.1).
            let target = match &a.kind {
                ExprKind::BorrowMut(inner) => inner.as_ref(),
                _ => a,
            };
            let staged = if how == Use::Mut { self.place(target).filter(|_| !self.captured(self.place(target).expect("a place").root)) } else { None };
            // The loan that lends the argument itself, on its place or on the temporary it is in.
            let mut lend: Option<LoanId> = None;
            let v = match &staged {
                Some(path) => {
                    let first = self.loans.len();
                    let v = self.expr(target, Use::Read);
                    if let Some(l) = (first..self.loans.len()).rev().find(|l| self.loans[*l].path == *path) {
                        mut_args.push((l, path.clone(), target.clone()));
                        lent_here.insert(l);
                        lend = Some(l);
                    }
                    v
                }
                None => {
                    let before = self.loans.len();
                    let v = self.expr(a, how);
                    if how != Use::Move {
                        let path = self.place(target);
                        if how == Use::Read && let Some(path) = &path {
                            lent_here.extend((before..self.loans.len()).filter(|l| self.loans[*l].path == *path));
                        }
                        lend = (before..self.loans.len()).rev().find(|l| {
                            let loan = &self.loans[*l];
                            Some(&loan.path) == path.as_ref() || (self.vars[loan.path.root].temp && loan.path.fields.is_empty())
                        });
                        lent_here.extend(lend);
                    }
                    v
                }
            };
            // A value that cannot hold a borrow holds none: `self.emit(self.dicts[j])` copies
            // the index out, and nothing of `self.dicts` stays lent across the call (§4.2). Lent,
            // it is still borrowed.
            let mut v = v;
            if !self.may_hold(&at) {
                v.loans.retain(|l| Some(*l) == lend);
            }
            self.next_role = Role::Plain;
            if let Some((_, p)) = params.get(i) {
                let p = p.clone();
                self.check_mode(a, &p, "passed");
            }
            // A value moved into a parameter that is a borrow in disguise: `readonly T` params
            // accept owned arguments by lending; nothing to do. An owned parameter fed from a
            // borrow of a non-Copy type is a move out of the borrow.
            if let (Some((_, p)), Ty::Borrow(_, inner)) = (params.get(i), &at)
                && !matches!(p, Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str)) && !self.p.is_copy(inner) && !self.p.is_copy(&at)
                    && self.p.class(p) == 1 {
                        let shown = self.show(inner);
                        self.err(a.span, format!("cannot move a `{shown}` out of a borrow; it is not `Copy`"));
                    }
            if let Some(t) = self.temps.last_mut() {
                t.extend(v.loans.iter().copied());
            }
            arg_vals.push((params.get(i).map(|(n, _)| n.clone()), v));
        }
        // Phase two: each staged `mut` argument's borrow becomes `mut` for the call itself.
        for (l, path, target) in mut_args {
            let mut except = BTreeSet::new();
            except.insert(l);
            self.loans[l].mutable = true;
            self.loans[l].element = matches!(target.kind, ExprKind::Index { .. });
            self.check_mutable(&path, &target);
            let outer = std::mem::replace(&mut self.lending_element, self.loans[l].element);
            self.access(&path, true, target.span, &except);
            self.lending_element = outer;
        }
        // Phase two: the receiver's borrow becomes `mut` for the call itself.
        if let Some((l, path, span)) = receiver_loan {
            let mut except = BTreeSet::new();
            except.insert(l);
            self.loans[l].mutable = true;
            self.check_mutable(&path, &Expr { kind: ExprKind::Bool(false), span });
            self.access(&path, true, span, &except);
        }
        self.task_captures(fid, args);
        self.temps.pop();
        // The result carries its sources' borrows unless it cannot hold one (§4.2). A result that
        // can hold a borrow only through a type argument holds what its arguments held, never a
        // borrow of an argument's place: generic code cannot make one into a `T`.
        let mut loans = BTreeSet::new();
        if yields || self.may_hold(&ret) {
            let sources = scheme.as_ref().map(|s| result_sources(self.p, s));
            // A generator's items are what it gives, whatever its result's type.
            let declared = yields || scheme.as_ref().is_none_or(|s| self.declared_holds(s));
            for (name, v) in &arg_vals {
                let is_source = match (&sources, name) {
                    (Some(srcs), Some(n)) => srcs.contains(n),
                    _ => true,
                };
                if is_source {
                    loans.extend(v.loans.iter().copied().filter(|l| declared || !lent_here.contains(l)));
                }
            }
        }
        Val { loans }
    }

    /// Whether a function's declared result can hold a borrow other than through its type
    /// parameters.
    /// Generic code can put a borrow of an argument's place into a `T` only through a function it
    /// is given — a closure, a generator, a continuation — or where `T` is a `comptime` type,
    /// which is code checked once it is known.
    fn declared_holds(&self, s: &super::env::Scheme) -> bool {
        let params: Vec<u32> = s.tparams.iter().filter(|g| !g.comptime).map(|g| g.sym.id).collect();
        self.p.class(&s.ret) == 2
            || hides_borrows(&s.ret, self.p, &params)
            || s.params.iter().any(|(_, t)| carries_code(self.p, t, &mut Vec::new()))
    }

    /// A task may capture only `Send` values, moved in, or `readonly` borrows of them (§6.1).
    /// At a point that may perform a handled effect, the body is suspended there while the arm
    /// runs, holding every loan still needed afterwards.
    fn note_perform(&mut self, e: &Expr) {
        if self.collecting || self.handling.is_empty() {
            return;
        }
        let Some(defs) = self.typed.performs.get(&e.span).cloned() else { return };
        let live = self.live_loans(e.span.end, &BTreeSet::new());
        for d in defs {
            // The innermost `handle` of an effect takes it; an open row may be any of them.
            for frame in self.handling.iter_mut().rev() {
                if d.is_none_or(|d| d == frame.0) {
                    frame.1.extend(live.iter().copied());
                    if d.is_some() {
                        break;
                    }
                }
            }
        }
    }

    /// Whether a call's closure argument is a scope's body or a task (§6.1).
    fn closure_role(&self, fid: Option<FnId>) -> Role {
        let Some(fid) = fid else { return Role::Plain };
        let info = &self.p.fns[fid];
        let on = |name: &str| info.impl_id.is_some_and(|i| matches!(&self.p.impls[i].target, Ty::Named(d, _) if self.p.defs[*d].name == name));
        if !self.p.modules[info.module].is_std {
            Role::Plain
        } else if matches!(info.name.as_str(), "spawn" | "fork") && on("Scope") {
            Role::Task
        } else if info.name == "scope" && on("Io") {
            Role::ScopeBody
        } else {
            Role::Plain
        }
    }

    fn task_captures(&mut self, fid: Option<FnId>, args: &[Expr]) {
        let Some(fid) = fid else { return };
        let info = &self.p.fns[fid];
        let is_task = self.p.modules[info.module].is_std
            && matches!(info.name.as_str(), "spawn" | "fork")
            && info.impl_id.is_some_and(|i| matches!(&self.p.impls[i].target, Ty::Named(d, _) if self.p.defs[*d].name == "Scope"));
        if !is_task || self.collecting {
            return;
        }
        // Only inside the body of its `Io.scope` is it known what outlives the scope; a task
        // started elsewhere, by a helper given the scope, cannot borrow at all.
        let in_body = self.roles.contains(&Role::ScopeBody);
        for a in args {
            let ExprKind::Lambda { body, params } = &a.kind else { continue };
            let bound: HashSet<String> = params.iter().map(|p| p.name.name.clone()).collect();
            let mut free = Vec::new();
            free_vars(body, &bound, &mut free);
            for (name, span) in free {
                let Some(v) = self.lookup(&name) else { continue };
                let ty = self.vars[v].ty.clone();
                if !in_body && (self.p.class(&ty) == 2 || matches!(ty, Ty::Fn(_))) {
                    let shown = self.show(&ty);
                    self.err(span, format!("a task started outside the body of its `Io.scope` cannot capture `{name}`, a `{shown}`, which borrows: nothing here says it outlives the scope (pass an owned value)"));
                    continue;
                }
                if !self.sendable(v, false) {
                    let shown = self.show(&self.vars[v].ty.clone());
                    let why = if self.p.is_send_given(&self.vars[v].ty, &self.send_params) { "holds a borrow" } else { "is not `Send`" };
                    self.err(span, format!("a task cannot capture `{name}`: `{shown}` {why}"));
                }
            }
        }
    }

    /// Whether binding `v` may be owned by something that leaves this function's fiber: an
    /// escaping closure (`mut` borrows, which it holds alone, allowed) or a task (§4.3, §6.1).
    fn sendable(&self, v: VarId, mut_ok: bool) -> bool {
        let ty = &self.vars[v].ty;
        let send = |t: &Ty| self.p.is_send_given(t, &self.send_params);
        match ty {
            Ty::Borrow(m, inner) => (mut_ok || !m) && send(inner),
            // A `str` is a `readonly` borrow of immutable bytes.
            Ty::Prim(Prim::Str) => true,
            // A closure lent borrows carries them; one that escaped owns only `Send` values.
            Ty::Fn(_) => mut_ok || self.state.holds.get(&v).is_none_or(|h| h.is_empty()),
            t => send(t),
        }
    }

    fn lambda(&mut self, e: &Expr, params: &[ast::Param], body: &Expr) -> Val {
        let escapes = self.escaping;
        let role = std::mem::replace(&mut self.next_role, Role::Plain);
        // A task borrows only what is outside its scope, which outlives it; what is declared
        // inside, it moves in (§6.1).
        let outside_scope: Option<HashSet<VarId>> = match role {
            Role::Task => self.roles.iter().rposition(|r| *r == Role::ScopeBody).map(|i| self.lambdas[i].0.clone()).or_else(|| Some(HashSet::new())),
            _ => None,
        };
        self.roles.push(role);
        // Check the body first, recording how it uses each binding it captures.
        let outer: HashSet<VarId> = self.scopes.iter().flat_map(|sc| sc.values().copied()).collect();
        self.lambdas.push((outer, HashMap::new()));
        let saved_state = self.state.clone();
        let saved_temps = std::mem::take(&mut self.temps);
        let saved_deferred = std::mem::take(&mut self.deferred);
        self.scopes.push(HashMap::new());
        let mut param_ids = Vec::new();
        for p in params {
            let ty = self.typed.bindings.get(&p.name.span).cloned().unwrap_or(Ty::Error);
            let id = self.declare_var(&p.name.name, ty, true, false, p.name.span.start);
            self.lambda_params.insert(id);
            param_ids.push(id);
        }
        let mark = self.made.len();
        let result = self.contained(|o| o.expr(body, Use::Move));
        self.end_temps(mark, Some(body), body.span.end, &result, "is dropped when the closure returns");
        // A closure's result may borrow a parameter that is itself a borrow, never one it owns,
        // which it drops when it returns (§4.2).
        if !self.collecting
            && let Some(l) = result.loans.iter().find(|l| {
                let loan = &self.loans[**l];
                !loan.external && param_ids.contains(&loan.path.root) && !self.through_reference(loan)
            })
        {
            let name = self.vars[self.loans[*l].path.root].name.clone();
            self.err(body.span, format!("the closure's result borrows `{name}`, a parameter it owns and drops when it returns: return an owned value"));
        }
        self.scopes.pop();
        self.temps = saved_temps;
        self.deferred = saved_deferred;
        self.state = saved_state;
        let (_, uses) = self.lambdas.pop().expect("lambda frame");
        self.roles.pop();
        // The closure's mode follows from what its body does with its captures (§4.3): changing
        // one makes it `mut`, giving one away makes it `once`.
        let mut mode = (FnMode::Shared, String::new());
        for (v, (how, _)) in &uses {
            let name = self.vars[*v].name.clone();
            let ty = self.vars[*v].ty.clone();
            match how {
                Use::Move if !self.p.is_copy(&ty) && !matches!(ty, Ty::Borrow(..)) => mode = (FnMode::Once, name),
                Use::Mut if mode.0 == FnMode::Shared => mode = (FnMode::Mut, name),
                _ => {}
            }
        }
        self.closure_modes.insert(e.span, mode);
        // Then capture each binding as the body needs it: a `readonly` loan for reads, a `mut`
        // loan for changes, a move for moves (§4.3). The closure holds these loans.
        let mut loans = BTreeSet::new();
        let mut captures: Vec<(VarId, (Use, Span))> = uses.into_iter().collect();
        captures.sort_by_key(|(_, (_, span))| span.start);
        for (v, (how, span)) in captures {
            // A closure that escapes owns what it captures: a borrow is copied (with its loans),
            // a `Copy` value is copied, anything else is moved (§4.3).
            let how = match &outside_scope {
                _ if escapes => Use::Move,
                Some(outside) if !outside.contains(&v) => {
                    if how != Use::Move {
                        self.task_moved.insert(v, e.span);
                    }
                    Use::Move
                }
                _ => how,
            };
            if escapes && !self.collecting && !self.sendable(v, true) {
                let (name, shown) = (self.vars[v].name.clone(), self.show(&self.vars[v].ty.clone()));
                self.err(span, format!("a closure that escapes owns what it captures, so it can capture only `Send` values: `{name}` is a `{shown}`"));
            } else if escapes && !self.collecting && has_region(&self.vars[v].ty) {
                // A closure's type does not say which regions it holds data of, so one that
                // escapes could outlive them (§4.6).
                let (name, shown) = (self.vars[v].name.clone(), self.show(&self.vars[v].ty.clone()));
                self.err(span, format!("a closure that escapes cannot capture `{name}`, a `{shown}`: its type does not mention the region, so it could outlive it"));
            }
            // A task shares what it borrows with the other tasks, so it may only read it (§6.1).
            if role == Role::Task && how == Use::Mut && !self.collecting {
                let name = self.vars[v].name.clone();
                self.err(span, format!("a task cannot change `{name}`, which other tasks may be reading: share it through a `Mutex`, or move it into one task"));
            }
            self.record_use(v, span);
            // The capture happens where the closure is made: a binding moved in leaves its
            // scope's ownership then, not when the closure runs.
            let ident = Expr { kind: ExprKind::Ident(self.vars[v].name.clone()), span: e.span };
            let val = self.use_place(&ident, Path { root: v, fields: Vec::new() }, how);
            if self.moves.remove(&e.span).is_some() {
                let (name, ty) = (self.vars[v].name.clone(), self.vars[v].ty.clone());
                // A loop's body is checked twice; the closure captures once.
                let list = self.captured_moves.entry(e.span).or_default();
                if !list.iter().any(|(n, _)| *n == name) {
                    list.push((name, ty));
                }
            }
            loans.extend(val.loans);
        }
        Val { loans }
    }

    /// The mode of a closure, written in place or bound to a name.
    fn closure_mode(&self, e: &Expr) -> Option<(FnMode, String)> {
        match &e.kind {
            ExprKind::Lambda { .. } => self.closure_modes.get(&e.span).cloned(),
            ExprKind::Ident(_) => self.resolved.get(&e.span).and_then(|v| self.var_modes.get(v)).cloned(),
            _ => None,
        }
    }

    /// A closure goes where a function type says how often, and by how many callers at once, it
    /// may be called: a `mut` closure where a shared one is wanted could run concurrently with
    /// itself (`par`), and a `once` closure anywhere but a `once` place could run twice.
    fn check_mode(&mut self, e: &Expr, want: &Ty, how: &str) {
        let Ty::Fn(f) = want else { return };
        let Some((mode, capture)) = self.closure_mode(e) else { return };
        if self.collecting {
            return;
        }
        let msg = match (mode, f.mode) {
            (FnMode::Mut, FnMode::Shared) => format!(
                "this closure changes `{capture}`, so one caller at a time may call it (`mut`), but it is {how} where it may be called by several at once"
            ),
            (FnMode::Once, FnMode::Shared | FnMode::Mut) => format!(
                "this closure gives away `{capture}`, so it can be called only once (`once`), but it is {how} where it may be called again"
            ),
            _ => return,
        };
        self.err(e.span, msg);
    }

    /// What a function returns may hold only borrows of its sources (§4.2).
    /// A yielded value is a result of its function, handed out before it returns: it may borrow
    /// what the function was given, never its locals, which may end before the item does (§5.5).
    fn check_yield(&mut self, v: &Val, e: &Expr) {
        if self.collecting || !self.may_hold(&self.ty_of(e)) {
            return;
        }
        let in_lambda = !self.lambdas.is_empty();
        for l in &v.loans {
            let loan = self.loans[*l].clone();
            let root = loan.path.root;
            let given = if in_lambda { self.lambda_params.contains(&root) } else { self.vars[root].param };
            // A loan taken through a reference borrows what that refers to, whose own loans the
            // value carries too: they are what decides.
            if loan.external || self.through_reference(&loan) {
                continue;
            }
            let name = self.vars[root].name.clone();
            let what = if given { "a parameter the generator owns, which it drops when it ends" } else { "a local of the generator, which may end before the item does" };
            self.err(e.span, format!("this yields a borrow of `{name}`, {what}: yield an owned value (`.toString()`), or borrow from a parameter that is itself a borrow"));
            return;
        }
    }

    fn is_gen(&self, t: &Ty) -> bool {
        let mut t = t;
        while let Ty::Borrow(_, inner) = t {
            t = inner;
        }
        matches!(t, Ty::Named(d, _) if self.p.defs[*d].name == "Gen" && self.p.modules[self.p.defs[*d].module].is_std)
    }

    /// Whether a binding of this type is a reference, so a borrow taken through it borrows what
    /// it refers to, which outlives the binding.
    fn is_reference(&self, t: &Ty) -> bool {
        matches!(t, Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str) | Ty::Fn(_) | Ty::Error)
    }

    /// Whether a loan reaches its place through a reference — the binding, or a field on the way
    /// (a view's slice) — so it borrows what that refers to, not the binding's own storage.
    fn through_reference(&self, loan: &Loan) -> bool {
        let mut t = self.vars[loan.path.root].ty.clone();
        if self.is_reference(&t) {
            return true;
        }
        for f in &loan.path.fields {
            t = field_type(self.p, &t, f).unwrap_or(Ty::Error);
            if self.is_reference(&t) {
                return true;
            }
        }
        false
    }

    fn check_return(&mut self, v: &Val, span: Span) {
        if self.collecting || !self.may_hold(&self.ret_ty.clone()) {
            return;
        }
        for l in &v.loans {
            let loan = self.loans[*l].clone();
            let root = loan.path.root;
            let name = self.vars[root].name.clone();
            if self.vars[root].param && self.sources.contains(&name) && (loan.external || self.through_reference(&loan)) {
                continue;
            }
            // Through a local reference, the reference's own loans decide.
            if !self.vars[root].param && !loan.external && self.through_reference(&loan) {
                continue;
            }
            let msg = if self.vars[root].param && self.sources.contains(&name) {
                format!("the result borrows `{name}`, a parameter this function owns and drops when it returns: take it as a borrow, or return an owned value")
            } else if self.vars[root].param {
                format!("the result borrows `{name}`, but `{name}` is not one of the result's sources (add it with `from`)")
            } else {
                format!("the result borrows {}, which does not outlive this function", self.shown_root(root))
            };
            self.err(span, msg);
        }
    }
}

/// The parameters a function's result may borrow from (§4.2): those named by `from`; otherwise
/// the receiver of a method, or every parameter of a free function, plus parameters whose types
/// can hide a borrow. An explicit `from` is verified against the body, so it may leave those out.
fn result_sources(p: &Program, scheme: &super::env::Scheme) -> Vec<String> {
    if !scheme.ret_from.is_empty() {
        return scheme.ret_from.clone();
    }
    let send = send_params(p, &scheme.tparams);
    let hidden = scheme.params.iter().filter(|(_, t)| hides_borrows(t, p, &send)).map(|(n, _)| n.clone());
    let mut sources: Vec<String> = if scheme.params.first().is_some_and(|(n, _)| n == "self") {
        vec!["self".to_string()]
    } else {
        scheme.params.iter().map(|(n, _)| n.clone()).collect()
    };
    sources.extend(hidden);
    sources
}

impl Own<'_> {
    /// How a function's result is taken from the expression that gives it.
    fn result_use(&self) -> Use {
        match &self.ret_ty {
            Ty::Borrow(true, _) => Use::Mut,
            Ty::Borrow(false, _) => Use::Read,
            _ => Use::Move,
        }
    }

    /// The arms of a `match` whose scrutinee's value is `sv`, none of which moves it.
    fn match_arms(&mut self, arms: &[ast::MatchArm], sv: Val, how: Use, whole: &Ty) -> Val {
        self.enter(Node::Branch, 0);
        let before = self.state.clone();
        let mut joined: Option<State> = None;
        let mut out = BTreeSet::new();
        for (i, arm) in arms.iter().enumerate() {
            self.set_child(i as u32);
            self.state = before.clone();
            self.scopes.push(HashMap::new());
            self.bind_pattern(&arm.pat, &sv, false);
            if let Some(g) = &arm.guard {
                self.guard(g, &arm.pat);
            }
            let how = self.part_use(whole, &arm.body, how);
            let v = self.expr(&arm.body, how);
            out.extend(v.loans);
            if let Some(scope) = self.scopes.pop() {
                for var in scope.values() {
                    self.state.holds.remove(var);
                }
            }
            if diverges(&arm.body) {
                continue;
            }
            match &mut joined {
                None => joined = Some(self.state.clone()),
                Some(j) => j.join(&self.state),
            }
        }
        self.state = joined.unwrap_or(before);
        self.leave();
        Val { loans: out }
    }

    /// A guard decides whether its arm runs: it may only read what its pattern binds, so the arms
    /// after it still find the value whole (§4.1).
    fn guard(&mut self, g: &Expr, pat: &Pattern) {
        let before = self.state.moved.clone();
        self.expr(g, Use::Read);
        let mut names = Vec::new();
        bind_names(pat, &mut names);
        let bound: HashSet<VarId> = names.iter().filter_map(|n| self.lookup(n)).collect();
        if self.state.moved.iter().any(|m| bound.contains(&m.root) && !before.contains(m)) {
            self.err(g.span, "a guard cannot move what its pattern binds: when it fails, the next arm still needs it");
        }
        let mut changed = HashSet::new();
        self.uses_beyond_read(g, true, false, &mut changed);
        if names.iter().any(|n| changed.contains(n)) {
            self.err(g.span, "a guard cannot change what its pattern binds: it only decides whether the arm runs");
        }
    }

    /// Whether a match arm changes a part of the scrutinee it binds, or lets one go where it could
    /// be changed: whether any use of what it binds does more than read it.
    fn arm_changes(&self, arm: &ast::MatchArm) -> bool {
        self.arm_uses(arm, true)
    }

    /// Whether a match arm changes a part of an owned place it binds: owned parts it lets go are
    /// moved or copied, not lent.
    fn arm_mutates(&self, arm: &ast::MatchArm) -> bool {
        self.arm_uses(arm, false)
    }

    fn arm_uses(&self, arm: &ast::MatchArm, escapes: bool) -> bool {
        let mut names = Vec::new();
        bind_names(&arm.pat, &mut names);
        let mut changed = HashSet::new();
        self.uses_beyond_read(&arm.body, false, escapes, &mut changed);
        names.iter().any(|n| changed.contains(n))
    }

    /// The bindings an expression uses other than by reading, by name. `read`: the expression's
    /// value is only read where it is used. A value escapes — so may be changed later — where it is
    /// bound, returned, yielded, assigned, put in a literal or passed for a `mut` borrow.
    fn uses_beyond_read(&self, e: &Expr, read: bool, escapes: bool, out: &mut HashSet<String>) {
        fn root(e: &Expr) -> Option<&str> {
            match &e.kind {
                ExprKind::Ident(n) => Some(n),
                ExprKind::Field { target, .. } | ExprKind::Index { target, .. } | ExprKind::BorrowMut(target) => root(target),
                _ => None,
            }
        }
        let changed = |x: &Expr, out: &mut HashSet<String>| {
            if let Some(r) = root(x) {
                out.insert(r.to_string());
            }
        };
        match &e.kind {
            ExprKind::Ident(n) => {
                if !read && escapes {
                    out.insert(n.clone());
                }
            }
            ExprKind::Field { target, .. } => self.uses_beyond_read(target, true, escapes, out),
            ExprKind::Index { target, index } => {
                self.uses_beyond_read(target, true, escapes, out);
                self.uses_beyond_read(index, true, escapes, out);
            }
            ExprKind::BorrowMut(x) => changed(x, out),
            ExprKind::Assign { target, value, .. } => {
                changed(target, out);
                self.uses_beyond_read(value, false, escapes, out);
            }
            ExprKind::Unary { operand, .. } => self.uses_beyond_read(operand, true, escapes, out),
            ExprKind::Binary { lhs, rhs, .. } => {
                self.uses_beyond_read(lhs, true, escapes, out);
                self.uses_beyond_read(rhs, true, escapes, out);
            }
            ExprKind::Cast { expr, .. } => self.uses_beyond_read(expr, true, escapes, out),
            ExprKind::Range { lo, hi } => {
                for x in lo.iter().chain(hi.iter()) {
                    self.uses_beyond_read(x, true, escapes, out);
                }
            }
            ExprKind::Template(pieces) => {
                for p in pieces {
                    if let ast::TemplatePiece::Expr(x) = p {
                        self.uses_beyond_read(x, true, escapes, out);
                    }
                }
            }
            ExprKind::Call { callee, args, .. } => {
                let params: Option<Vec<Ty>> = match self.typed.calls.get(&e.span) {
                    Some(f) => Some(self.p.fns[*f].scheme.params.iter().map(|(_, t)| t.clone()).collect()),
                    None => match self.typed.exprs.get(&callee.span) {
                        Some(Ty::Fn(f)) => Some(f.params.clone()),
                        _ => None,
                    },
                };
                let has_self = self.typed.calls.get(&e.span).is_some_and(|f| self.p.fns[*f].scheme.params.first().is_some_and(|(n, _)| n == "self"));
                let mut all: Vec<&Expr> = Vec::new();
                match (&callee.kind, has_self) {
                    (ExprKind::Field { target, .. }, true) => all.push(target),
                    _ => self.uses_beyond_read(callee, true, escapes, out),
                }
                all.extend(args.iter());
                for (i, x) in all.iter().enumerate() {
                    match params.as_ref().and_then(|ps| ps.get(i)) {
                        Some(Ty::Borrow(true, _)) => changed(x, out),
                        Some(_) => self.uses_beyond_read(x, true, escapes, out),
                        None => self.uses_beyond_read(x, false, escapes, out),
                    }
                }
            }
            // A match through a `mut` borrow of a binding that changes what it binds changes it.
            ExprKind::Match { scrutinee, arms } => {
                if self.typed.lent_scrutinees.get(&scrutinee.span) == Some(&true) && arms.iter().any(|a| self.arm_changes(a)) {
                    changed(scrutinee, out);
                } else {
                    self.uses_beyond_read(scrutinee, true, escapes, out);
                }
                for a in arms {
                    if let Some(g) = &a.guard {
                        self.uses_beyond_read(g, true, escapes, out);
                    }
                    self.uses_beyond_read(&a.body, read, escapes, out);
                }
            }
            ExprKind::Block(b) | ExprKind::Region { body: b, .. } | ExprKind::Unsafe(b) => self.block_beyond_read(b, read, escapes, out),
            ExprKind::If { cond, then, otherwise } => {
                self.uses_beyond_read(cond, true, escapes, out);
                self.block_beyond_read(then, read, escapes, out);
                if let Some(o) = otherwise {
                    self.uses_beyond_read(o, read, escapes, out);
                }
            }
            ExprKind::While { cond, body } => {
                self.uses_beyond_read(cond, true, escapes, out);
                self.block_beyond_read(body, true, escapes, out);
            }
            ExprKind::For { iter, body, .. } => {
                self.uses_beyond_read(iter, true, escapes, out);
                self.block_beyond_read(body, true, escapes, out);
            }
            ExprKind::Try { body, handler, .. } => {
                self.block_beyond_read(body, read, escapes, out);
                self.block_beyond_read(handler, read, escapes, out);
            }
            ExprKind::Handle { body, arms, .. } => {
                self.block_beyond_read(body, read, escapes, out);
                for a in arms {
                    self.block_beyond_read(&a.body, read, escapes, out);
                }
            }
            ExprKind::Lambda { body, .. } => self.uses_beyond_read(body, false, escapes, out),
            // What is returned, yielded, thrown or put in a value escapes.
            _ => {
                for c in children(e) {
                    self.uses_beyond_read(c, false, escapes, out);
                }
            }
        }
    }

    fn block_beyond_read(&self, b: &ast::Block, read: bool, escapes: bool, out: &mut HashSet<String>) {
        for st in &b.stmts {
            match st {
                Stmt::Let { init, .. } => self.uses_beyond_read(init, false, escapes, out),
                Stmt::Defer(x) | Stmt::Expr(x) => self.uses_beyond_read(x, true, escapes, out),
            }
        }
        if let Some(t) = &b.tail {
            self.uses_beyond_read(t, read, escapes, out);
        }
    }

    /// Whether a pattern binds a part that is owned and not `Copy`, which it takes.
    /// Whether a pattern takes apart a value whose type implements `Drop`, at `ty` or within it.
    fn destructures_drop(&self, p: &Pattern, ty: &Ty) -> bool {
        let dropped = matches!(ty, Ty::Named(d, _) if self.p.has_drop(*d));
        match &p.kind {
            PatternKind::Record { fields, .. } => {
                dropped
                    || fields.iter().any(|(name, sub)| {
                        sub.as_ref().is_some_and(|q| self.destructures_drop(q, &field_type(self.p, ty, &name.name).unwrap_or(Ty::Error)))
                    })
            }
            PatternKind::Tag { .. } => dropped,
            PatternKind::Tuple(ps) => match ty {
                Ty::Tuple(ts) => ps.iter().zip(ts).any(|(q, t)| self.destructures_drop(q, t)),
                _ => false,
            },
            PatternKind::Or(ps) => ps.iter().any(|q| self.destructures_drop(q, ty)),
            _ => false,
        }
    }

    fn takes_owned(&self, p: &Pattern) -> bool {
        let mut names = Vec::new();
        bind_spans(p, &mut names);
        names.iter().any(|span| match self.typed.bindings.get(span) {
            Some(t) => !self.p.is_copy(t) && !matches!(t, Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str)),
            None => true,
        })
    }
}

fn bind_names(p: &Pattern, out: &mut Vec<String>) {
    let fields = |fs: &[(ast::Ident, Option<Pattern>)], out: &mut Vec<String>| {
        for (name, sub) in fs {
            match sub {
                Some(p) => bind_names(p, out),
                None => out.push(name.name.clone()),
            }
        }
    };
    match &p.kind {
        PatternKind::Bind(n) => out.push(n.clone()),
        PatternKind::Tuple(ps) | PatternKind::Or(ps) => ps.iter().for_each(|p| bind_names(p, out)),
        PatternKind::Record { fields: fs, .. } => fields(fs, out),
        PatternKind::Tag { args, .. } => match args {
            TagPatArgs::None => {}
            TagPatArgs::Tuple(ps) => ps.iter().for_each(|p| bind_names(p, out)),
            TagPatArgs::Record(fs) => fields(fs, out),
        },
        _ => {}
    }
}

fn bind_spans(p: &Pattern, out: &mut Vec<Span>) {
    match &p.kind {
        PatternKind::Bind(_) => out.push(p.span),
        PatternKind::Tuple(ps) | PatternKind::Or(ps) => ps.iter().for_each(|p| bind_spans(p, out)),
        PatternKind::Record { fields, .. } => {
            for (name, sub) in fields {
                match sub {
                    Some(p) => bind_spans(p, out),
                    None => out.push(name.span),
                }
            }
        }
        PatternKind::Tag { args, .. } => match args {
            TagPatArgs::None => {}
            TagPatArgs::Tuple(ps) => ps.iter().for_each(|p| bind_spans(p, out)),
            TagPatArgs::Record(fs) => {
                for (name, sub) in fs {
                    match sub {
                        Some(p) => bind_spans(p, out),
                        None => out.push(name.span),
                    }
                }
            }
        },
        _ => {}
    }
}

fn how_for_scrutinee(arms: &[ast::MatchArm]) -> Use {
    // Arms that bind parts of the value take them; arms that only test it read it.
    let binds = arms.iter().any(|a| pattern_binds(&a.pat));
    if binds { Use::Move } else { Use::Read }
}

fn pattern_binds(p: &Pattern) -> bool {
    match &p.kind {
        PatternKind::Bind(_) => true,
        PatternKind::Tuple(ps) | PatternKind::Or(ps) => ps.iter().any(pattern_binds),
        PatternKind::Record { fields, .. } => fields.iter().any(|(_, p)| p.as_ref().is_none_or(pattern_binds)),
        PatternKind::Tag { args, .. } => match args {
            TagPatArgs::None => false,
            TagPatArgs::Tuple(ps) => ps.iter().any(pattern_binds),
            TagPatArgs::Record(fs) => fs.iter().any(|(_, p)| p.as_ref().is_none_or(pattern_binds)),
        },
        _ => false,
    }
}

/// Types that can hold a borrow without showing it in their arguments: closures,
/// continuations and generators, and type parameters (§4.2).
/// Type parameters that are `Send`, directly or through an interface that extends it
/// (`T extends FromJson`): they range over class-1 types, so they hide no borrow (§4.4).
fn send_params(p: &Program, tparams: &[super::env::GParam]) -> Vec<u32> {
    let send = p.known.get("Send").copied();
    tparams
        .iter()
        .filter(|g| g.bounds.iter().any(|b| matches!(b, Ty::Named(d, _) if p.iface_closure(*d).iter().any(|i| Some(*i) == send))))
        .map(|g| g.sym.id)
        .collect()
}

fn hides_borrows(t: &Ty, p: &Program, send: &[u32]) -> bool {
    hides_in(t, p, send, &mut Vec::new())
}

/// Whether a type can hold a borrow its type does not show: a closure, a continuation, a type
/// parameter, or a type built from one — a nominal type's fields included.
/// As the walks in `traits.rs`: a nominal type met again inside itself is a cycle, which hides
/// nothing that the first visit did not find.
fn hides_in(t: &Ty, p: &Program, send: &[u32], inside: &mut Vec<Ty>) -> bool {
    match t {
        Ty::Param(s) => !send.contains(&s.id),
        Ty::Fn(_) | Ty::Var(_) | Ty::Assoc(..) => true,
        Ty::Named(d, args) => {
            let def = &p.defs[*d];
            if matches!(def.name.as_str(), "Gen" | "Cont") && p.modules[def.module].is_std {
                return true;
            }
            if inside.contains(t) {
                return false;
            }
            inside.push(t.clone());
            args.iter().any(|a| matches!(a, GArg::Ty(t) if hides_in(t, p, send, inside)))
                || match &def.kind {
                    super::env::DefKind::Struct { .. } => p.struct_fields(*d, args).is_some_and(|fs| fs.iter().any(|(_, t)| hides_in(t, p, send, inside))),
                    super::env::DefKind::Enum { tags } => tags.values().any(|t| hides_in(&super::env::subst_params(t, &def.params, args), p, send, inside)),
                    _ => false,
                }
        }
        Ty::Tuple(ts) => ts.iter().any(|t| hides_in(t, p, send, inside)),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(|t| hides_in(t, p, send, inside)),
        Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) => hides_in(t, p, send, inside),
        _ => false,
    }
}

/// Whether a value of the type can be code that runs: a closure, a generator, a continuation, or
/// something holding one.
fn carries_code(p: &Program, t: &Ty, inside: &mut Vec<Ty>) -> bool {
    match t {
        Ty::Fn(_) => true,
        Ty::Named(d, args) => {
            let def = &p.defs[*d];
            if matches!(def.name.as_str(), "Gen" | "Cont") && p.modules[def.module].is_std {
                return true;
            }
            if inside.contains(t) {
                return false;
            }
            inside.push(t.clone());
            args.iter().any(|a| matches!(a, GArg::Ty(t) if carries_code(p, t, inside)))
                || p.struct_fields(*d, args).is_some_and(|fs| fs.iter().any(|(_, t)| carries_code(p, t, inside)))
        }
        Ty::Tuple(ts) => ts.iter().any(|t| carries_code(p, t, inside)),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(|t| carries_code(p, t, inside)),
        Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) => carries_code(p, t, inside),
        _ => false,
    }
}

fn field_type(p: &Program, t: &Ty, field: &str) -> Option<Ty> {
    let mut t = t.clone();
    loop {
        match t {
            Ty::Borrow(_, inner) => t = *inner,
            Ty::Named(d, ref args) if p.known.get("Ref") == Some(&d) => match args.get(1) {
                Some(GArg::Ty(inner)) => t = inner.clone(),
                _ => return None,
            },
            _ => break,
        }
    }
    match &t {
        Ty::Named(d, args) => p.struct_fields(*d, args)?.into_iter().find(|(k, _)| k == field).map(|(_, t)| t),
        Ty::Record(r) => r.labels.get(field).cloned(),
        Ty::Tuple(ts) => field.parse::<usize>().ok().and_then(|i| ts.get(i).cloned()),
        _ => None,
    }
}

/// The free variables of an expression (names not bound inside it), with a span of each use.
fn free_vars(e: &Expr, bound: &HashSet<String>, out: &mut Vec<(String, Span)>) {
    let mut bound = bound.clone();
    walk_free(e, &mut bound, out);
}

fn walk_free(e: &Expr, bound: &mut HashSet<String>, out: &mut Vec<(String, Span)>) {
    let mut go = |x: &Expr, b: &mut HashSet<String>| walk_free(x, b, out);
    match &e.kind {
        ExprKind::Ident(n) => {
            if !bound.contains(n) {
                out.push((n.clone(), e.span));
            }
        }
        ExprKind::Lambda { params, body } => {
            let mut inner = bound.clone();
            inner.extend(params.iter().map(|p| p.name.name.clone()));
            walk_free(body, &mut inner, out);
        }
        ExprKind::Block(b) | ExprKind::Region { body: b, .. } | ExprKind::Unsafe(b) => walk_block(b, bound, out),
        _ => {
            for child in children(e) {
                go(child, bound);
            }
            match &e.kind {
                ExprKind::If { then, .. } => walk_block(then, bound, out),
                ExprKind::While { body, .. } => walk_block(body, bound, out),
                ExprKind::For { pat, body, .. } => {
                    let mut inner = bound.clone();
                    pattern_names(pat, &mut inner);
                    walk_block(body, &inner, out);
                }
                ExprKind::Match { arms, .. } => {
                    for arm in arms {
                        let mut inner = bound.clone();
                        pattern_names(&arm.pat, &mut inner);
                        if let Some(g) = &arm.guard {
                            walk_free(g, &mut inner, out);
                        }
                        walk_free(&arm.body, &mut inner, out);
                    }
                }
                ExprKind::Try { body, pat, handler } => {
                    walk_block(body, bound, out);
                    let mut inner = bound.clone();
                    pattern_names(pat, &mut inner);
                    walk_block(handler, &inner, out);
                }
                ExprKind::Handle { body, arms, .. } => {
                    walk_block(body, bound, out);
                    for arm in arms {
                        let mut inner = bound.clone();
                        inner.extend(arm.params.iter().map(|p| p.name.clone()));
                        if let Some(k) = &arm.resumes {
                            inner.insert(k.name.clone());
                        }
                        walk_block(&arm.body, &inner, out);
                    }
                }
                _ => {}
            }
        }
    }
}

fn walk_block(b: &ast::Block, bound: &HashSet<String>, out: &mut Vec<(String, Span)>) {
    let mut inner = bound.clone();
    for s in &b.stmts {
        match s {
            Stmt::Let { pat, init, .. } => {
                walk_free(init, &mut inner, out);
                pattern_names(pat, &mut inner);
            }
            Stmt::Defer(e) | Stmt::Expr(e) => walk_free(e, &mut inner, out),
        }
    }
    if let Some(t) = &b.tail {
        walk_free(t, &mut inner, out);
    }
}

fn pattern_names(p: &Pattern, out: &mut HashSet<String>) {
    match &p.kind {
        PatternKind::Bind(n) => {
            out.insert(n.clone());
        }
        PatternKind::Tuple(ps) | PatternKind::Or(ps) => ps.iter().for_each(|p| pattern_names(p, out)),
        PatternKind::Record { fields, .. } => {
            for (n, sub) in fields {
                match sub {
                    Some(p) => pattern_names(p, out),
                    None => {
                        out.insert(n.name.clone());
                    }
                }
            }
        }
        PatternKind::Tag { args, .. } => match args {
            TagPatArgs::Tuple(ps) => ps.iter().for_each(|p| pattern_names(p, out)),
            TagPatArgs::Record(fs) => {
                for (n, sub) in fs {
                    match sub {
                        Some(p) => pattern_names(p, out),
                        None => {
                            out.insert(n.name.clone());
                        }
                    }
                }
            }
            TagPatArgs::None => {}
        },
        _ => {}
    }
}

/// The direct sub-expressions of an expression (not those inside blocks it owns).
pub(super) fn children(e: &Expr) -> Vec<&Expr> {
    match &e.kind {
        ExprKind::Field { target, .. } => vec![target],
        ExprKind::Index { target, index } => vec![target, index],
        ExprKind::Call { callee, args, .. } => std::iter::once(&**callee).chain(args.iter()).collect(),
        ExprKind::Unary { operand, .. } => vec![operand],
        ExprKind::BorrowMut(x) | ExprKind::Throw(x) | ExprKind::Yield(x) | ExprKind::Comptime(x) => vec![x],
        ExprKind::Binary { lhs, rhs, .. } => vec![lhs, rhs],
        ExprKind::Assign { target, value, .. } => vec![target, value],
        ExprKind::Cast { expr, .. } => vec![expr],
        ExprKind::Range { lo, hi } => lo.iter().chain(hi.iter()).map(|b| &**b).collect(),
        ExprKind::If { cond, otherwise, .. } => std::iter::once(&**cond).chain(otherwise.iter().map(|b| &**b)).collect(),
        ExprKind::While { cond, .. } => vec![cond],
        ExprKind::For { iter, .. } => vec![iter],
        ExprKind::Match { scrutinee, .. } => vec![scrutinee],
        ExprKind::Return(x) => x.iter().map(|b| &**b).collect(),
        ExprKind::Tag { args: TagArgs::Tuple(items), .. } | ExprKind::List(items) => items.iter().collect(),
        ExprKind::Tag { args: TagArgs::Record(fields), .. } | ExprKind::Record { fields, .. } => {
            fields.iter().filter_map(|f| f.value.as_ref()).collect()
        }
        ExprKind::Template(pieces) => pieces
            .iter()
            .filter_map(|p| match p {
                ast::TemplatePiece::Expr(x) => Some(x),
                ast::TemplatePiece::Lit(_) => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

/// The bindings a block assigns to or lends `mut` (by name), for the resume rule.
fn block_changes(b: &ast::Block, out: &mut HashSet<String>) {
    for st in &b.stmts {
        match st {
            Stmt::Let { init, .. } => expr_changes(init, out),
            Stmt::Defer(e) | Stmt::Expr(e) => expr_changes(e, out),
        }
    }
    if let Some(t) = &b.tail {
        expr_changes(t, out);
    }
}

fn expr_changes(e: &Expr, out: &mut HashSet<String>) {
    fn root(e: &Expr) -> Option<&str> {
        match &e.kind {
            ExprKind::Ident(n) => Some(n),
            ExprKind::Field { target, .. } | ExprKind::Index { target, .. } => root(target),
            _ => None,
        }
    }
    match &e.kind {
        ExprKind::Assign { target, .. } | ExprKind::BorrowMut(target) => {
            if let Some(r) = root(target) {
                out.insert(r.to_string());
            }
        }
        // A method call may change its receiver.
        ExprKind::Call { callee, .. } => {
            if let ExprKind::Field { target, .. } = &callee.kind
                && let Some(r) = root(target) {
                    out.insert(r.to_string());
                }
        }
        _ => {}
    }
    for c in children(e) {
        expr_changes(c, out);
    }
    match &e.kind {
        ExprKind::Block(b) | ExprKind::Region { body: b, .. } | ExprKind::Unsafe(b) => block_changes(b, out),
        ExprKind::If { then, .. } => block_changes(then, out),
        ExprKind::While { body, .. } | ExprKind::For { body, .. } => block_changes(body, out),
        ExprKind::Match { arms, .. } => arms.iter().for_each(|a| expr_changes(&a.body, out)),
        ExprKind::Try { body, handler, .. } => {
            block_changes(body, out);
            block_changes(handler, out);
        }
        ExprKind::Lambda { body, .. } => expr_changes(body, out),
        _ => {}
    }
}

/// Whether an expression never finishes normally: it throws, returns, breaks or continues on
/// every path.
fn diverges(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Throw(_) | ExprKind::Return(_) | ExprKind::Break | ExprKind::Continue => true,
        ExprKind::Block(b) | ExprKind::Unsafe(b) => block_diverges(b),
        ExprKind::If { then, otherwise: Some(o), .. } => block_diverges(then) && diverges(o),
        ExprKind::Match { arms, .. } => !arms.is_empty() && arms.iter().all(|a| diverges(&a.body)),
        _ => false,
    }
}

fn block_diverges(b: &ast::Block) -> bool {
    b.stmts.iter().any(|s| matches!(s, Stmt::Expr(e) if diverges(e))) || b.tail.as_deref().is_some_and(diverges)
}

/// Whether a type refers into some region.
fn mentions_any_region(t: &Ty) -> bool {
    let arg = |a: &GArg| match a {
        GArg::Ty(t) => mentions_any_region(t),
        GArg::Region(_) => true,
        _ => false,
    };
    match t {
        Ty::Named(_, args) => args.iter().any(arg),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(mentions_any_region),
        Ty::Tuple(ts) => ts.iter().any(mentions_any_region),
        Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) => mentions_any_region(t),
        Ty::Fn(f) => f.params.iter().any(mentions_any_region) || mentions_any_region(&f.ret),
        _ => false,
    }
}

/// Whether an arm lets its continuation `k` go other than by calling it: returns it, stores it,
/// passes it on.
pub fn escapes(b: &ast::Block, k: &str) -> bool {
    let mut uses = Vec::new();
    walk_block(b, &HashSet::new(), &mut uses);
    let mut calls = 0;
    count_calls(b, k, &mut calls);
    uses.iter().filter(|(n, _)| n == k).count() > calls
}

/// How many times `k(…)` is called in a block.
fn count_calls(b: &ast::Block, k: &str, n: &mut usize) {
    fn expr(e: &Expr, k: &str, n: &mut usize) {
        if let ExprKind::Call { callee, args, .. } = &e.kind {
            if matches!(&callee.kind, ExprKind::Ident(c) if c == k) {
                *n += 1;
            } else {
                expr(callee, k, n);
            }
            for a in args {
                expr(a, k, n);
            }
            return;
        }
        for c in children(e) {
            expr(c, k, n);
        }
    }
    for s in &b.stmts {
        match s {
            Stmt::Let { init, .. } => expr(init, k, n),
            Stmt::Defer(e) | Stmt::Expr(e) => expr(e, k, n),
        }
    }
    if let Some(t) = &b.tail {
        expr(t, k, n);
    }
}

/// Whether a type holds region data: a `Ref`, `Cell` or `RegionList` of some region (§4.6).
fn has_region(t: &Ty) -> bool {
    match t {
        Ty::Named(_, args) => args.iter().any(|a| match a {
            GArg::Region(_) => true,
            GArg::Ty(t) => has_region(t),
            _ => false,
        }),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(has_region),
        Ty::Tuple(ts) => ts.iter().any(has_region),
        Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) => has_region(t),
        _ => false,
    }
}
