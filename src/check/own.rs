//! The ownership pass (milestone 3): moves, borrows, mutability, class and task captures.
//!
//! Runs after type checking, over each function body, using the types the checker recorded.
//! Every value carries the set of *loans* (borrows) it holds; a loan stays live while any
//! binding holding it may still be used, and every access to a place is checked against the
//! live loans that conflict with it (§4.1). Liveness uses the program's structure: a later use
//! is reachable from a point unless they are in different arms of the same branch, and a loop
//! makes every use of a binding declared outside it reachable (its back edge).

use std::collections::{BTreeSet, HashMap, HashSet};

use super::env::{FnId, Program, Typed};
use super::types::*;
use crate::diag::Span;
use crate::syntax::ast::{self, Expr, ExprKind, Pattern, PatternKind, Stmt, TagArgs, TagPatArgs};

type VarId = usize;
type LoanId = usize;
/// A closure being checked: the bindings it captures from outside, and the strongest use its
/// body makes of each.
type LambdaFrame = (HashSet<VarId>, HashMap<VarId, (Use, Span)>);

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
        reported: HashSet::new(),
        lambdas: Vec::new(),
        escaping: false,
        resumes: HashMap::new(),
        sites: HashMap::new(),
        ret_ty,
        sources,
        send_params,
        collecting: true,
        closure_modes: HashMap::new(),
        var_modes: HashMap::new(),
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
        for (i, (name, ty)) in o.typed.params.clone().into_iter().enumerate() {
            let id = o.declare_var(&name, ty.clone(), true, true, usize::MAX - i);
            // A parameter whose type can hide a borrow carries one too, so a `from` that leaves
            // it out is checked against what the body returns (§4.2).
            if o.p.class(&ty) == 2 || hides_borrows(&ty, o.p, &o.send_params) {
                o.loans.push(Loan { path: Path { root: id, fields: Vec::new() }, mutable: false, span: body.span, external: true });
                let l = o.loans.len() - 1;
                o.state.holds.insert(id, [l].into_iter().collect());
            }
        }
        o.escaping = true;
        let v = o.block(&body, Use::Move);
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
    reported: HashSet<(Span, String)>,
    /// Closures being checked, innermost last.
    lambdas: Vec<LambdaFrame>,
    /// Set while evaluating a value that escapes (returned, or stored in a first-class value): a
    /// closure there captures by move (§4.3).
    escaping: bool,
    /// For each continuation binding, the outer bindings its handler's body and arms use, and
    /// whether any of them changes each: calling it re-enters them (§5.3).
    resumes: HashMap<VarId, Vec<(VarId, bool)>>,
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
        let var = Var { name: name.to_string(), ty, mutable, chain: self.chain.clone(), param };
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
        if self.collecting {
            return;
        }
        for l in self.live_loans(at.start, except) {
            let loan = self.loans[l].clone();
            if loan.external || !loan.path.overlaps(path) {
                continue;
            }
            if loan.mutable || write {
                let name = self.path_name(path);
                let how = if loan.mutable { "lent `mut`" } else { "lent `readonly`" };
                let what = if write { "changed" } else { "used" };
                let (line, col) = crate::diag::line_col(&self.p.modules[self.module].source, loan.span.start);
                self.err(at, format!("`{name}` cannot be {what} here: it was {how} at {line}:{col}, and that borrow is still in use"));
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
        self.loans.push(Loan { path, mutable, span, external: false });
        self.loans.len() - 1
    }

    // ---- places ----

    /// The place an expression denotes, if it is one: a binding, or fields of one.
    fn place(&self, e: &Expr) -> Option<Path> {
        match &e.kind {
            ExprKind::Ident(_) => self.resolved.get(&e.span).map(|v| Path { root: *v, fields: Vec::new() }),
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
        let at = e.span;
        if self.captured(path.root) {
            self.record_capture(path.root, how, at);
            return Val { loans: self.state.holds.get(&path.root).cloned().unwrap_or_default() };
        }
        let ty = self.ty_of(e);
        let none = BTreeSet::new();
        // Using something moved.
        if let Some(m) = self.state.moved.iter().find(|m| m.overlaps(&path) || path.overlaps(m)).cloned() {
            let name = self.path_name(&path);
            let what = if m == path { format!("`{name}` was moved") } else { format!("`{}` was moved", self.path_name(&m)) };
            self.err(at, format!("{what} and cannot be used here"));
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
                        self.state.moved.insert(path.clone());
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
                let mut loans = held;
                loans.insert(l);
                Val { loans }
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
        self.scopes.push(HashMap::new());
        let id = self.enter(Node::Seq, 0);
        let _ = id;
        let deferred_depth = self.deferred.len();
        let mut child = 0;
        let escaping = std::mem::replace(&mut self.escaping, false);
        for stmt in &b.stmts {
            child += 1;
            self.set_child(child);
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
        }
        child += 1;
        self.set_child(child);
        self.escaping = escaping;
        let v = match &b.tail {
            Some(e) => self.expr(e, how),
            None => Val::default(),
        };
        self.deferred.truncate(deferred_depth);
        self.leave();
        // Bindings going out of scope release what they hold.
        if let Some(scope) = self.scopes.pop() {
            for var in scope.values() {
                self.state.holds.remove(var);
            }
        }
        v
    }

    fn bind_pattern(&mut self, pat: &Pattern, v: &Val, mutable: bool) {
        match &pat.kind {
            PatternKind::TagAt { .. } => {}
            PatternKind::Bind(name) => {
                let ty = self.typed.bindings.get(&pat.span).cloned().unwrap_or(Ty::Error);
                let id = self.declare_var(name, ty.clone(), mutable, false, pat.span.start);
                if self.may_hold(&ty) {
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
                let v = self.expr(target, base_how);
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
            ExprKind::Range { .. } => Val::default(),
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
                // Into a place that is not a borrow, a borrow is read, not moved.
                let how = self.arg_use(&self.ty_of(target), &self.ty_of(value));
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
                        self.access(&path, true, target.span, &none);
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
                        if path.fields.is_empty() && self.may_hold(&ty) {
                            // A binding assigned on several paths holds the union (§4.1).
                            self.state.holds.entry(path.root).or_default().extend(v.loans.iter().copied());
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
            ExprKind::Call { callee, args, .. } => self.call(e, callee, args),
            ExprKind::Lambda { params, body } => self.lambda(e, params, body),
            ExprKind::Block(b) => self.block(b, how),
            ExprKind::If { cond, then, otherwise } => {
                self.contained(|o| o.expr(cond, Use::Read));
                self.enter(Node::Branch, 0);
                let before = self.state.clone();
                let a = self.block(then, how);
                let after_then = std::mem::replace(&mut self.state, before);
                self.set_child(1);
                let b = match otherwise {
                    Some(o) => self.expr(o, how),
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
                    self.expr(cond, Use::Read);
                    self.block(body, Use::Move);
                    self.state.join(&before);
                }
                self.leave();
                Val::default()
            }
            ExprKind::For { pat, iter, body, .. } => {
                // What the iterated value borrows stays borrowed for the whole loop (§4.1).
                let first_loan = self.loans.len();
                let iv = self.expr(iter, Use::Read);
                let mut held = iv.loans.clone();
                held.extend(first_loan..self.loans.len());
                self.temps.push(held);
                self.enter(Node::Loop, 0);
                for _ in 0..2 {
                    let before = self.state.clone();
                    self.scopes.push(HashMap::new());
                    self.bind_pattern(pat, &iv, false);
                    self.block(body, Use::Move);
                    self.scopes.pop();
                    self.state.join(&before);
                }
                self.leave();
                self.temps.pop();
                Val::default()
            }
            ExprKind::Match { scrutinee, arms } => {
                let sv = self.contained(|o| o.expr(scrutinee, how_for_scrutinee(arms)));
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
                        self.expr(g, Use::Read);
                    }
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
            ExprKind::Try { body, pat, handler } => {
                self.enter(Node::Branch, 0);
                let before = self.state.clone();
                let a = self.block(body, how);
                let after_body = std::mem::replace(&mut self.state, before);
                // The catch arm runs after the body unwound: its borrows are released (§5.2), but
                // its moves may have happened.
                self.state.moved.extend(after_body.moved.iter().cloned());
                self.set_child(1);
                self.scopes.push(HashMap::new());
                self.bind_pattern(pat, &Val::default(), false);
                let b = self.block(handler, how);
                self.scopes.pop();
                self.state.join(&after_body);
                self.leave();
                Val { loans: a.loans.union(&b.loans).copied().collect() }
            }
            ExprKind::Throw(v) | ExprKind::Yield(v) => {
                self.expr(v, Use::Move);
                Val::default()
            }
            ExprKind::Return(v) => {
                if let Some(v) = v {
                    let val = self.escape(|o| o.expr(v, Use::Move));
                    self.check_return(&val, v.span);
                    let ret = self.ret_ty.clone();
                    self.check_mode(v, &ret, "returned");
                }
                Val::default()
            }
            ExprKind::Break | ExprKind::Continue => Val::default(),
            ExprKind::Region { body, .. } | ExprKind::Unsafe(body) => self.block(body, how),
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
                let v = self.block(body, how);
                let mut loans = v.loans.clone();
                for arm in arms {
                    self.scopes.push(HashMap::new());
                    for p in &arm.params {
                        self.declare_var(&p.name, Ty::Error, false, false, p.span.start);
                    }
                    if let Some(k) = &arm.resumes {
                        // The continuation holds whatever the body held (§5.3).
                        let id = self.declare_var(&k.name, Ty::Error, false, false, k.span.start);
                        self.state.holds.insert(id, v.loans.clone());
                        self.resumes.insert(id, reached.clone());
                    }
                    // What an arm gives back is the `handle` expression's value.
                    loans.extend(self.block(&arm.body, how).loans);
                    self.scopes.pop();
                }
                // A continuation that leaves its arm takes its handler with it, so whatever has it
                // borrows everything the handler's arms use (§5.3).
                if arms.iter().any(|a| a.resumes.as_ref().is_some_and(|k| escapes(&a.body, &k.name))) {
                    let mut arm_uses: Vec<(String, Span)> = Vec::new();
                    let mut arm_changes = HashSet::new();
                    for arm in arms {
                        let mut bound: HashSet<String> = arm.params.iter().map(|p| p.name.clone()).collect();
                        if let Some(k) = &arm.resumes {
                            bound.insert(k.name.clone());
                        }
                        walk_block(&arm.body, &bound, &mut arm_uses);
                        block_changes(&arm.body, &mut arm_changes);
                    }
                    for (name, span) in arm_uses {
                        if let Some(var) = self.lookup(&name) {
                            let l = self.new_loan(Path { root: var, fields: Vec::new() }, arm_changes.contains(&name), span);
                            loans.insert(l);
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
            loans.extend(self.escape(|o| o.expr(it, Use::Move)).loans);
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
                Some(v) => loans.extend(self.escape(|o| o.expr(v, Use::Move)).loans),
                None => {
                    let e = Expr { kind: ExprKind::Ident(f.name.name.clone()), span: f.name.span };
                    loans.extend(self.expr(&e, Use::Move).loans);
                }
            }
        }
        Val { loans }
    }

    // ---- calls ----

    /// How an argument is used, given the parameter type and the argument's own type.
    fn arg_use(&self, param: &Ty, arg_ty: &Ty) -> Use {
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
        let mut arg_vals: Vec<(Option<String>, Val)> = Vec::new();
        let mut receiver_loan: Option<(LoanId, Path, Span)> = None;
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
            let v = self.expr(target, first);
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
            let v = self.expr(callee, Use::Read);
            arg_vals.push((None, v));
        } else if !matches!(callee.kind, ExprKind::Ident(_) | ExprKind::Field { .. }) || scheme.is_none() {
            // Calling a function value: it is used, and what it captured flows on — but not the
            // borrow taken to call it.
            let v = self.expr(callee, Use::Read);
            let callee_root = self.place(callee).map(|p| p.root);
            let held: BTreeSet<LoanId> =
                v.loans.into_iter().filter(|l| Some(self.loans[*l].path.root) != callee_root).collect();
            arg_vals.push((None, Val { loans: held }));
        }
        for (i, a) in args.iter().enumerate() {
            let at = self.ty_of(a);
            let how = match params.get(i) {
                Some((_, p)) => self.arg_use(p, &at),
                None => Use::Move,
            };
            let v = self.expr(a, how);
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
        // The result carries its sources' borrows unless it cannot hold one (§4.2).
        let mut loans = BTreeSet::new();
        if self.may_hold(&ret) {
            let sources = scheme.as_ref().map(|s| result_sources(self.p, s));
            for (name, v) in &arg_vals {
                let is_source = match (&sources, name) {
                    (Some(srcs), Some(n)) => srcs.contains(n),
                    _ => true,
                };
                if is_source {
                    loans.extend(v.loans.iter().copied());
                }
            }
        }
        Val { loans }
    }

    /// A task may capture only `Send` values, moved in, or `readonly` borrows of them (§6.1).
    fn task_captures(&mut self, fid: Option<FnId>, args: &[Expr]) {
        let Some(fid) = fid else { return };
        let info = &self.p.fns[fid];
        let is_task = self.p.modules[info.module].is_std
            && matches!(info.name.as_str(), "spawn" | "fork")
            && info.impl_id.is_some_and(|i| matches!(&self.p.impls[i].target, Ty::Named(d, _) if self.p.defs[*d].name == "Scope"));
        if !is_task || self.collecting {
            return;
        }
        for a in args {
            let ExprKind::Lambda { body, params } = &a.kind else { continue };
            let bound: HashSet<String> = params.iter().map(|p| p.name.name.clone()).collect();
            let mut free = Vec::new();
            free_vars(body, &bound, &mut free);
            for (name, span) in free {
                let Some(v) = self.lookup(&name) else { continue };
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
            t => send(t) || self.p.is_copy(t) && self.p.class(t) == 1,
        }
    }

    fn lambda(&mut self, e: &Expr, params: &[ast::Param], body: &Expr) -> Val {
        let escapes = self.escaping;
        // Check the body first, recording how it uses each binding it captures.
        let outer: HashSet<VarId> = self.scopes.iter().flat_map(|sc| sc.values().copied()).collect();
        self.lambdas.push((outer, HashMap::new()));
        let saved_state = self.state.clone();
        let saved_temps = std::mem::take(&mut self.temps);
        let saved_deferred = std::mem::take(&mut self.deferred);
        self.scopes.push(HashMap::new());
        for p in params {
            self.declare_var(&p.name.name, Ty::Error, true, false, p.name.span.start);
        }
        self.contained(|o| o.expr(body, Use::Move));
        self.scopes.pop();
        self.temps = saved_temps;
        self.deferred = saved_deferred;
        self.state = saved_state;
        let (_, uses) = self.lambdas.pop().expect("lambda frame");
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
            let how = if escapes { Use::Move } else { how };
            if escapes && !self.collecting && !self.sendable(v, true) {
                let (name, shown) = (self.vars[v].name.clone(), self.show(&self.vars[v].ty.clone()));
                self.err(span, format!("a closure that escapes owns what it captures, so it can capture only `Send` values: `{name}` is a `{shown}`"));
            }
            self.record_use(v, span);
            let ident = Expr { kind: ExprKind::Ident(self.vars[v].name.clone()), span };
            let val = self.use_place(&ident, Path { root: v, fields: Vec::new() }, how);
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
    fn check_return(&mut self, v: &Val, span: Span) {
        if self.collecting || !self.may_hold(&self.ret_ty.clone()) {
            return;
        }
        for l in &v.loans {
            let loan = self.loans[*l].clone();
            let root = loan.path.root;
            let name = self.vars[root].name.clone();
            if self.vars[root].param && self.sources.contains(&name) {
                continue;
            }
            let msg = if self.vars[root].param {
                format!("the result borrows `{name}`, but `{name}` is not one of the result's sources (add it with `from`)")
            } else {
                format!("the result borrows `{name}`, which does not outlive this function")
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
    hides_depth(t, p, send, 0)
}

/// Whether a type can hold a borrow its type does not show: a closure, a continuation, a type
/// parameter, or a type built from one — a nominal type's fields included.
fn hides_depth(t: &Ty, p: &Program, send: &[u32], depth: usize) -> bool {
    if depth > 8 {
        return false;
    }
    let rec = |t: &Ty| hides_depth(t, p, send, depth + 1);
    match t {
        Ty::Param(s) => !send.contains(&s.id),
        Ty::Fn(_) | Ty::Var(_) | Ty::Assoc(..) => true,
        Ty::Named(d, args) => {
            let def = &p.defs[*d];
            if matches!(def.name.as_str(), "Gen" | "Cont") && p.modules[def.module].is_std {
                return true;
            }
            if args.iter().any(|a| matches!(a, GArg::Ty(t) if rec(t))) {
                return true;
            }
            match &def.kind {
                super::env::DefKind::Struct { .. } => p.struct_fields(*d, args).is_some_and(|fs| fs.iter().any(|(_, t)| rec(t))),
                super::env::DefKind::Enum { tags } => tags.values().any(|t| rec(&super::env::subst_params(t, &def.params, args))),
                _ => false,
            }
        }
        Ty::Tuple(ts) => ts.iter().any(rec),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(rec),
        Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) => rec(t),
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

/// Whether an arm lets its continuation `k` go other than by calling it: returns it, stores it,
/// passes it on.
fn escapes(b: &ast::Block, k: &str) -> bool {
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
