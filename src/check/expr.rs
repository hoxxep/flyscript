//! Checking function bodies: bidirectional types, effects, and patterns.

use std::collections::{BTreeMap, HashMap};

use super::env::*;
use super::subst::{Subst, VarKind};
use super::types::*;
use crate::diag::Span;
use crate::syntax::ast::{self, Expr, ExprKind, Pattern, PatternKind, Stmt, TagArgs, TagPatArgs};

#[derive(Clone, Debug)]
struct Local {
    ty: Ty,
}

/// What a call supplies: explicit type arguments, value arguments, and the expected result.
#[derive(Clone, Copy)]
struct CallSite<'a> {
    explicit: &'a [Ty],
    args: &'a [Expr],
    expected: Option<&'a Ty>,
    span: Span,
}

/// An instantiated signature.
struct Inst {
    params: Vec<(String, Ty)>,
    ret: Ty,
    effects: Option<EffRow>,
    /// The instantiated generic arguments, in the scheme's parameter order.
    args: Vec<GArg>,
}

pub struct Checker<'p> {
    pub p: &'p mut Program,
    pub s: Subst,
    module: usize,
    scopes: Vec<HashMap<String, Local>>,
    ret: Ty,
    allowed: EffRow,
    scope: TyScope,
    /// Exhaustiveness is checked once the body's types are final: a union still open then was
    /// built only from the tags seen, so it is closed rather than demanding a `_` arm.
    pending_matches: Vec<(Ty, Vec<ast::MatchArm>, Span)>,
    /// What later passes need: the type of every expression and binding, and every call's target.
    typed: Typed,
    /// Region allocations whose region the types do not determine: the region variable, and the
    /// regions that were handling `Region` at that point, innermost first. Each goes to the
    /// innermost of them that it does not escape from (§4.6), decided when that region ends.
    pending_regions: Vec<(u32, Vec<Sym>)>,
    /// Values read out of a borrow into an owned position: legal only for `Copy` types, which
    /// is checked once types are final (§4.1).
    copies_out: Vec<(Ty, Span)>,
    pending_copy: Vec<Ty>,
}

/// Checks the body of `fid`, if it has one and has not been checked.
pub fn check_fn(p: &mut Program, fid: FnId) {
    if p.checked.contains(&fid) || !p.fns[fid].has_body {
        return;
    }
    p.checked.insert(fid);
    let info = &p.fns[fid];
    let decl = info.decl;
    let module = info.module;
    let scheme = info.scheme.clone();
    let impl_target = info.impl_id.map(|i| p.impls[i].target.clone());
    let item = &p.modules[decl.module].ast.items[decl.item];
    let fdecl = match (&item.kind, decl.method) {
        (ast::ItemKind::Function(f), None) => f.clone(),
        (ast::ItemKind::Impl(imp), Some(k)) => imp.methods[k].decl.clone(),
        _ => return,
    };
    let Some(body) = fdecl.body.clone() else { return };

    let mut scope = TyScope { module, self_ty: impl_target, ..Default::default() }.with_params(&scheme.tparams);
    let regions: Vec<&GParam> = scheme.tparams.iter().filter(|g| g.kind == PKind::Region).collect();
    scope.elided_region = if regions.len() == 1 { Some(Region::Param(regions[0].sym.clone())) } else { None };

    let mut c = Checker {
        p,
        s: Subst::default(),
        module,
        scopes: vec![HashMap::new()],
        ret: scheme.ret.clone(),
        allowed: EffRow::pure(),
        scope,
        pending_matches: Vec::new(),
        typed: Typed::default(),
        pending_regions: Vec::new(),
        copies_out: Vec::new(),
        pending_copy: Vec::new(),
    };
    let inferring = scheme.effects.is_none();
    c.allowed = match &scheme.effects {
        Some(e) => e.clone(),
        None => c.s.fresh_effs(),
    };
    for (name, ty) in &scheme.params {
        c.declare(name, ty.clone());
    }
    let ret = scheme.ret.clone();
    let t = c.block(&body, Some(&ret));
    c.coerce(&t, &ret, body.tail.as_ref().map_or(body.span, |e| e.span));
    c.s.default_literals();
    for (var, candidates) in std::mem::take(&mut c.pending_regions) {
        if let (Region::Var(_), Some(r)) = (c.s.resolve_region(&Region::Var(var)), candidates.first()) {
            let _ = c.s.unify_region(&Region::Var(var), &Region::Param(r.clone()));
        }
    }
    for (scrut, arms, span) in std::mem::take(&mut c.pending_matches) {
        c.exhaustive(&scrut, &arms, span);
    }
    for (t, span) in std::mem::take(&mut c.copies_out) {
        let z = c.s.zonk(&t);
        if !c.p.is_copy(&z) && !matches!(z, Ty::Var(_) | Ty::Error) {
            let shown = format!("{}", Show(&z, &*c.p));
            c.p.error(module, span, format!("cannot move a `{shown}` out of a borrow; it is not `Copy`"));
        }
    }
    for (name, ty) in &scheme.params {
        c.typed.params.push((name.clone(), ty.clone()));
    }
    let mut typed = std::mem::take(&mut c.typed);
    for t in typed.exprs.values_mut().chain(typed.bindings.values_mut()) {
        *t = c.s.zonk(t);
    }
    c.p.typed.insert(fid, typed);
    if inferring {
        let mut row = c.s.zonk_effs(&c.allowed.clone());
        row.tail = Tail::Closed;
        c.p.inferred.insert(fid, Some(row));
    }
}

/// Effects of a function, inferring them from its body if it declares none.
fn fn_effects(p: &mut Program, fid: FnId, module: usize, span: Span) -> EffRow {
    if let Some(e) = &p.fns[fid].scheme.effects {
        return e.clone();
    }
    match p.inferred.get(&fid) {
        Some(Some(e)) => return e.clone(),
        Some(None) => {
            let name = p.fns[fid].name.clone();
            p.error(module, span, format!("`{name}` calls itself, so it must declare its effects with `uses`"));
            return EffRow::pure();
        }
        None => {}
    }
    p.inferred.insert(fid, None);
    check_fn(p, fid);
    match p.inferred.get(&fid) {
        Some(Some(e)) => e.clone(),
        _ => EffRow::pure(),
    }
}

impl<'p> Checker<'p> {
    // ---- utilities ----

    fn err(&mut self, span: Span, msg: impl Into<String>) {
        self.p.error(self.module, span, msg);
    }

    fn show(&self, t: &Ty) -> String {
        let t = self.s.zonk(t);
        format!("{}", Show(&t, &*self.p))
    }

    fn show_eff(&self, e: &Eff) -> String {
        if e.def == usize::MAX {
            return format!("the effects `...{}`", e.args.first().map_or(String::new(), |t| self.show(t)));
        }
        let e = Eff {
            def: e.def,
            regions: e.regions.iter().map(|r| self.s.resolve_region(r)).collect(),
            args: e.args.iter().map(|t| self.s.zonk(t)).collect(),
        };
        format!("`{}`", Show(&e, &*self.p))
    }

    fn declare(&mut self, name: &str, ty: Ty) {
        self.scopes.last_mut().expect("scope").insert(name.to_string(), Local { ty });
    }

    fn local(&self, name: &str) -> Option<&Local> {
        self.scopes.iter().rev().find_map(|s| s.get(name))
    }

    fn known(&self, name: &str) -> DefId {
        self.p.known[name]
    }

    fn named(&self, name: &str, args: Vec<GArg>) -> Ty {
        Ty::Named(self.known(name), args)
    }

    fn string_ty(&self) -> Ty {
        self.named("String", Vec::new())
    }

    /// The value seen through borrows and region references (borrows are transparent, §4.1).
    fn strip(&self, t: &Ty) -> Ty {
        let mut t = self.s.resolve(t);
        loop {
            match t {
                Ty::Borrow(_, inner) => t = self.s.resolve(&inner),
                Ty::Named(d, ref args) if d == self.known("Ref") => match args.get(1) {
                    Some(GArg::Ty(inner)) => t = self.s.resolve(inner),
                    _ => return t,
                },
                _ => return self.normalize(&t),
            }
        }
    }

    /// Normalizes associated types whose base is known (`Soa<P>.View`).
    fn normalize(&self, t: &Ty) -> Ty {
        match self.s.resolve(t) {
            Ty::Assoc(base, name) => {
                let base = self.s.resolve(&base);
                match (&base, name.as_str()) {
                    (Ty::Named(d, args), "View" | "ReadView") if *d == self.known("Soa") => {
                        let Some(GArg::Ty(elem)) = args.first() else { return Ty::Error };
                        self.soa_view(elem, name == "View")
                    }
                    (Ty::Slice(elem), "View") => Ty::Borrow(true, elem.clone()),
                    (Ty::Slice(elem), "ReadView") => Ty::Borrow(false, elem.clone()),
                    _ => Ty::Assoc(Box::new(base), name),
                }
            }
            Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
                mode: f.mode,
                params: f.params.iter().map(|t| self.normalize(t)).collect(),
                ret: self.normalize(&f.ret),
                effects: f.effects.clone(),
            })),
            Ty::Borrow(m, inner) => Ty::Borrow(m, Box::new(self.normalize(&inner))),
            t => t,
        }
    }

    /// The view of one element of `Soa<T>`: a record of field borrows, flattened recursively (§7.2).
    fn soa_view(&self, elem: &Ty, mutable: bool) -> Ty {
        match self.s.resolve(elem) {
            Ty::Named(d, args) => match &self.p.defs[d].kind {
                DefKind::Struct { fields: Some(fields) } => {
                    let params = self.p.defs[d].params.clone();
                    let labels = fields
                        .iter()
                        .map(|(k, t)| (k.clone(), self.soa_view(&subst_params(t, &params, &args), mutable)))
                        .collect();
                    Ty::Record(Row::closed(labels))
                }
                _ => Ty::Borrow(mutable, Box::new(Ty::Named(d, args))),
            },
            Ty::Record(r) => Ty::Record(Row::closed(r.labels.iter().map(|(k, t)| (k.clone(), self.soa_view(t, mutable))).collect())),
            t => Ty::Borrow(mutable, Box::new(t)),
        }
    }

    /// Unifies, rolling back on failure.
    fn try_unify(&mut self, a: &Ty, b: &Ty) -> bool {
        let snap = self.s.snapshot();
        if self.s.unify(a, b).is_ok() {
            true
        } else {
            self.s.restore(snap);
            false
        }
    }

    /// Whether `found` can be used where `expected` is wanted: by unification, or by lending
    /// (§4.1), the only implicit conversion. Commits the successful attempt.
    fn lends(&mut self, found: &Ty, expected: &Ty) -> bool {
        if self.try_unify(found, expected) {
            return true;
        }
        let f = self.normalize(&self.s.resolve(found));
        let x = self.normalize(&self.s.resolve(expected));
        if f.is_never() {
            return true;
        }
        let snap = self.s.snapshot();
        let ok = match (&f, &x) {
            (Ty::Fn(ff), Ty::Fn(xf)) if ff.params.len() == xf.params.len() => {
                ff.params.iter().zip(&xf.params).all(|(a, b)| self.s.unify(a, b).is_ok() || self.lends(b, a))
                    && self.lends(&ff.ret, &xf.ret)
                    && self.s.eff_sub(&ff.effects, &xf.effects).is_ok()
            }
            (Ty::Borrow(fm, fi), Ty::Borrow(xm, xi)) if *fm || !*xm => {
                let (fi, xi) = (fi.clone(), xi.clone());
                self.lends(&fi, &xi)
            }
            (Ty::Borrow(_, fi), _) => {
                // Reading out of a borrow into an owned position copies, so it must be `Copy`.
                let fi = fi.clone();
                let ok = self.lends(&fi, &x);
                if ok && !matches!(x, Ty::Prim(Prim::Str) | Ty::Slice(_)) {
                    self.pending_copy.push((*fi).clone());
                }
                ok
            }
            (_, Ty::Borrow(_, xi)) => {
                let xi = xi.clone();
                self.lends(&f, &xi)
            }
            (Ty::Named(d, args), _) if *d == self.known("Ref") || *d == self.p.known.get("Box").copied().unwrap_or(usize::MAX) => {
                match args.last() {
                    Some(GArg::Ty(inner)) => {
                        let inner = inner.clone();
                        self.lends(&inner, &x)
                    }
                    _ => false,
                }
            }
            (Ty::Named(d, _), Ty::Prim(Prim::Str)) => *d == self.known("String"),
            (Ty::Array(e, _), Ty::Slice(xe)) => self.s.unify(e, xe).is_ok(),
            (Ty::Named(d, args), Ty::Slice(xe)) if *d == self.known("Vec") => match args.first() {
                Some(GArg::Ty(e)) => self.s.unify(e, xe).is_ok(),
                _ => false,
            },
            _ => false,
        };
        if !ok {
            self.s.restore(snap);
        }
        ok
    }

    fn coerce(&mut self, found: &Ty, expected: &Ty, span: Span) {
        // A function that fits except for its effects: name the effect that does not fit.
        if let (Ty::Fn(f), Ty::Fn(x)) = (self.normalize(&self.s.resolve(found)), self.normalize(&self.s.resolve(expected))) {
            let snap = self.s.snapshot();
            let shapes_fit = f.params.len() == x.params.len()
                && f.params.iter().zip(&x.params).all(|(a, b)| self.s.unify(a, b).is_ok())
                && self.lends(&f.ret, &x.ret);
            if shapes_fit
                && let Err(e) = self.s.eff_sub(&f.effects, &x.effects) {
                    let what = self.show_eff(&e);
                    let allowed = self.s.zonk_effs(&x.effects);
                    let allowed = if allowed.effs.is_empty() && allowed.tail == Tail::Closed {
                        "no effects".to_string()
                    } else {
                        format!("only `{}`", Show(&allowed, &*self.p))
                    };
                    self.s.restore(snap);
                    self.err(span, format!("this function performs {what}, but {allowed} may be performed here"));
                    return;
                }
            self.s.restore(snap);
        }
        let before = self.pending_copy.len();
        if !self.lends(found, expected) {
            let (f, x) = (self.show(found), self.show(expected));
            self.err(span, format!("expected `{x}`, found `{f}`"));
        }
        for t in self.pending_copy.drain(before..).collect::<Vec<_>>() {
            self.copies_out.push((t, span));
        }
    }

    /// Performs effects at `span`: they must fit the effects allowed here.
    fn perform(&mut self, effects: &EffRow, span: Span) {
        let allowed = self.allowed.clone();
        // Region allocations whose region is still unknown are decided later (`pending_regions`).
        let region_def = self.known("Region");
        let handled: Vec<Sym> = self
            .s
            .expand_effs(&allowed)
            .effs
            .iter()
            .filter(|e| e.def == region_def)
            .filter_map(|e| match e.regions.first().map(|r| self.s.resolve_region(r)) {
                Some(Region::Param(s)) => Some(s),
                _ => None,
            })
            .collect();
        let mut effects = self.s.expand_effs(effects);
        // A failure set that is empty, or that nothing has constrained, is no failure: `Io.scope`
        // with no fallible tasks does not make its caller fail.
        let fail_def = self.known("Fail");
        let allows_fail = self.s.expand_effs(&allowed).effs.iter().any(|e| e.def == fail_def);
        let s_ref = &mut self.s;
        effects.effs.retain(|e| {
            if e.def != fail_def {
                return true;
            }
            match e.args.first().map(|t| s_ref.resolve(t)) {
                Some(Ty::Var(_)) if !allows_fail => {
                    let empty = Ty::Union(Row::closed(BTreeMap::new()));
                    let _ = s_ref.unify(&e.args[0], &empty);
                    false
                }
                Some(Ty::Union(r)) => {
                    let r = s_ref.expand_row(&r);
                    !(r.labels.is_empty() && r.tail == Tail::Closed)
                }
                _ => true,
            }
        });
        if !handled.is_empty() {
            let pending = &mut self.pending_regions;
            let s = &self.s;
            effects.effs.retain(|e| {
                if e.def != region_def {
                    return true;
                }
                match e.regions.first().map(|r| s.resolve_region(r)) {
                    Some(Region::Var(v)) => {
                        pending.push((v, handled.clone()));
                        false
                    }
                    _ => true,
                }
            });
        }
        let effects = &effects;
        if let Err(e) = self.s.eff_sub(effects, &allowed) {
            let what = self.show_eff(&e);
            let msg = if self.p.known.get("Fail") == Some(&e.def) {
                let declared = self.s.expand_effs(&allowed).effs.into_iter().find(|x| x.def == e.def);
                match declared {
                    Some(d) => format!(
                        "this can fail with `{}`, which is not in the declared failures `{}`",
                        self.show(&e.args[0]),
                        self.show(&d.args[0])
                    ),
                    None => format!("this can fail with `{}`, but the enclosing function does not declare `Fail`", self.show(&e.args[0])),
                }
            } else if self.p.known.get("Region") == Some(&e.def) {
                match e.regions.first().map(|r| self.s.resolve_region(r)) {
                    Some(Region::Heap) => "this allocates in a region, but its result is expected in the heap; region allocation needs an enclosing `region` block".to_string(),
                    _ => format!("this allocates in {what}, but no enclosing `region` block or declared effect allows it"),
                }
            } else {
                format!("effect {what} is not declared by the enclosing function")
            };
            self.err(span, msg);
        }
    }

    fn eff(&self, name: &str, regions: Vec<Region>, args: Vec<Ty>) -> Eff {
        Eff { def: self.known(name), regions, args }
    }

    // ---- instantiation ----

    fn instantiate(&mut self, scheme: &Scheme, explicit: &[Ty], callee_open_fail: bool) -> Inst {
        let mut map: HashMap<Sym, GArg> = HashMap::new();
        let mut record_tails: HashMap<Sym, Tail> = HashMap::new();
        let mut explicit = explicit.iter();
        let mut args = Vec::new();
        for g in &scheme.tparams {
            let a = match g.kind {
                PKind::Type => GArg::Ty(explicit.next().cloned().unwrap_or_else(|| self.s.fresh())),
                PKind::Region => GArg::Region(self.s.fresh_region()),
                PKind::Row => {
                    record_tails.insert(g.sym.clone(), self.s.fresh_row_tail());
                    GArg::Row(self.s.fresh_effs())
                }
                PKind::Len => GArg::Len(self.s.fresh_len()),
            };
            args.push(a.clone());
            map.insert(g.sym.clone(), a);
        }
        let refs: HashMap<&Sym, &GArg> = map.iter().collect();
        let go = |t: &Ty| inst_record_tails(&subst(t, &refs), &record_tails);
        let params = scheme.params.iter().map(|(n, t)| (n.clone(), go(t))).collect();
        let ret = go(&scheme.ret);
        let effects = scheme.effects.as_ref().map(|e| {
            let mut row = subst_effs(e, &refs);
            for eff in &mut row.effs {
                eff.args = eff.args.iter().map(&go).collect();
            }
            if callee_open_fail {
                self.open_fail(&mut row);
            }
            row
        });
        Inst { params, ret, effects, args }
    }

    /// A callee's declared failures are open at the call site (§3.2).
    fn open_fail(&mut self, row: &mut EffRow) {
        let fail = self.known("Fail");
        for e in &mut row.effs {
            if e.def == fail
                && let Some(Ty::Union(r)) = e.args.first().map(|t| self.s.resolve(t))
                    && r.tail == Tail::Closed {
                        let tail = self.s.fresh_row_tail();
                        e.args[0] = Ty::Union(Row { labels: r.labels.clone(), tail });
                    }
        }
    }

    // ---- blocks and statements ----

    fn block(&mut self, b: &ast::Block, expected: Option<&Ty>) -> Ty {
        self.scopes.push(HashMap::new());
        let mut diverges = false;
        for stmt in &b.stmts {
            match stmt {
                Stmt::Let { pat, ty, init, .. } => {
                    let ann = ty.as_ref().map(|t| {
                        let scope = self.scope.clone();
                        self.p.elab_ty(t, &scope)
                    });
                    let t = match &ann {
                        Some(a) => {
                            let found = self.expr(init, Some(a));
                            self.coerce(&found, a, init.span);
                            a.clone()
                        }
                        None => self.expr(init, None),
                    };
                    self.bind(pat, &t);
                }
                Stmt::Defer(e) => {
                    self.expr(e, None);
                }
                Stmt::Expr(e) => {
                    let t = self.expr(e, None);
                    if self.s.resolve(&t).is_never() {
                        diverges = true;
                    }
                }
            }
        }
        let t = match &b.tail {
            Some(e) => self.expr(e, expected),
            None if diverges => Ty::never(),
            None => Ty::void(),
        };
        self.scopes.pop();
        t
    }

    fn check(&mut self, e: &Expr, expected: &Ty) -> Ty {
        let t = self.expr(e, Some(expected));
        self.coerce(&t, expected, e.span);
        t
    }

    /// Joins the types of alternative branches.
    fn join(&mut self, types: &[(Ty, Span)], expected: Option<&Ty>) -> Ty {
        if let Some(x) = expected {
            for (t, span) in types {
                self.coerce(t, x, *span);
            }
            return x.clone();
        }
        let mut result: Option<Ty> = None;
        for (t, span) in types {
            if self.s.resolve(t).is_never() {
                continue;
            }
            match &result {
                None => result = Some(t.clone()),
                Some(r) => {
                    let r = r.clone();
                    if !self.lends(t, &r) && !self.lends(&r, t) {
                        let (a, b) = (self.show(&r), self.show(t));
                        self.err(*span, format!("branches have different types: `{a}` and `{b}`"));
                    }
                }
            }
        }
        result.unwrap_or_else(Ty::never)
    }

    // ---- expressions ----

    pub fn expr(&mut self, e: &Expr, expected: Option<&Ty>) -> Ty {
        let t = self.expr_inner(e, expected);
        self.typed.exprs.insert(e.span, t.clone());
        t
    }

    fn expr_inner(&mut self, e: &Expr, expected: Option<&Ty>) -> Ty {
        let span = e.span;
        match &e.kind {
            ExprKind::Int(_) => match expected.map(|x| self.strip(x)) {
                Some(Ty::Prim(p)) if p.is_float() => Ty::Prim(p),
                _ => self.s.fresh_kind(VarKind::Int),
            },
            ExprKind::Float(_) => self.s.fresh_kind(VarKind::Float),
            ExprKind::Byte(_) => Ty::Prim(Prim::U8),
            ExprKind::Str(_) => Ty::Prim(Prim::Str),
            ExprKind::Bool(_) => Ty::bool(),
            ExprKind::Template(pieces) => {
                for piece in pieces {
                    if let ast::TemplatePiece::Expr(x) = piece {
                        self.expr(x, None);
                    }
                }
                self.string_ty()
            }
            ExprKind::Ident(name) => self.ident(name, span),
            ExprKind::Tag { name, args } => self.tag(name, args, expected, span),
            ExprKind::Record { name, fields } => self.record(name.as_deref(), fields, expected, span),
            ExprKind::List(items) => self.list(items, expected),
            ExprKind::StructType(_) => {
                self.err(span, "`comptime` type construction is not supported yet");
                Ty::Error
            }
            ExprKind::Field { target, name } => {
                let t = self.expr(target, None);
                self.field(&t, &name.name, name.span)
            }
            ExprKind::Index { target, index } => self.index(target, index, span),
            ExprKind::Call { callee, type_args, args } => self.call(callee, type_args, args, expected, span),
            ExprKind::Unary { op, operand } => {
                let t = self.expr(operand, None);
                let v = self.strip(&t);
                match *op {
                    "!" => {
                        self.coerce(&v, &Ty::bool(), operand.span);
                        Ty::bool()
                    }
                    _ => v,
                }
            }
            ExprKind::BorrowMut(inner) => {
                let t = self.expr(inner, expected.map(|x| self.strip(x)).as_ref());
                match self.s.resolve(&t) {
                    Ty::Borrow(true, _) => t,
                    Ty::Borrow(false, _) => {
                        self.err(span, "cannot lend a `readonly` borrow as `mut`");
                        t
                    }
                    other => Ty::Borrow(true, Box::new(other)),
                }
            }
            ExprKind::Binary { op, lhs, rhs } => self.binary(op, lhs, rhs, span),
            ExprKind::Assign { op, target, value } => {
                let t = self.expr(target, None);
                let v = self.strip(&t);
                let found = self.expr(value, Some(&v));
                let found = if *op == "=" { found } else { self.strip(&found) };
                self.coerce(&found, &v, value.span);
                Ty::void()
            }
            ExprKind::Cast { expr, ty } => {
                self.expr(expr, None);
                let scope = self.scope.clone();
                self.p.elab_ty(ty, &scope)
            }
            ExprKind::Range { .. } => {
                self.err(span, "a range can only be used to index");
                Ty::Error
            }
            ExprKind::Lambda { params, body } => self.lambda(params, body, expected),
            ExprKind::Block(b) => self.block(b, expected),
            ExprKind::If { cond, then, otherwise } => {
                self.check(cond, &Ty::bool());
                let a = self.block(then, expected);
                match otherwise {
                    Some(o) => {
                        let b = self.expr(o, expected);
                        self.join(&[(a, then.span), (b, o.span)], expected)
                    }
                    None => Ty::void(),
                }
            }
            ExprKind::While { cond, body } => {
                self.check(cond, &Ty::bool());
                self.block(body, None);
                Ty::void()
            }
            ExprKind::For { pat, iter, body, .. } => self.for_of(pat, iter, body),
            ExprKind::Match { scrutinee, arms } => self.match_expr(scrutinee, arms, expected, span),
            ExprKind::Try { body, pat, handler } => self.try_catch(body, pat, handler, expected),
            ExprKind::Throw(value) => {
                let t = self.expr(value, None);
                let row = EffRow { effs: vec![self.eff("Fail", Vec::new(), vec![t])], tail: Tail::Closed };
                self.perform(&row, span);
                Ty::never()
            }
            ExprKind::Yield(value) => {
                let yield_def = self.known("Yield");
                let declared = self.s.expand_effs(&self.allowed.clone()).effs.into_iter().find(|x| x.def == yield_def);
                // The effect carries the declared item type, not the value's (which may be a borrow
                // lent to it).
                let t = match declared.as_ref().and_then(|d| d.args.first().cloned()) {
                    Some(item) => {
                        self.check(value, &item);
                        item
                    }
                    None => self.expr(value, None),
                };
                let row = EffRow { effs: vec![self.eff("Yield", Vec::new(), vec![t])], tail: Tail::Closed };
                self.perform(&row, span);
                Ty::void()
            }
            ExprKind::Return(value) => {
                let ret = self.ret.clone();
                match value {
                    Some(v) => {
                        self.check(v, &ret);
                    }
                    None => self.coerce(&Ty::void(), &ret, span),
                }
                Ty::never()
            }
            ExprKind::Break | ExprKind::Continue => Ty::never(),
            ExprKind::Region { name, body } => self.region(name, body, expected, span),
            ExprKind::Handle { body, effect, arms } => self.handle(body, effect, arms, expected),
            ExprKind::Unsafe(b) => self.block(b, expected),
            ExprKind::Comptime(inner) => self.expr(inner, expected),
        }
    }

    fn ident(&mut self, name: &str, span: Span) -> Ty {
        if let Some(l) = self.local(name) {
            return l.ty.clone();
        }
        match self.p.lookup(self.module, name) {
            Some(Binding::Const(c)) => self.p.consts[c].ty.clone(),
            Some(Binding::Fn(fid)) => {
                let scheme = self.p.fns[fid].scheme.clone();
                let effects = fn_effects(self.p, fid, self.module, span);
                let inst = self.instantiate(&Scheme { effects: Some(effects), ..scheme }, &[], true);
                Ty::Fn(Box::new(FnTy {
                    mode: FnMode::Shared,
                    params: inst.params.into_iter().map(|(_, t)| t).collect(),
                    ret: inst.ret,
                    effects: inst.effects.unwrap_or_else(EffRow::pure),
                }))
            }
            _ => {
                self.err(span, format!("unknown name `{name}`"));
                Ty::Error
            }
        }
    }

    fn tag_payloads(&mut self, scrut: &Ty) -> Option<(BTreeMap<String, Ty>, Tail)> {
        match self.strip(scrut) {
            Ty::Named(d, args) => match &self.p.defs[d].kind {
                DefKind::Enum { tags } => {
                    let params = self.p.defs[d].params.clone();
                    Some((tags.iter().map(|(k, t)| (k.clone(), subst_params(t, &params, &args))).collect(), Tail::Closed))
                }
                _ => None,
            },
            Ty::Union(r) => {
                let r = self.s.expand_row(&r);
                Some((r.labels, r.tail))
            }
            _ => None,
        }
    }

    fn tag(&mut self, name: &str, args: &TagArgs, expected: Option<&Ty>, span: Span) -> Ty {
        // The payload type expected for this tag, if the context names it.
        let known = expected.and_then(|x| {
            let (tags, tail) = self.tag_payloads(x)?;
            match tags.get(name) {
                Some(t) => Some(Some(t.clone())),
                None if tail == Tail::Closed => Some(None),
                None => None,
            }
        });
        if let Some(None) = known {
            let x = self.show(expected.expect("known"));
            self.err(span, format!("`#{name}` is not a tag of `{x}`"));
        }
        let payload_expected = known.flatten();
        let payload = match args {
            TagArgs::None => Ty::void(),
            TagArgs::Tuple(items) => {
                let want: Vec<Option<Ty>> = match payload_expected.as_ref().map(|t| self.s.resolve(t)) {
                    Some(Ty::Tuple(ts)) if ts.len() == items.len() => ts.into_iter().map(Some).collect(),
                    _ => vec![None; items.len()],
                };
                Ty::Tuple(
                    items
                        .iter()
                        .zip(want)
                        .map(|(it, w)| match w {
                            Some(w) => {
                                self.check(it, &w);
                                w
                            }
                            None => self.expr(it, None),
                        })
                        .collect(),
                )
            }
            TagArgs::Record(fields) => self.record(None, fields, payload_expected.as_ref(), span),
        };
        if let Some(p) = &payload_expected {
            let p = p.clone();
            if !self.lends(&payload, &p) {
                let (a, b) = (self.show(&p), self.show(&payload));
                self.err(span, format!("`#{name}` carries `{a}`, found `{b}`"));
            }
            if let Some(x) = expected {
                let x = x.clone();
                if matches!(self.strip(&x), Ty::Named(..)) {
                    return self.strip(&x);
                }
            }
        }
        // A construction is open: it fits any union with this tag (§3.2).
        let mut labels = BTreeMap::new();
        labels.insert(name.to_string(), payload);
        Ty::Union(Row { labels, tail: self.s.fresh_row_tail() })
    }

    fn record(&mut self, name: Option<&[ast::Ident]>, fields: &[ast::FieldInit], expected: Option<&Ty>, span: Span) -> Ty {
        let target = match name {
            Some(path) => {
                let scope = self.scope.clone();
                let t = ast::Type { kind: ast::TypeKind::Path { segments: path.to_vec(), args: Vec::new() }, span };
                Some(self.instantiate_named(&t, &scope))
            }
            None => expected.map(|x| self.strip(x)).filter(|t| matches!(t, Ty::Named(..) | Ty::Record(_))),
        };
        let wanted: Option<BTreeMap<String, Ty>> = match &target {
            Some(Ty::Named(d, args)) => match &self.p.defs[*d].kind {
                DefKind::Struct { fields: Some(fs) } => {
                    let params = self.p.defs[*d].params.clone();
                    Some(fs.iter().map(|(k, t)| (k.clone(), subst_params(t, &params, args))).collect())
                }
                _ => None,
            },
            Some(Ty::Record(r)) => Some(self.s.expand_row(r).labels),
            _ => None,
        };
        let mut labels = BTreeMap::new();
        for f in fields {
            let want = wanted.as_ref().and_then(|w| w.get(&f.name.name).cloned());
            if wanted.is_some() && want.is_none() && matches!(target, Some(Ty::Named(..))) {
                self.err(f.name.span, format!("no field `{}` in `{}`", f.name.name, self.show(target.as_ref().expect("named"))));
            }
            let t = match (&f.value, &want) {
                (Some(v), Some(w)) => {
                    self.check(v, w);
                    w.clone()
                }
                (Some(v), None) => self.expr(v, None),
                (None, w) => {
                    let t = self.ident(&f.name.name, f.name.span);
                    if let Some(w) = w {
                        self.coerce(&t, w, f.name.span);
                        w.clone()
                    } else {
                        t
                    }
                }
            };
            labels.insert(f.name.name.clone(), t);
        }
        match target {
            Some(Ty::Named(d, args)) => {
                if let Some(w) = &wanted {
                    let missing: Vec<&String> = w.keys().filter(|k| !labels.contains_key(*k)).collect();
                    if !missing.is_empty() {
                        let list = missing.iter().map(|k| format!("`{k}`")).collect::<Vec<_>>().join(", ");
                        self.err(span, format!("missing fields {list}"));
                    }
                }
                Ty::Named(d, args)
            }
            _ => Ty::Record(Row::closed(labels)),
        }
    }

    /// A nominal type named in an expression (`Decl { … }`), with fresh arguments.
    fn instantiate_named(&mut self, t: &ast::Type, scope: &TyScope) -> Ty {
        let ast::TypeKind::Path { segments, .. } = &t.kind else { return Ty::Error };
        match self.p.lookup(self.module, &segments[0].name) {
            Some(Binding::Def(d)) => {
                let params = self.p.defs[d].params.clone();
                let args = params
                    .iter()
                    .map(|g| match g.kind {
                        PKind::Type => GArg::Ty(self.s.fresh()),
                        PKind::Region => match &scope.elided_region {
                            Some(r) => GArg::Region(r.clone()),
                            None => GArg::Region(self.s.fresh_region()),
                        },
                        PKind::Row => GArg::Row(self.s.fresh_effs()),
                        PKind::Len => GArg::Len(self.s.fresh_len()),
                    })
                    .collect();
                Ty::Named(d, args)
            }
            _ => {
                self.err(t.span, format!("unknown type `{}`", segments[0].name));
                Ty::Error
            }
        }
    }

    fn list(&mut self, items: &[Expr], expected: Option<&Ty>) -> Ty {
        let want = expected.map(|x| self.strip(x));
        match want {
            Some(Ty::Tuple(ts)) if ts.len() == items.len() => {
                for (it, t) in items.iter().zip(&ts) {
                    self.check(it, t);
                }
                Ty::Tuple(ts)
            }
            Some(Ty::Array(elem, len)) => {
                for it in items {
                    self.check(it, &elem);
                }
                let _ = self.s.unify_len(&len, &Len::Known(items.len() as u64));
                Ty::Array(elem, len)
            }
            Some(Ty::Slice(elem)) => {
                for it in items {
                    self.check(it, &elem);
                }
                Ty::Array(elem, Len::Known(items.len() as u64))
            }
            _ => Ty::Tuple(items.iter().map(|it| self.expr(it, None)).collect()),
        }
    }

    fn field(&mut self, t: &Ty, name: &str, span: Span) -> Ty {
        let base = self.strip(t);
        match &base {
            Ty::Named(d, args) => match &self.p.defs[*d].kind {
                DefKind::Struct { fields: Some(fields) } => {
                    if let Some((_, ft)) = fields.iter().find(|(k, _)| k == name) {
                        let ft = ft.clone();
                        let def = &self.p.defs[*d];
                        let hidden = def.module != self.module && def.private.iter().any(|f| f == name);
                        let tname = def.name.clone();
                        let params = def.params.clone();
                        if hidden {
                            self.err(span, format!("`{name}` is a private field of `{tname}`"));
                        }
                        return subst_params(&ft, &params, args);
                    }
                }
                DefKind::Struct { fields: None } => {
                    let n = self.p.defs[*d].name.clone();
                    self.err(span, format!("the fields of `{n}` are private"));
                    return Ty::Error;
                }
                _ => {}
            },
            Ty::Record(r) => {
                let r = self.s.expand_row(r);
                if let Some(ft) = r.labels.get(name) {
                    return ft.clone();
                }
                if let Tail::Var(_) = r.tail {
                    let ft = self.s.fresh();
                    let mut one = BTreeMap::new();
                    one.insert(name.to_string(), ft.clone());
                    let tail = self.s.fresh_row_tail();
                    if self.s.unify_rows(&r, &Row { labels: one, tail }).is_ok() {
                        return ft;
                    }
                }
            }
            Ty::Error => return Ty::Error,
            Ty::Var(_) => {
                self.err(span, format!("cannot infer the type that has field `{name}`; add a type annotation"));
                return Ty::Error;
            }
            _ => {}
        }
        let shown = self.show(&base);
        self.err(span, format!("no field `{name}` on `{shown}`"));
        Ty::Error
    }

    fn index(&mut self, target: &Expr, index: &Expr, span: Span) -> Ty {
        let t = self.expr(target, None);
        let base = self.strip(&t);
        let elem = match &base {
            Ty::Array(e, _) | Ty::Slice(e) => (**e).clone(),
            Ty::Prim(Prim::Str) => Ty::Prim(Prim::U8),
            Ty::Named(d, args) if *d == self.known("Vec") => match args.first() {
                Some(GArg::Ty(e)) => e.clone(),
                _ => Ty::Error,
            },
            Ty::Error => return Ty::Error,
            _ => {
                let shown = self.show(&base);
                self.err(span, format!("cannot index `{shown}`"));
                return Ty::Error;
            }
        };
        let usize_ty = Ty::Prim(Prim::Usize);
        if let ExprKind::Range { lo, hi } = &index.kind {
            for bound in [lo, hi].into_iter().flatten() {
                self.check(bound, &usize_ty);
            }
            return if matches!(base, Ty::Prim(Prim::Str)) { Ty::Prim(Prim::Str) } else { Ty::Slice(Box::new(elem)) };
        }
        let it = self.expr(index, Some(&usize_ty));
        let it = self.strip(&it);
        self.coerce(&it, &usize_ty, index.span);
        elem
    }

    fn binary(&mut self, op: &str, lhs: &Expr, rhs: &Expr, span: Span) -> Ty {
        if matches!(op, "&&" | "||") {
            self.check(lhs, &Ty::bool());
            self.check(rhs, &Ty::bool());
            return Ty::bool();
        }
        let l = self.expr(lhs, None);
        let l = self.strip(&l);
        let r = self.expr(rhs, Some(&l));
        let r = self.strip(&r);
        if !self.try_unify(&l, &r) {
            let (a, b) = (self.show(&l), self.show(&r));
            self.err(span, format!("`{op}` needs operands of the same type, found `{a}` and `{b}`"));
        }
        match op {
            "==" | "!=" | "<" | ">" | "<=" | ">=" => Ty::bool(),
            _ => l,
        }
    }

    // ---- calls ----

    fn call(&mut self, callee: &Expr, type_args: &[ast::Type], args: &[Expr], expected: Option<&Ty>, span: Span) -> Ty {
        let scope = self.scope.clone();
        let explicit: Vec<Ty> = type_args.iter().map(|t| self.p.elab_ty(t, &scope)).collect();
        match &callee.kind {
            ExprKind::Ident(name) if self.local(name).is_none() => {
                if let Some(Binding::Fn(fid)) = self.p.lookup(self.module, name) {
                    return self.call_fn(fid, None, CallSite { explicit: &explicit, args, expected, span });
                }
            }
            ExprKind::Field { target, name } => {
                if let ExprKind::Ident(tname) = &target.kind
                    && self.local(tname).is_none()
                        && let Some(Binding::Def(d)) = self.p.lookup(self.module, tname) {
                            return self.call_static(d, &name.name, &explicit, args, expected, span);
                        }
                let recv = self.expr(target, None);
                return self.call_method(&recv, target.span, &name.name, CallSite { explicit: &explicit, args, expected, span });
            }
            _ => {}
        }
        let t = self.expr(callee, None);
        match self.normalize(&self.s.resolve(&t)) {
            Ty::Fn(f) => {
                self.check_args(&f.params, args, span);
                self.perform(&f.effects, span);
                f.ret
            }
            Ty::Error => Ty::Error,
            other => {
                let shown = self.show(&other);
                self.err(callee.span, format!("`{shown}` is not a function"));
                Ty::Error
            }
        }
    }

    fn check_args(&mut self, params: &[Ty], args: &[Expr], span: Span) {
        if params.len() != args.len() {
            self.err(span, format!("expected {} arguments, found {}", params.len(), args.len()));
        }
        for (p, a) in params.iter().zip(args) {
            let p = self.normalize(p);
            self.check(a, &p);
        }
    }

    fn call_fn(&mut self, fid: FnId, recv: Option<(Ty, Span)>, site: CallSite<'_>) -> Ty {
        let CallSite { explicit, args, expected, span } = site;
        self.typed.calls.insert(span, fid);
        let scheme = self.p.fns[fid].scheme.clone();
        let effects = fn_effects(self.p, fid, self.module, span);
        let scheme = Scheme { effects: Some(effects), ..scheme };
        // Explicit type arguments apply to the function's own parameters, or to its impl's when
        // it has none (`HashMap.new<String, u64>()`).
        let inst = self.instantiate(&scheme, &[], true);
        let own_types: Vec<usize> = scheme.tparams.iter().enumerate().filter(|(_, g)| g.kind == PKind::Type).map(|(i, _)| i).collect();
        if !explicit.is_empty() {
            let impl_params = self.p.fns[fid].impl_id.map_or(0, |i| self.p.impls[i].params.len());
            let own: Vec<usize> = own_types.iter().copied().filter(|i| *i >= impl_params).collect();
            let targets = if own.is_empty() { own_types.clone() } else { own };
            for (i, t) in targets.iter().zip(explicit) {
                if let GArg::Ty(v) = &inst.args[*i] {
                    let v = v.clone();
                    if self.s.unify(&v, t).is_err() {
                        self.err(span, "explicit type argument does not fit");
                    }
                }
            }
        }
        if let Some(x) = expected {
            // Expected types flow into calls before the arguments are checked (§3.6).
            let ret = inst.ret.clone();
            if !self.try_unify(&ret, x) {
                let _ = self.lends(&ret, x);
            }
        }
        let mut params: Vec<Ty> = inst.params.iter().map(|(_, t)| t.clone()).collect();
        if let Some((rt, rspan)) = recv {
            if params.is_empty() {
                self.err(rspan, "this function takes no receiver");
            } else {
                let self_ty = params.remove(0);
                self.coerce(&rt, &self_ty, rspan);
            }
        }
        self.check_args(&params, args, span);
        for (g, a) in scheme.tparams.iter().zip(&inst.args) {
            let wants_send = g.kind == PKind::Row && g.bounds.iter().any(|b| matches!(b, Ty::Named(d, _) if self.p.known.get("Send") == Some(d)));
            if let (true, GArg::Row(row)) = (wants_send, a) {
                let region = self.known("Region");
                if self.s.expand_effs(row).effs.iter().any(|e| e.def == region) {
                    self.err(span, "this writes to a region outside the scope, which is not allowed here: an outer region is frozen while tasks may read it (§6.1)");
                }
            }
        }
        if let Some(e) = &inst.effects {
            self.perform(e, span);
        }
        inst.ret
    }

    fn has_self(&self, fid: FnId) -> bool {
        self.p.fns[fid].scheme.params.first().is_some_and(|(n, _)| n == "self")
    }

    /// `Type.f(…)`: an effect operation, or a function in an `impl` of the type without `self`.
    fn call_static(&mut self, def: DefId, name: &str, explicit: &[Ty], args: &[Expr], expected: Option<&Ty>, span: Span) -> Ty {
        if let DefKind::Effect { ops } = &self.p.defs[def].kind
            && let Some((_, op)) = ops.iter().find(|(n, _)| n == name) {
                let op = op.clone();
                return self.call_op(def, &op, args, expected, span);
            }
        let candidates: Vec<FnId> = self
            .p
            .impls
            .iter()
            .filter(|imp| matches!(&imp.target, Ty::Named(d, _) if *d == def) && imp.interface.is_none())
            .flat_map(|imp| imp.methods.iter().copied())
            .filter(|f| self.p.fns[*f].name == name && !self.has_self(*f))
            .collect();
        match candidates.first() {
            Some(fid) => self.call_fn(*fid, None, CallSite { explicit, args, expected, span }),
            None => {
                let tname = self.p.defs[def].name.clone();
                self.err(span, format!("`{tname}` has no function `{name}`"));
                Ty::Error
            }
        }
    }

    /// An effect operation `Eff.op(…)`: performs `Eff` with the arguments the call determines.
    fn call_op(&mut self, def: DefId, op: &Scheme, args: &[Expr], expected: Option<&Ty>, span: Span) -> Ty {
        let eff_params = self.p.defs[def].params.clone();
        let mut all = eff_params.clone();
        all.extend(op.tparams.iter().cloned());
        let inst = self.instantiate(&Scheme { tparams: all, ..op.clone() }, &[], false);
        if let Some(x) = expected {
            let ret = inst.ret.clone();
            self.try_unify(&ret, x);
        }
        let mut regions = Vec::new();
        let mut targs = Vec::new();
        for (g, a) in eff_params.iter().zip(&inst.args) {
            match (g.kind, a) {
                (PKind::Region, GArg::Region(r)) => regions.push(r.clone()),
                (PKind::Type, GArg::Ty(t)) => targs.push(t.clone()),
                _ => {}
            }
        }
        // Perform first so the allowed row determines the effect's arguments (`Dom<Msg>`).
        let row = EffRow { effs: vec![Eff { def, regions, args: targs }], tail: Tail::Closed };
        self.perform(&row, span);
        let params: Vec<Ty> = inst.params.iter().map(|(_, t)| t.clone()).collect();
        self.check_args(&params, args, span);
        inst.ret
    }

    /// The method `name` whose receiver `recv` can be lent to, if any. Changes nothing.
    fn find_method(&mut self, recv: &Ty, name: &str) -> Option<FnId> {
        let candidates: Vec<FnId> = (0..self.p.fns.len())
            .filter(|f| self.p.fns[*f].name == name && self.p.fns[*f].impl_id.is_some() && self.has_self(*f))
            .collect();
        for fid in candidates {
            let scheme = self.p.fns[fid].scheme.clone();
            let snap = self.s.snapshot();
            let inst = self.instantiate(&Scheme { effects: None, ..scheme }, &[], false);
            let self_ty = inst.params[0].1.clone();
            let fits = self.lends(recv, &self_ty);
            self.s.restore(snap);
            if fits {
                return Some(fid);
            }
        }
        None
    }

    fn call_method(&mut self, recv: &Ty, rspan: Span, name: &str, site: CallSite<'_>) -> Ty {
        let span = site.span;
        if let Some(fid) = self.find_method(recv, name) {
            return self.call_fn(fid, Some((recv.clone(), rspan)), site);
        }
        let shown = self.show(recv);
        if !matches!(self.s.resolve(recv), Ty::Error) {
            self.err(span, format!("no method `{name}` on `{shown}`"));
        }
        Ty::Error
    }

    fn lambda(&mut self, params: &[ast::Param], body: &Expr, expected: Option<&Ty>) -> Ty {
        let want = expected.map(|x| self.normalize(&self.s.resolve(x)));
        let (want_params, want_ret, mode) = match &want {
            Some(Ty::Fn(f)) if f.params.len() == params.len() => (Some(f.params.clone()), Some(f.ret.clone()), f.mode),
            _ => (None, None, FnMode::Shared),
        };
        self.scopes.push(HashMap::new());
        let mut ptys = Vec::new();
        for (i, p) in params.iter().enumerate() {
            let t = match (&p.ty, &want_params) {
                (Some(t), _) => {
                    let scope = self.scope.clone();
                    self.p.elab_ty(t, &scope)
                }
                (None, Some(w)) => self.normalize(&w[i]),
                (None, None) => self.s.fresh(),
            };
            if p.name.name != "_" {
                self.declare(&p.name.name, t.clone());
            }
            ptys.push(t);
        }
        let saved_ret = std::mem::replace(&mut self.ret, want_ret.clone().unwrap_or_else(|| self.s.fresh()));
        let inner_allowed = self.s.fresh_effs();
        let saved_allowed = std::mem::replace(&mut self.allowed, inner_allowed.clone());
        let ret = self.ret.clone();
        let t = self.expr(body, Some(&ret));
        if want_ret.is_some() {
            self.coerce(&t, &ret, body.span);
        } else {
            let _ = self.s.unify(&ret, &t);
        }
        self.allowed = saved_allowed;
        self.ret = saved_ret;
        self.scopes.pop();
        Ty::Fn(Box::new(FnTy { mode, params: ptys, ret, effects: inner_allowed }))
    }

    // ---- handlers ----

    /// Runs `f` with `eff` handled: it is allowed in front of the enclosing effects.
    fn with_handler<T>(&mut self, eff: Eff, f: impl FnOnce(&mut Self) -> T) -> T {
        let outer = self.allowed.clone();
        let mut row = self.s.expand_effs(&outer);
        row.effs.insert(0, eff);
        self.allowed = row;
        let r = f(self);
        self.allowed = outer;
        r
    }

    fn for_of(&mut self, pat: &Pattern, iter: &Expr, body: &ast::Block) -> Ty {
        // Check the iterated expression in isolation to see whether it is a generator.
        let isolated = self.s.fresh_effs();
        let outer = std::mem::replace(&mut self.allowed, isolated.clone());
        // A list literal iterated directly is an array, as in TypeScript (`for (const x of [a, b])`).
        let t = if let ExprKind::List(_) = iter.kind {
            let elem = self.s.fresh();
            self.expr(iter, Some(&Ty::Slice(Box::new(elem))))
        } else {
            self.expr(iter, None)
        };
        self.allowed = outer;
        let yield_def = self.known("Yield");
        let mut row = self.s.expand_effs(&isolated);
        let item = match row.effs.iter().position(|e| e.def == yield_def) {
            Some(i) => row.effs.remove(i).args[0].clone(),
            None => {
                // Not a generator: the iteration protocol (`Iterable.each`).
                if self.find_method(&t, "each").is_none() {
                    if !matches!(self.s.resolve(&t), Ty::Error) {
                        let shown = self.show(&t);
                        self.err(iter.span, format!("`{shown}` is neither a generator nor `Iterable`"));
                    }
                    Ty::Error
                } else {
                    let isolated2 = self.s.fresh_effs();
                    let outer = std::mem::replace(&mut self.allowed, isolated2.clone());
                    // The implicit call gets its own (zero-width) span, so it does not overwrite the
                    // record of a call written there (`xs.iter()`).
                    let implicit = Span::new(iter.span.end, iter.span.end);
                    self.call_method(&t, iter.span, "each", CallSite { explicit: &[], args: &[], expected: None, span: implicit });
                    self.allowed = outer;
                    row = self.s.expand_effs(&isolated2);
                    match row.effs.iter().position(|e| e.def == yield_def) {
                        Some(i) => row.effs.remove(i).args[0].clone(),
                        None => Ty::Error,
                    }
                }
            }
        };
        self.perform(&row, iter.span);
        self.scopes.push(HashMap::new());
        self.bind(pat, &item);
        self.block(body, None);
        self.scopes.pop();
        Ty::void()
    }

    fn try_catch(&mut self, body: &ast::Block, pat: &Pattern, handler: &ast::Block, expected: Option<&Ty>) -> Ty {
        let payload = Ty::Union(Row { labels: BTreeMap::new(), tail: self.s.fresh_row_tail() });
        let fail = self.eff("Fail", Vec::new(), vec![payload.clone()]);
        let a = self.with_handler(fail, |c| c.block(body, expected));
        // Handling `Fail` closes its row (§5.4).
        self.s.close_union(&payload);
        self.scopes.push(HashMap::new());
        self.bind(pat, &payload);
        let b = self.block(handler, expected);
        self.scopes.pop();
        self.join(&[(a, body.span), (b, handler.span)], expected)
    }

    fn region(&mut self, name: &ast::Ident, body: &ast::Block, expected: Option<&Ty>, span: Span) -> Ty {
        let sym = self.p.fresh_sym(&name.name);
        let saved = self.scope.clone();
        self.scope.params.insert(name.name.clone(), (sym.clone(), PKind::Region));
        self.scope.elided_region = Some(Region::Param(sym.clone()));
        let eff = self.eff("Region", vec![Region::Param(sym.clone())], Vec::new());
        let t = self.with_handler(eff, |c| c.block(body, expected));
        self.scope = saved;
        self.settle_regions(&sym, &t);
        let z = self.s.zonk(&t);
        if mentions_region(&z, &sym) {
            let shown = self.show(&z);
            self.err(span, format!("a value of type `{shown}` would outlive region `{}`", name.name));
        }
        // Nor may region data be stored in a variable that outlives the block (§4.6).
        let outer: Vec<(String, Ty)> =
            self.scopes.iter().flat_map(|sc| sc.iter().map(|(k, l)| (k.clone(), l.ty.clone()))).collect();
        for (var, ty) in outer {
            let z = self.s.zonk(&ty);
            if mentions_region(&z, &sym) {
                self.err(span, format!("`{var}` would hold data from region `{}` after the region ends", name.name));
            }
        }
        t
    }

    /// Whether region `sym`'s data would outlive it: through the block's result or a variable
    /// declared outside the block.
    fn escapes(&self, sym: &Sym, result: &Ty) -> bool {
        mentions_region(&self.s.zonk(result), sym)
            || self.scopes.iter().flat_map(|sc| sc.values()).any(|l| mentions_region(&self.s.zonk(&l.ty), sym))
    }

    /// Decides the allocations pending on region `sym` as it ends: each goes here unless that
    /// would let it escape, in which case it waits for the next enclosing region.
    fn settle_regions(&mut self, sym: &Sym, result: &Ty) {
        let pending = std::mem::take(&mut self.pending_regions);
        for (var, mut candidates) in pending {
            let undecided = matches!(self.s.resolve_region(&Region::Var(var)), Region::Var(_));
            if !undecided {
                continue;
            }
            if candidates.first() != Some(sym) {
                self.pending_regions.push((var, candidates));
                continue;
            }
            let snap = self.s.snapshot();
            let _ = self.s.unify_region(&Region::Var(var), &Region::Param(sym.clone()));
            if self.escapes(sym, result) && candidates.len() > 1 {
                self.s.restore(snap);
                candidates.remove(0);
                self.pending_regions.push((var, candidates));
            }
        }
    }

    fn handle(&mut self, body: &ast::Block, effect: &ast::Type, arms: &[ast::HandlerArm], expected: Option<&Ty>) -> Ty {
        let scope = self.scope.clone();
        let row = self.p.elab_effects(&[ast::RowItem::Effect(effect.clone())], &scope);
        let Some(eff) = row.effs.first().cloned() else { return Ty::Error };
        let result = expected.cloned().unwrap_or_else(|| self.s.fresh());
        let t = self.with_handler(eff.clone(), |c| c.block(body, Some(&result)));
        self.coerce(&t, &result, body.span);
        let DefKind::Effect { ops } = &self.p.defs[eff.def].kind else { return result };
        let ops = ops.clone();
        let eff_params = self.p.defs[eff.def].params.clone();
        let mut eff_args = Vec::new();
        let (mut ri, mut ti) = (0, 0);
        for g in &eff_params {
            match g.kind {
                PKind::Region => {
                    eff_args.push(GArg::Region(eff.regions.get(ri).cloned().unwrap_or(Region::Heap)));
                    ri += 1;
                }
                _ => {
                    eff_args.push(GArg::Ty(eff.args.get(ti).cloned().unwrap_or(Ty::Error)));
                    ti += 1;
                }
            }
        }
        for arm in arms {
            let Some((_, op)) = ops.iter().find(|(n, _)| *n == arm.op.name) else {
                let ename = self.p.defs[eff.def].name.clone();
                self.err(arm.op.span, format!("`{ename}` has no operation `{}`", arm.op.name));
                continue;
            };
            let params: Vec<(String, Ty)> = op.params.iter().map(|(n, t)| (n.clone(), subst_params(t, &eff_params, &eff_args))).collect();
            let op_ret = subst_params(&op.ret, &eff_params, &eff_args);
            self.scopes.push(HashMap::new());
            for (name, (_, t)) in arm.params.iter().zip(&params) {
                self.declare(&name.name, t.clone());
            }
            if let Some(k) = &arm.resumes {
                // A continuation of a `void` operation takes no argument: `k()`.
                let params = if op_ret == Ty::void() { Vec::new() } else { vec![op_ret] };
                let cont = Ty::Fn(Box::new(FnTy { mode: FnMode::Once, params, ret: result.clone(), effects: EffRow::pure() }));
                self.declare(&k.name, cont);
            }
            let t = self.block(&arm.body, Some(&result));
            self.coerce(&t, &result, arm.body.span);
            self.scopes.pop();
        }
        result
    }

    // ---- match and patterns ----

    fn match_expr(&mut self, scrutinee: &Expr, arms: &[ast::MatchArm], expected: Option<&Ty>, span: Span) -> Ty {
        let st = self.expr(scrutinee, None);
        let mut types = Vec::new();
        for arm in arms {
            self.scopes.push(HashMap::new());
            self.bind(&arm.pat, &st);
            if let Some(g) = &arm.guard {
                self.check(g, &Ty::bool());
            }
            let t = self.expr(&arm.body, expected);
            types.push((t, arm.body.span));
            self.scopes.pop();
        }
        self.pending_matches.push((st, arms.to_vec(), span));
        self.join(&types, expected)
    }

    /// Binds a pattern's variables against a value of type `t`. Destructuring through a borrow
    /// binds borrows of the parts.
    fn bind(&mut self, pat: &Pattern, t: &Ty) {
        let resolved = self.s.resolve(t);
        let (mode, inner) = match &resolved {
            Ty::Borrow(m, i) => (Some(*m), (**i).clone()),
            _ => (None, resolved.clone()),
        };
        let wrap = |ty: Ty| match mode {
            Some(m) if !matches!(ty, Ty::Borrow(..)) => Ty::Borrow(m, Box::new(ty)),
            _ => ty,
        };
        match &pat.kind {
            PatternKind::Wild => {}
            PatternKind::Bind(name) => {
                self.typed.bindings.insert(pat.span, t.clone());
                self.declare(name, t.clone())
            }
            PatternKind::Lit(e) => {
                let v = self.strip(t);
                let lt = self.expr(e, Some(&v));
                if !self.try_unify(&lt, &v) {
                    let (a, b) = (self.show(&v), self.show(&lt));
                    self.err(pat.span, format!("pattern of type `{b}` cannot match `{a}`"));
                }
            }
            PatternKind::Tuple(pats) => {
                let elems: Vec<Ty> = match self.strip(&inner) {
                    Ty::Tuple(ts) if ts.len() == pats.len() => ts,
                    Ty::Var(_) => {
                        let ts: Vec<Ty> = pats.iter().map(|_| self.s.fresh()).collect();
                        let _ = self.s.unify(&inner, &Ty::Tuple(ts.clone()));
                        ts
                    }
                    other => {
                        let shown = self.show(&other);
                        self.err(pat.span, format!("a tuple pattern cannot match `{shown}`"));
                        vec![Ty::Error; pats.len()]
                    }
                };
                for (p, e) in pats.iter().zip(elems) {
                    self.bind(p, &wrap(e));
                }
            }
            PatternKind::Record { fields, .. } => {
                for (name, sub) in fields {
                    let ft = self.field(&inner, &name.name, name.span);
                    match sub {
                        Some(p) => self.bind(p, &wrap(ft)),
                        None => self.declare(&name.name, wrap(ft)),
                    }
                }
            }
            PatternKind::Tag { name, args } => {
                let payload = match self.tag_payloads(&inner) {
                    Some((tags, tail)) => match tags.get(name) {
                        Some(p) => p.clone(),
                        None if tail == Tail::Closed => {
                            let shown = self.show(&inner);
                            self.err(pat.span, format!("`#{name}` is not a tag of `{shown}`"));
                            Ty::Error
                        }
                        None => {
                            let p = self.s.fresh();
                            let mut one = BTreeMap::new();
                            one.insert(name.clone(), p.clone());
                            let tail = self.s.fresh_row_tail();
                            let _ = self.s.unify(&inner, &Ty::Union(Row { labels: one, tail }));
                            p
                        }
                    },
                    None => {
                        let shown = self.show(&inner);
                        if !matches!(self.s.resolve(&inner), Ty::Error) {
                            self.err(pat.span, format!("a tag pattern cannot match `{shown}`"));
                        }
                        Ty::Error
                    }
                };
                match args {
                    TagPatArgs::None => {}
                    TagPatArgs::Tuple(pats) => {
                        let parts = match self.s.resolve(&payload) {
                            Ty::Tuple(ts) if ts.len() == pats.len() => ts,
                            Ty::Error => vec![Ty::Error; pats.len()],
                            other => {
                                let shown = self.show(&other);
                                self.err(pat.span, format!("`#{name}` carries `{shown}`"));
                                vec![Ty::Error; pats.len()]
                            }
                        };
                        for (p, t) in pats.iter().zip(parts) {
                            self.bind(p, &wrap(t));
                        }
                    }
                    TagPatArgs::Record(fields) => {
                        for (fname, sub) in fields {
                            let ft = self.field(&payload, &fname.name, fname.span);
                            match sub {
                                Some(p) => self.bind(p, &wrap(ft)),
                                None => self.declare(&fname.name, wrap(ft)),
                            }
                        }
                    }
                }
            }
            PatternKind::Or(alts) => {
                for a in alts {
                    self.bind(a, t);
                }
            }
        }
    }

    /// Exhaustiveness for tag unions and enums, `bool`, and anything with a catch-all arm.
    fn exhaustive(&mut self, scrut: &Ty, arms: &[ast::MatchArm], span: Span) {
        fn irrefutable(p: &Pattern) -> bool {
            match &p.kind {
                PatternKind::Wild | PatternKind::Bind(_) => true,
                PatternKind::Tuple(ps) => ps.iter().all(irrefutable),
                PatternKind::Record { fields, .. } => fields.iter().all(|(_, p)| p.as_ref().is_none_or(irrefutable)),
                PatternKind::Or(ps) => ps.iter().any(irrefutable),
                _ => false,
            }
        }
        fn covered_tags(p: &Pattern, out: &mut Vec<String>, bools: &mut Vec<bool>) {
            match &p.kind {
                PatternKind::Tag { name, args } => {
                    let full = match args {
                        TagPatArgs::None => true,
                        TagPatArgs::Tuple(ps) => ps.iter().all(irrefutable),
                        TagPatArgs::Record(fs) => fs.iter().all(|(_, p)| p.as_ref().is_none_or(irrefutable)),
                    };
                    if full {
                        out.push(name.clone());
                    }
                }
                PatternKind::Lit(e) => {
                    if let ExprKind::Bool(b) = e.kind {
                        bools.push(b);
                    }
                }
                PatternKind::Or(ps) => ps.iter().for_each(|p| covered_tags(p, out, bools)),
                _ => {}
            }
        }
        let unguarded: Vec<&Pattern> = arms.iter().filter(|a| a.guard.is_none()).map(|a| &a.pat).collect();
        if unguarded.iter().any(|p| irrefutable(p)) {
            return;
        }
        let mut tags = Vec::new();
        let mut bools = Vec::new();
        for p in &unguarded {
            covered_tags(p, &mut tags, &mut bools);
        }
        let st = self.strip(scrut);
        if st == Ty::bool() {
            if !(bools.contains(&true) && bools.contains(&false)) {
                self.err(span, "this `match` does not cover every case of `bool`");
            }
            return;
        }
        match self.tag_payloads(&st) {
            Some((all, tail)) => {
                if let Tail::Var(_) = tail {
                    // Final types: nothing can add tags now (see `pending_matches`).
                    self.s.close_union(&st);
                }
                let tail = self.tag_payloads(&st).map_or(Tail::Closed, |(_, t)| t);
                if tail != Tail::Closed {
                    // An open union can always hold more tags; a catch-all is needed.
                    let shown = self.show(&st);
                    self.err(span, format!("this `match` needs a `_` arm: `{shown}` may hold more tags"));
                    return;
                }
                let missing: Vec<String> = all.keys().filter(|k| !tags.contains(k)).map(|k| format!("`#{k}`")).collect();
                if !missing.is_empty() {
                    self.err(span, format!("this `match` does not handle {}", missing.join(", ")));
                }
            }
            None => {
                if !matches!(st, Ty::Error) {
                    self.err(span, "this `match` needs a `_` arm to be exhaustive");
                }
            }
        }
    }
}

fn mentions_region(t: &Ty, sym: &Sym) -> bool {
    let arg = |a: &GArg| match a {
        GArg::Ty(t) => mentions_region(t, sym),
        GArg::Region(Region::Param(s)) => s == sym,
        _ => false,
    };
    match t {
        Ty::Named(_, args) => args.iter().any(arg),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(|t| mentions_region(t, sym)),
        Ty::Tuple(ts) => ts.iter().any(|t| mentions_region(t, sym)),
        Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) => mentions_region(t, sym),
        Ty::Fn(f) => f.params.iter().any(|t| mentions_region(t, sym)) || mentions_region(&f.ret, sym),
        _ => false,
    }
}

/// Replaces row-parameter tails in records and unions by instantiated row variables.
fn inst_record_tails(t: &Ty, tails: &HashMap<Sym, Tail>) -> Ty {
    let row = |r: &Row| Row {
        labels: r.labels.iter().map(|(k, t)| (k.clone(), inst_record_tails(t, tails))).collect(),
        tail: match &r.tail {
            Tail::Param(s) => tails.get(s).cloned().unwrap_or(r.tail.clone()),
            other => other.clone(),
        },
    };
    match t {
        Ty::Record(r) => Ty::Record(row(r)),
        Ty::Union(r) => Ty::Union(row(r)),
        Ty::Named(d, args) => Ty::Named(
            *d,
            args.iter()
                .map(|a| match a {
                    GArg::Ty(t) => GArg::Ty(inst_record_tails(t, tails)),
                    a => a.clone(),
                })
                .collect(),
        ),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| inst_record_tails(t, tails)).collect()),
        Ty::Array(t, l) => Ty::Array(Box::new(inst_record_tails(t, tails)), l.clone()),
        Ty::Slice(t) => Ty::Slice(Box::new(inst_record_tails(t, tails))),
        Ty::Borrow(m, t) => Ty::Borrow(*m, Box::new(inst_record_tails(t, tails))),
        Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
            mode: f.mode,
            params: f.params.iter().map(|t| inst_record_tails(t, tails)).collect(),
            ret: inst_record_tails(&f.ret, tails),
            effects: f.effects.clone(),
        })),
        t => t.clone(),
    }
}
