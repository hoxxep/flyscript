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
    /// The bounds of the generic parameters in scope, by symbol.
    bounds: HashMap<u32, Vec<Ty>>,
    /// Each call's generic arguments, and the bounds they must satisfy, checked once types are
    /// final.
    pending_targs: Vec<PendingCall>,
    /// Calls of templates, specialized once their `comptime` arguments are known.
    pending_specs: Vec<(Span, FnId, Vec<GArg>)>,
    /// `==`, `!=` and `${e}` on operands whose types are not yet final: each calls an
    /// interface's method unless the operand is a primitive (§3.5).
    pending_ops: Vec<(Span, Ty, &'static str, &'static str)>,
    /// In a derivation's specialization, the type that asked for it: its private fields are
    /// visible here (§7.3).
    privileged: Option<DefId>,
    /// Checking a `defer`, which cannot fail or yield (§5.6).
    in_defer: bool,
}

/// A call's span, its generic arguments, and each (argument, bound) pair it must satisfy.
type PendingCall = (Span, Vec<GArg>, Vec<(Ty, Ty)>);

/// Checks the body of `fid`, if it has one and has not been checked.
pub fn check_fn(p: &mut Program, fid: FnId) {
    if p.checked.contains(&fid) || !p.fns[fid].has_body {
        return;
    }
    p.checked.insert(fid);
    // A template is checked in each specialization, not on its own (§7.1).
    if p.is_template(fid) {
        return;
    }
    let info = &p.fns[fid];
    let module = info.module;
    let scheme = info.scheme.clone();
    let impl_target = info.impl_id.map(|i| p.impls[i].target.clone());
    let Some(mut fdecl) = p.fn_decl(fid) else { return };
    // A `comptime function` runs only in the compiler (§7.1).
    if fdecl.sig.comptime {
        return;
    }
    // A body that uses `comptime` code is expanded first (§7.2).
    if !p.bodies.contains_key(&fid)
        && let Some(b) = &fdecl.body
            && super::comptime::block_has_comptime(b) {
                fdecl.body = super::comptime::Expand::new(p, module, None, Vec::new()).body(b);
                p.bodies.insert(fid, fdecl.clone());
            }
    let Some(body) = fdecl.body.clone() else { return };
    let saved_note = std::mem::replace(&mut p.note, p.spec_notes.get(&fid).cloned());

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
        bounds: scheme.tparams.iter().map(|g| (g.sym.id, g.bounds.clone())).collect(),
        pending_targs: Vec::new(),
        pending_specs: Vec::new(),
        pending_ops: Vec::new(),
        privileged: None,
        in_defer: false,
    };
    c.privileged = c.p.spec_requested.get(&fid).copied();
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
    for (span, t, iface, method) in std::mem::take(&mut c.pending_ops) {
        // Through borrows and region references, which read as what they refer to.
        let mut t = c.s.zonk(&t);
        loop {
            let inner = match &t {
                Ty::Borrow(_, inner) => (**inner).clone(),
                Ty::Named(d, args) if c.p.known.get("Ref") == Some(d) => match args.get(1) {
                    Some(GArg::Ty(inner)) => inner.clone(),
                    _ => break,
                },
                _ => break,
            };
            t = inner;
        }
        // Primitives, and strings when written into a string, are built in.
        let builtin = match &t {
            Ty::Prim(_) | Ty::Error | Ty::Var(_) => true,
            Ty::Named(d, _) => iface == "Show" && c.p.known.get("String") == Some(d),
            _ => false,
        };
        if builtin {
            continue;
        }
        c.s.close_rows(&t);
        let t = c.s.zonk(&t);
        let Some(&d) = c.p.known.get(iface) else { continue };
        let assumed = |id: u32| c.bounds.get(&id).cloned().unwrap_or_default();
        if !c.p.satisfies(&t, &Ty::Named(d, Vec::new()), &assumed) {
            let shown = format!("{}", Show(&t, &*c.p));
            let hint = match &t {
                Ty::Named(n, _) => {
                    let name = c.p.defs[*n].name.clone();
                    // Asked for, but an interface it extends is missing (`Ord` needs `Eq`).
                    let missing = c.p.iface_closure(d).into_iter().skip(1).find(|s| !c.p.satisfies(&t, &Ty::Named(*s, Vec::new()), &assumed));
                    match missing {
                        Some(sup) if c.p.derive_request(d, *n) => {
                            let sup = c.p.defs[sup].name.clone();
                            format!(": `{iface}` needs `{sup}`; ask for it with `impl {sup} for {name};`")
                        }
                        _ => format!(": ask for it with `impl {iface} for {name};`"),
                    }
                }
                _ => String::new(),
            };
            c.p.error(module, span, format!("`{shown}` does not implement `{iface}`{hint}"));
            continue;
        }
        c.p.ensure_impl(d, &t, 0);
        if let Some(&f) = c.p.iface_fns.get(&(d, method.to_string())) {
            let table = if iface == "Show" { &mut c.typed.shows } else { &mut c.typed.ops };
            table.insert(span, (f, vec![GArg::Ty(t)]));
        }
    }
    for (span, args, bounds) in std::mem::take(&mut c.pending_targs) {
        for a in &args {
            if let GArg::Ty(t) = a {
                c.s.close_rows(t);
            }
        }
        for (t, b) in bounds {
            let (t, b) = (c.s.zonk(&t), c.s.zonk(&b));
            let assumed = |id: u32| c.bounds.get(&id).cloned().unwrap_or_default();
            if !c.p.satisfies(&t, &b, &assumed) {
                let (ts, bs) = (format!("{}", Show(&t, &*c.p)), format!("{}", Show(&b, &*c.p)));
                c.p.error(module, span, format!("`{ts}` does not implement `{bs}`"));
            } else if let Ty::Named(d, _) = &b
                && matches!(c.p.defs[*d].kind, DefKind::Interface { .. }) {
                    c.p.ensure_impl(*d, &t, 0);
                }
        }
        let args = args.iter().map(|a| c.s.zonk_arg(a)).collect();
        c.typed.targs.insert(span, args);
    }
    for (span, tfid, args) in std::mem::take(&mut c.pending_specs) {
        let tparams = c.p.fns[tfid].scheme.tparams.clone();
        let binds: super::impls::Binds = tparams.iter().zip(&args).map(|(g, a)| (g.sym.id, c.s.zonk_arg(a))).collect();
        let Some(ct) = c.p.comptime_args(tfid, &binds) else { continue };
        if let Some((s, _)) = ct.iter().find(|(_, t)| super::impls::contains_params(t)) {
            let name = s.name.clone();
            c.p.error(module, span, format!("the `comptime` type `{name}` must be known here; it cannot depend on a generic parameter"));
            continue;
        }
        let spec = c.p.specialize_for(tfid, &ct);
        c.typed.calls.insert(span, spec);
        let rest: Vec<GArg> = tparams.iter().zip(&args).filter(|(g, _)| !g.comptime).map(|(_, a)| c.s.zonk_arg(a)).collect();
        c.typed.targs.insert(span, rest);
    }
    for (name, ty) in &scheme.params {
        c.typed.params.push((name.clone(), ty.clone()));
    }
    let mut typed = std::mem::take(&mut c.typed);
    for t in typed.exprs.values_mut().chain(typed.bindings.values_mut()) {
        *t = c.s.zonk(t);
    }
    let mut spans: Vec<(&Span, &Ty)> = typed.exprs.iter().chain(typed.bindings.iter()).collect();
    spans.sort_by_key(|(sp, _)| (sp.start, sp.end));
    if let Some((span, (d, arg))) = spans.iter().find_map(|(sp, t)| c.p.borrow_in_container(t).map(|x| (**sp, x))) {
        let msg = container_message(c.p, d, &arg);
        c.p.error(module, span, msg);
    }
    c.p.typed.insert(fid, typed);
    if inferring {
        let mut row = c.s.zonk_effs(&c.allowed.clone());
        row.tail = Tail::Closed;
        if !row.effs.is_empty()
            && let Some((m, span)) = c.p.assumed_pure.get(&fid).copied() {
                let name = c.p.fns[fid].name.clone();
                let what = format!("{}", Show(&row, &*c.p));
                c.p.error(m, span, format!("`{name}` calls itself and performs `{what}`, so it must declare its effects with `uses`"));
            }
        c.p.inferred.insert(fid, Some(row));
    }
    c.p.note = saved_note;
}

pub fn container_message(p: &Program, d: DefId, arg: &Ty) -> String {
    let shown = format!("{}", Show(arg, p));
    let hint = if shown.contains("str") && !shown.contains("u8") { "an owned `String`" } else { "an owned value" };
    format!("`{}` cannot hold `{shown}`, which borrows: it holds owned values, so use {hint} (§4.2)", p.defs[d].name)
}

/// Effects of a function, inferring them from its body if it declares none.
fn fn_effects(p: &mut Program, fid: FnId, module: usize, span: Span) -> EffRow {
    if let Some(e) = &p.fns[fid].scheme.effects {
        return e.clone();
    }
    match p.inferred.get(&fid) {
        Some(Some(e)) => return e.clone(),
        // A function whose effects are being inferred, called again: it is assumed pure, which
        // its body must then bear out.
        Some(None) => {
            p.assumed_pure.insert(fid, (module, span));
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

    /// Normalizes associated types whose base is known (`Soa<P>.View`), through its impl (§3.4).
    fn normalize(&self, t: &Ty) -> Ty {
        match self.s.resolve(t) {
            Ty::Assoc(base, name) => {
                let base = self.s.resolve(&base);
                let known = self.s.zonk(&base);
                if let Some(t) = self.p.assoc_type(&known, &name) {
                    return self.normalize(&t);
                }
                Ty::Assoc(Box::new(base), name)
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
            // A record with a struct's fields: the struct is a new type, named where it is built.
            let hint = match (self.strip(found), self.strip(expected)) {
                (Ty::Record(r), Ty::Named(d, _)) if matches!(&self.p.defs[d].kind, DefKind::Struct { fields: Some(fs) }
                    if { let r = self.s.expand_row(&r); fs.len() == r.labels.len() && fs.iter().all(|(k, _)| r.labels.contains_key(k)) }) => {
                    let n = self.p.defs[d].name.clone();
                    format!(": a record is not a `{n}`; build it as one with `{n} {{ … }}`, or give its binding the type `{n}`")
                }
                _ => String::new(),
            };
            self.err(span, format!("expected `{x}`, found `{f}`{hint}"));
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
            let cleanup = self.in_defer && (self.p.known.get("Fail") == Some(&e.def) || self.p.known.get("Yield") == Some(&e.def));
            let msg = if cleanup {
                format!("a `defer` cannot perform {what}: it runs while its block is being left, perhaps by a failure")
            } else if self.p.known.get("Fail") == Some(&e.def) {
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
        let refs: SubstMap<'_> = map.iter().map(|(k, v)| (k.id, v)).collect();
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
                // Cleanup runs while unwinding, so it cannot fail, yield or leave (§5.6).
                Stmt::Defer(e) => {
                    let (fail, yld) = (self.known("Fail"), self.known("Yield"));
                    let mut row = self.s.expand_effs(&self.allowed.clone());
                    row.effs.retain(|eff| eff.def != fail && eff.def != yld);
                    if let Tail::Var(_) = row.tail {
                        row.tail = Tail::Closed;
                    }
                    let saved = std::mem::replace(&mut self.allowed, row);
                    let was = std::mem::replace(&mut self.in_defer, true);
                    self.expr(e, None);
                    self.in_defer = was;
                    self.allowed = saved;
                    if let Some(span) = leaves(e) {
                        self.err(span, "a `defer` cannot leave its block: it runs while the block is being left");
                    }
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
            ExprKind::TypeRef(i) => {
                let shown = self.show(&self.p.spliced[*i].clone());
                self.err(span, format!("the type `{shown}` is not a value"));
                Ty::Error
            }
            ExprKind::FieldAt { .. } | ExprKind::TagAt { .. } => {
                self.err(span, "a computed name `[e]` belongs in code that `comptime` generates");
                Ty::Error
            }
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
                        let t = self.expr(x, None);
                        self.pending_ops.push((x.span, t, "Show", "show"));
                    }
                }
                self.string_ty()
            }
            ExprKind::Ident(name) => self.ident(name, span),
            ExprKind::Tag { name, args } => self.tag(name, args, expected, span),
            ExprKind::Record { name, fields } => self.record(name.as_deref(), fields, expected, span),
            ExprKind::List(items) => self.list(items, expected),
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
        let whole = match (args, payload_expected.as_ref().map(|t| self.s.resolve(t))) {
            (TagArgs::Tuple(items), Some(Ty::Tuple(ts))) => items.len() == 1 && ts.len() != 1,
            (TagArgs::Tuple(items), Some(Ty::Record(_))) => items.len() == 1,
            _ => false,
        };
        let payload = match args {
            TagArgs::None => Ty::void(),
            // `#A(x)` with `x` the whole of a larger payload (§3.2).
            TagArgs::Tuple(items) if whole => {
                let p = payload_expected.clone().expect("whole payload");
                self.check(&items[0], &p);
                self.typed.whole.insert(span);
                p
            }
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
            Some(Ty::Named(d, args)) => {
                let args = args.iter().map(|a| self.s.zonk_arg(a)).collect::<Vec<_>>();
                self.p.ensure_instance(*d, &args);
                if self.p.failed_instance(*d, &args) {
                    for f in fields.iter().filter_map(|f| f.value.as_ref()) {
                        self.expr(f, None);
                    }
                    return Ty::Error;
                }
                self.p.struct_fields(*d, &args).map(|fs| fs.into_iter().collect())
            }
            Some(Ty::Record(r)) => Some(self.s.expand_row(r).labels),
            _ => None,
        };
        if let Some(Ty::Named(d, _)) = &target {
            self.unsealed(*d, "built", span);
        }
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
            // With nothing expected, a list is an array if its items agree, as in TypeScript, and a
            // tuple if they do not.
            _ => {
                let ts: Vec<Ty> = items.iter().map(|it| self.expr(it, None)).collect();
                match ts.split_first() {
                    Some((first, rest)) if rest.iter().all(|t| self.try_unify(first, t)) => Ty::Array(Box::new(first.clone()), Len::Known(ts.len() as u64)),
                    _ => Ty::Tuple(ts),
                }
            }
        }
    }

    /// Outside its module, a struct with private fields is built and taken apart only by the
    /// functions its module exports, so it can keep an invariant (§3.3).
    fn unsealed(&mut self, d: DefId, verb: &str, span: Span) {
        let def = &self.p.defs[d];
        if def.module != self.module && !def.private.is_empty() && self.privileged != Some(d) {
            let msg = format!("`{}` has private fields, so it cannot be {verb} outside its module", def.name);
            self.err(span, msg);
        }
    }

    fn field(&mut self, t: &Ty, name: &str, span: Span) -> Ty {
        let base = self.strip(t);
        if let Ty::Named(d, args) = &base {
            let args: Vec<GArg> = args.iter().map(|a| self.s.zonk_arg(a)).collect();
            self.p.ensure_instance(*d, &args);
            if self.p.failed_instance(*d, &args) {
                return Ty::Error;
            }
        }
        match &base {
            Ty::Named(d, args) => match &self.p.defs[*d].kind {
                DefKind::Struct { fields: Some(_) } => {
                    let fields = self.p.struct_fields(*d, &args.iter().map(|a| self.s.zonk_arg(a)).collect::<Vec<_>>()).unwrap_or_default();
                    if let Some((_, ft)) = fields.iter().find(|(k, _)| k == name) {
                        let ft = ft.clone();
                        let def = &self.p.defs[*d];
                        let hidden = def.module != self.module && def.private.iter().any(|f| f == name) && self.privileged != Some(*d);
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
            // `t.[i]`: an element of a tuple, by a `comptime` index (§7.2).
            Ty::Tuple(ts) if name.parse::<usize>().is_ok_and(|i| i < ts.len()) => return ts[name.parse::<usize>().expect("index")].clone(),
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
        // `t[0]`: a tuple's element, by a constant index, as in TypeScript (§3.1).
        if let Ty::Tuple(ts) = &base {
            return match &index.kind {
                ExprKind::Int(i) => match i.parse::<usize>().ok().and_then(|i| ts.get(i)) {
                    Some(t) => t.clone(),
                    None => {
                        self.err(index.span, format!("a tuple of {} has no element {i}", ts.len()));
                        Ty::Error
                    }
                },
                _ => {
                    self.err(index.span, "a tuple is indexed by a constant: `t[0]`");
                    Ty::Error
                }
            };
        }
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
        // A literal takes its type from the other side: `#Info < level`.
        let literal = |e: &Expr| matches!(e.kind, ExprKind::Tag { .. } | ExprKind::Record { name: None, .. } | ExprKind::List(_));
        let (l, r) = if literal(lhs) && !literal(rhs) {
            let r = self.expr(rhs, None);
            let r = self.strip(&r);
            let l = self.expr(lhs, Some(&r));
            (self.strip(&l), r)
        } else {
            let l = self.expr(lhs, None);
            let l = self.strip(&l);
            let r = self.expr(rhs, Some(&l));
            (l, self.strip(&r))
        };
        // An owner compared with what it lends is compared as that: `name == "ada"` for a
        // `String` (§3.5).
        let comparison = matches!(op, "==" | "!=" | "<" | ">" | "<=" | ">=");
        let l = if self.try_unify(&l, &r) {
            l
        } else if comparison && self.lends(&l, &Ty::Borrow(false, Box::new(r.clone()))) {
            r.clone()
        } else if comparison && self.lends(&r, &Ty::Borrow(false, Box::new(l.clone()))) {
            l
        } else {
            let (a, b) = (self.show(&l), self.show(&r));
            self.err(span, format!("`{op}` needs operands of the same type, found `{a}` and `{b}`"));
            l
        };
        match op {
            "==" | "!=" => {
                self.pending_ops.push((span, l.clone(), "Eq", "eq"));
                Ty::bool()
            }
            "<" | ">" | "<=" | ">=" => {
                self.pending_ops.push((span, l.clone(), "Ord", "cmp"));
                Ty::bool()
            }
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
                    if self.p.fn_decl(fid).is_some_and(|d| d.sig.comptime) {
                        self.err(span, format!("`{name}` is a `comptime function`: call it from `comptime` code"));
                        return Ty::Error;
                    }
                    return self.call_fn(fid, None, CallSite { explicit: &explicit, args, expected, span });
                }
            }
            ExprKind::Field { target, name } => {
                if let ExprKind::TypeRef(i) = &target.kind {
                    let ty = self.p.spliced[*i].clone();
                    return self.call_on_type(&ty, &name.name, CallSite { explicit: &explicit, args, expected, span });
                }
                if let ExprKind::Ident(tname) = &target.kind
                    && self.local(tname).is_none() {
                        if let Some((sym, _)) = self.scope.params.get(tname).cloned() {
                            let site = CallSite { explicit: &explicit, args, expected, span };
                            return self.call_on_type(&Ty::Param(sym), &name.name, site);
                        }
                        if let Some(Binding::Def(d)) = self.p.lookup(self.module, tname) {
                            return self.call_static(d, &name.name, &explicit, args, expected, span);
                        }
                    }
                let recv = self.expr(target, None);
                return self.call_method(&recv, target.span, &name.name, CallSite { explicit: &explicit, args, expected, span });
            }
            _ => {}
        }
        let t = self.expr(callee, None);
        // A function is called through a borrow of it, too, as its mode allows (§4.3): a shared
        // one through any borrow, a `mut` one through a `mut` borrow, a `once` one only by move.
        let through = match self.s.resolve(&t) {
            Ty::Borrow(m, _) => Some(m),
            _ => None,
        };
        // A continuation is called once, like a `once` function (§5.3).
        if let Ty::Named(d, cargs) = self.strip(&t)
            && d == self.known("Cont") {
                let (Some(GArg::Ty(a)), Some(GArg::Ty(b))) = (cargs.first(), cargs.get(1)) else { return Ty::Error };
                if through.is_some() {
                    self.err(callee.span, "a continuation is called only by moving it");
                }
                let params = if *a == Ty::void() { Vec::new() } else { vec![a.clone()] };
                self.check_args(&params, args, span);
                if let Some(GArg::Row(e)) = cargs.get(2) {
                    let e = e.clone();
                    self.perform(&e, span);
                }
                return b.clone();
            }
        match self.strip(&t) {
            Ty::Fn(f) if through.is_some() && (f.mode == FnMode::Once || f.mode == FnMode::Mut && through == Some(false)) => {
                let (mode, how) = if f.mode == FnMode::Once { ("once", "only by moving it") } else { ("mut", "only through a `mut` borrow") };
                self.err(callee.span, format!("a `{mode}` function is called {how}"));
                f.ret
            }
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

    /// Computes the associated types in `t` whose base is now known (§3.4).
    fn ensure_assocs(&mut self, t: &Ty) {
        match self.s.resolve(t) {
            Ty::Assoc(base, name) => {
                let base = self.s.zonk(&base);
                self.p.ensure_assoc(&base, &name);
            }
            Ty::Fn(f) => {
                for p in &f.params {
                    self.ensure_assocs(p);
                }
                self.ensure_assocs(&f.ret);
            }
            Ty::Borrow(_, inner) => self.ensure_assocs(&inner),
            _ => {}
        }
    }

    fn check_args(&mut self, params: &[Ty], args: &[Expr], span: Span) {
        if params.len() != args.len() {
            self.err(span, format!("expected {} arguments, found {}", params.len(), args.len()));
        }
        for (p, a) in params.iter().zip(args) {
            self.ensure_assocs(p);
            let p = self.normalize(p);
            self.check(a, &p);
        }
    }

    fn call_fn(&mut self, fid: FnId, recv: Option<(Ty, Span)>, site: CallSite<'_>) -> Ty {
        self.call_fn_fixed(fid, &[], recv, site)
    }

    /// Calls `fid` with its leading generic arguments fixed: `Self` and the interface's
    /// arguments, for a method called through a bound.
    fn call_fn_fixed(&mut self, fid: FnId, fixed: &[GArg], recv: Option<(Ty, Span)>, site: CallSite<'_>) -> Ty {
        let CallSite { explicit, args, expected, span } = site;
        self.typed.calls.insert(span, fid);
        let scheme = self.p.fns[fid].scheme.clone();
        let effects = fn_effects(self.p, fid, self.module, span);
        let scheme = Scheme { effects: Some(effects), ..scheme };
        let inst = self.instantiate(&scheme, &[], true);
        for (a, f) in inst.args.iter().zip(fixed) {
            if let (GArg::Ty(a), GArg::Ty(f)) = (a, f) {
                let _ = self.s.unify(a, f);
            }
        }
        let bounds: Vec<(Ty, Ty)> = scheme
            .tparams
            .iter()
            .zip(&inst.args)
            .skip(fixed.len())
            .filter_map(|(g, a)| match a {
                GArg::Ty(t) => Some(g.bounds.iter().map(|b| (t.clone(), subst_params(b, &scheme.tparams, &inst.args))).collect::<Vec<_>>()),
                _ => None,
            })
            .flatten()
            .collect();
        self.pending_targs.push((span, inst.args.clone(), bounds));
        if self.p.is_template(fid) {
            self.pending_specs.push((span, fid, inst.args.clone()));
        }
        // Explicit type arguments apply to the function's own parameters, or to its impl's when
        // it has none (`HashMap.new<String, u64>()`).
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
                let args_ty = self.p.defs[def].params.iter().map(|_| GArg::Ty(self.s.fresh())).collect::<Vec<_>>();
                let ty = self.normalize(&Ty::Named(def, self.p.defs[def].params.iter().zip(args_ty).map(|(g, a)| match g.kind {
                    PKind::Type => a,
                    _ => super::impls::param_arg(g),
                }).collect()));
                self.call_on_type(&ty, name, CallSite { explicit, args, expected, span })
            }
        }
    }

    /// `T.f(…)` for a function of an interface `T` implements, without `self` (`User.decode(p)`).
    fn call_on_type(&mut self, ty: &Ty, name: &str, site: CallSite<'_>) -> Ty {
        if let Ty::Param(sym) = ty
            && let Some(bounds) = self.bounds.get(&sym.id).cloned()
                && let Some((fid, Ty::Named(_, args))) = self.p.bound_method(&bounds, name) {
                    let mut fixed = vec![GArg::Ty(ty.clone())];
                    fixed.extend(args);
                    return self.call_fn_fixed(fid, &fixed, None, site);
                }
        let ifaces: Vec<DefId> = self.p.iface_fns.keys().filter(|(_, n)| n == name).map(|(d, _)| *d).collect();
        for d in ifaces {
            let concrete = self.s.zonk(ty);
            if let Some((imp, binds)) = self.p.resolve_impl(d, &concrete) {
                let fid = if self.p.is_template_impl(imp) { self.p.impl_method(imp, name) } else { self.p.method_for(imp, name, &binds) };
                if let Some(fid) = fid {
                    let fixed: Vec<GArg> = if self.p.is_template_impl(imp) { vec![GArg::Ty(concrete.clone())] } else { Vec::new() };
                    return self.call_fn_fixed(fid, &fixed, None, site);
                }
            }
        }
        let shown = self.show(ty);
        self.err(site.span, format!("`{shown}` has no function `{name}`"));
        Ty::Error
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
    /// A method called through a bound of the receiver's type parameter: the interface method
    /// and the fixed arguments (`Self`, then the bound's).
    fn bound_method(&mut self, recv: &Ty, name: &str) -> Option<(FnId, Vec<GArg>)> {
        let mut t = self.s.resolve(recv);
        while let Ty::Borrow(_, inner) = t {
            t = self.s.resolve(&inner);
        }
        let Ty::Param(sym) = &t else { return None };
        let bounds = self.bounds.get(&sym.id)?.clone();
        let (fid, via) = self.p.bound_method(&bounds, name)?;
        let Ty::Named(_, args) = via else { return None };
        let mut fixed = vec![GArg::Ty(t.clone())];
        fixed.extend(args);
        Some((fid, fixed))
    }

    fn find_method(&mut self, recv: &Ty, name: &str) -> Option<FnId> {
        let candidates: Vec<FnId> = (0..self.p.fns.len())
            .filter(|f| {
                let info = &self.p.fns[*f];
                info.name == name
                    && info.impl_id.is_some_and(|i| !self.p.is_blanket(i))
                    && self.has_self(*f)
                    && !self.p.spec_of.contains_key(f)
            })
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
        // A derivation: the template impl of an interface with this method (§7.3).
        let recv = self.s.zonk(recv);
        let ifaces: Vec<DefId> = self.p.iface_fns.keys().filter(|(_, n)| n == name).map(|(d, _)| *d).collect();
        for d in ifaces {
            // The template's method: it is specialized once the receiver's type is final.
            if let Some((imp, _)) = self.p.resolve_impl(d, &recv)
                && self.p.is_blanket(imp) {
                    return self.p.impl_method(imp, name);
                }
        }
        None
    }

    fn call_method(&mut self, recv: &Ty, rspan: Span, name: &str, site: CallSite<'_>) -> Ty {
        let span = site.span;
        if let Some((fid, fixed)) = self.bound_method(recv, name) {
            return self.call_fn_fixed(fid, &fixed, Some((recv.clone(), rspan)), site);
        }
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
                // Resuming may perform what the code around the `handle` may.
                let around = self.allowed.clone();
                let cont = Ty::Named(self.known("Cont"), vec![GArg::Ty(op_ret), GArg::Ty(result.clone()), GArg::Row(around)]);
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
            PatternKind::TagAt { .. } => self.err(pat.span, "a computed name `[e]` belongs in code that `comptime` generates"),
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
                    // An array of the same length is taken apart the same way: `const [a, b] = xs`.
                    Ty::Array(e, Len::Known(n)) if n as usize == pats.len() => vec![(*e).clone(); pats.len()],
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
                if let Ty::Named(d, _) = self.strip(&inner) {
                    self.unsealed(d, "taken apart", pat.span);
                }
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
                    // `#A(x)` binds the whole of a larger payload (§3.2).
                    TagPatArgs::Tuple(pats) if pats.len() == 1 && matches!(self.s.resolve(&payload), Ty::Record(_)) || matches!(self.s.resolve(&payload), Ty::Tuple(ts) if ts.len() != 1 && pats.len() == 1) => {
                        self.bind(&pats[0], &wrap(self.s.resolve(&payload)));
                    }
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
    /// Whether the arms of a `match` cover every value of `scrut`, over nested patterns
    /// (Maranget's usefulness algorithm); if not, reports a value they miss.
    fn exhaustive(&mut self, scrut: &Ty, arms: &[ast::MatchArm], span: Span) {
        let st = self.strip(scrut);
        if let Some((_, Tail::Var(_))) = self.tag_payloads(&st) {
            // Final types: nothing can add tags now (see `pending_matches`).
            self.s.close_union(&st);
        }
        let unguarded: Vec<&Pattern> = arms.iter().filter(|a| a.guard.is_none()).map(|a| &a.pat).collect();
        if let Some((_, Tail::Param(_))) = self.tag_payloads(&st)
            && !unguarded.iter().any(|p| matches!(p.kind, PatternKind::Wild | PatternKind::Bind(_))) {
                let shown = self.show(&st);
                self.err(span, format!("this `match` needs a `_` arm: `{shown}` may hold more tags"));
                return;
            }
        let rows: Vec<Vec<Pat>> = unguarded.iter().map(|p| vec![self.lower_pat(p, &st)]).collect();
        if let Some(w) = self.missing(rows, vec![st.clone()]) {
            let shown = w[0].show();
            if st == Ty::bool() {
                self.err(span, "this `match` does not cover every case of `bool`");
            } else if shown == "_" {
                self.err(span, "this `match` needs a `_` arm to be exhaustive");
            } else {
                self.err(span, format!("this `match` does not handle `{shown}`"));
            }
        }
    }

    /// The constructors of a type and the types of their fields, if there are finitely many.
    fn ctors(&mut self, t: &Ty) -> Option<Vec<(Ctor, Vec<Ty>)>> {
        let t = self.strip(t);
        if t == Ty::bool() {
            return Some(vec![(Ctor::Bool(false), Vec::new()), (Ctor::Bool(true), Vec::new())]);
        }
        if let Some((tags, tail)) = self.tag_payloads(&t) {
            let tail = if let Tail::Var(_) = tail {
                self.s.close_union(&t);
                Tail::Closed
            } else {
                tail
            };
            if tail != Tail::Closed {
                return None;
            }
            return Some(tags.into_iter().map(|(k, p)| {
                let fields = payload_fields(&self.s.resolve(&p));
                (Ctor::Tag(k), fields)
            }).collect());
        }
        match &t {
            Ty::Tuple(ts) => Some(vec![(Ctor::Tuple, ts.clone())]),
            Ty::Array(e, Len::Known(n)) => Some(vec![(Ctor::Tuple, vec![(**e).clone(); *n as usize])]),
            Ty::Record(r) => Some(vec![(Ctor::Record, self.s.expand_row(r).labels.into_values().collect())]),
            Ty::Named(d, args) => match &self.p.defs[*d].kind {
                DefKind::Struct { fields: Some(_) } => {
                    self.p.ensure_instance(*d, args);
                    let mut fs = self.p.struct_fields(*d, args).unwrap_or_default();
                    fs.sort_by(|a, b| a.0.cmp(&b.0));
                    Some(vec![(Ctor::Record, fs.into_iter().map(|(_, t)| t).collect())])
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// A pattern as constructors and wildcards, for the exhaustiveness check.
    fn lower_pat(&mut self, p: &Pattern, t: &Ty) -> Pat {
        let t = self.strip(t);
        match &p.kind {
            PatternKind::Wild | PatternKind::Bind(_) => Pat::Wild,
            PatternKind::Or(ps) => Pat::Or(ps.iter().map(|q| self.lower_pat(q, &t)).collect()),
            PatternKind::Lit(e) => match &e.kind {
                ExprKind::Bool(b) => Pat::Ctor(Ctor::Bool(*b), Vec::new()),
                _ => Pat::Ctor(Ctor::Lit, Vec::new()),
            },
            PatternKind::Tuple(ps) => match &t {
                Ty::Tuple(ts) if ts.len() == ps.len() => Pat::Ctor(Ctor::Tuple, ps.iter().zip(ts).map(|(q, t)| self.lower_pat(q, t)).collect()),
                Ty::Array(e, Len::Known(n)) if *n as usize == ps.len() => Pat::Ctor(Ctor::Tuple, ps.iter().map(|q| self.lower_pat(q, e)).collect()),
                _ => Pat::Never,
            },
            PatternKind::Record { fields, .. } => {
                let Some(all) = self.ctors(&t).and_then(|c| c.into_iter().next()).filter(|(c, _)| *c == Ctor::Record) else { return Pat::Never };
                let labels = self.record_labels(&t);
                let subs = labels
                    .iter()
                    .zip(all.1)
                    .map(|(l, ft)| match fields.iter().find(|(n, _)| &n.name == l) {
                        Some((_, Some(q))) => self.lower_pat(q, &ft),
                        _ => Pat::Wild,
                    })
                    .collect();
                Pat::Ctor(Ctor::Record, subs)
            }
            PatternKind::Tag { name, args } => {
                let Some((tags, _)) = self.tag_payloads(&t) else { return Pat::Never };
                let Some(payload) = tags.get(name).map(|p| self.s.resolve(p)) else { return Pat::Never };
                let fields = payload_fields(&payload);
                let subs = match (args, &payload) {
                    (TagPatArgs::None, _) => vec![Pat::Wild; fields.len()],
                    (TagPatArgs::Tuple(ps), Ty::Tuple(ts)) if ps.len() == ts.len() => ps.iter().zip(ts).map(|(q, t)| self.lower_pat(q, t)).collect(),
                    // `#A(x)` with a larger payload: `x` matches the payload whole (§3.2).
                    (TagPatArgs::Tuple(ps), _) if ps.len() == 1 => match self.lower_pat(&ps[0], &payload) {
                        Pat::Wild => vec![Pat::Wild; fields.len()],
                        Pat::Ctor(Ctor::Tuple | Ctor::Record, subs) => subs,
                        _ => return Pat::Never,
                    },
                    (TagPatArgs::Record(fs), Ty::Record(r)) => {
                        let labels: Vec<String> = r.labels.keys().cloned().collect();
                        labels
                            .iter()
                            .zip(&fields)
                            .map(|(l, ft)| match fs.iter().find(|(n, _)| &n.name == l) {
                                Some((_, Some(q))) => self.lower_pat(q, ft),
                                _ => Pat::Wild,
                            })
                            .collect()
                    }
                    _ => return Pat::Never,
                };
                Pat::Ctor(Ctor::Tag(name.clone()), subs)
            }
            PatternKind::TagAt { .. } => Pat::Never,
        }
    }

    fn record_labels(&mut self, t: &Ty) -> Vec<String> {
        match t {
            Ty::Record(r) => self.s.expand_row(r).labels.into_keys().collect(),
            Ty::Named(d, args) => match &self.p.defs[*d].kind {
                DefKind::Struct { fields: Some(_) } => {
                    let mut ls: Vec<String> = self.p.struct_fields(*d, args).unwrap_or_default().into_iter().map(|(k, _)| k).collect();
                    ls.sort();
                    ls
                }
                _ => Vec::new(),
            },
            _ => Vec::new(),
        }
    }

    /// A vector of values the rows do not match, if there is one: the usefulness of a row of
    /// wildcards against `rows`, whose columns have types `tys`.
    fn missing(&mut self, rows: Vec<Vec<Pat>>, tys: Vec<Ty>) -> Option<Vec<Witness>> {
        let Some(t0) = tys.first().cloned() else {
            return if rows.is_empty() { Some(Vec::new()) } else { None };
        };
        // Or-patterns in the first column become rows of their own.
        let mut flat = Vec::new();
        for r in rows {
            match &r[0] {
                Pat::Or(alts) => {
                    for a in alts {
                        let mut r2 = vec![a.clone()];
                        r2.extend(r[1..].iter().cloned());
                        flat.push(r2);
                    }
                }
                _ => flat.push(r),
            }
        }
        let rows = flat;
        let rest_tys: Vec<Ty> = tys[1..].to_vec();
        let used: Vec<Ctor> = rows.iter().filter_map(|r| if let Pat::Ctor(c, _) = &r[0] { Some(c.clone()) } else { None }).collect();
        let default = |rows: &[Vec<Pat>]| -> Vec<Vec<Pat>> { rows.iter().filter(|r| matches!(r[0], Pat::Wild)).map(|r| r[1..].to_vec()).collect() };
        match self.ctors(&t0) {
            Some(all) if all.iter().all(|(c, _)| used.contains(c)) => {
                for (c, ftys) in all {
                    let n = ftys.len();
                    let spec: Vec<Vec<Pat>> = rows
                        .iter()
                        .filter_map(|r| match &r[0] {
                            Pat::Ctor(c2, subs) if *c2 == c => Some(subs.iter().cloned().chain(r[1..].iter().cloned()).collect()),
                            Pat::Wild => Some(std::iter::repeat_n(Pat::Wild, n).chain(r[1..].iter().cloned()).collect()),
                            _ => None,
                        })
                        .collect();
                    let mut sub_tys = ftys.clone();
                    sub_tys.extend(rest_tys.iter().cloned());
                    if let Some(w) = self.missing(spec, sub_tys) {
                        let mut out = vec![Witness::Ctor(c.clone(), w[..n].to_vec())];
                        out.extend(w[n..].iter().cloned());
                        return Some(out);
                    }
                }
                None
            }
            Some(all) => {
                let w = self.missing(default(&rows), rest_tys)?;
                let (c, ftys) = all.into_iter().find(|(c, _)| !used.contains(c)).expect("a constructor not used");
                let mut out = vec![Witness::Ctor(c, vec![Witness::Wild; ftys.len()])];
                out.extend(w);
                Some(out)
            }
            None => {
                let w = self.missing(default(&rows), rest_tys)?;
                let mut out = vec![Witness::Wild];
                out.extend(w);
                Some(out)
            }
        }
    }
}

/// A pattern, for exhaustiveness: constructors applied to subpatterns, wildcards, alternatives,
/// and patterns the check cannot use (which cover nothing, so it stays sound).
#[derive(Clone, Debug)]
enum Pat {
    Wild,
    Never,
    Ctor(Ctor, Vec<Pat>),
    Or(Vec<Pat>),
}

#[derive(Clone, Debug, PartialEq)]
enum Ctor {
    Tag(String),
    Bool(bool),
    Tuple,
    Record,
    /// A number or string literal: there are always more.
    Lit,
}

/// A value a `match` misses.
#[derive(Clone, Debug)]
enum Witness {
    Wild,
    Ctor(Ctor, Vec<Witness>),
}

impl Witness {
    fn show(&self) -> String {
        match self {
            Witness::Wild => "_".into(),
            Witness::Ctor(Ctor::Bool(b), _) => b.to_string(),
            Witness::Ctor(Ctor::Tag(n), subs) if subs.is_empty() => format!("#{n}"),
            Witness::Ctor(Ctor::Tag(n), subs) if subs.iter().all(|w| matches!(w, Witness::Wild)) => format!("#{n}(_)"),
            Witness::Ctor(Ctor::Tag(n), subs) => format!("#{n}({})", subs.iter().map(|w| w.show()).collect::<Vec<_>>().join(", ")),
            Witness::Ctor(Ctor::Tuple, subs) => format!("[{}]", subs.iter().map(|w| w.show()).collect::<Vec<_>>().join(", ")),
            Witness::Ctor(Ctor::Record, _) => "{ … }".into(),
            Witness::Ctor(Ctor::Lit, _) => "_".into(),
        }
    }
}

/// The fields of a tag's payload, as the exhaustiveness check sees them: none, the elements of a
/// tuple, or a record's fields in label order.
fn payload_fields(p: &Ty) -> Vec<Ty> {
    match p {
        Ty::Prim(Prim::Void) => Vec::new(),
        Ty::Tuple(ts) => ts.clone(),
        Ty::Record(r) => r.labels.values().cloned().collect(),
        t => vec![t.clone()],
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

/// A `return`, or a `break` or `continue` of a loop around it, in an expression, outside the
/// functions written in it.
fn leaves(e: &Expr) -> Option<Span> {
    leaves_in(e, 0)
}

fn leaves_in(e: &Expr, loops: usize) -> Option<Span> {
    let block = |b: &ast::Block, loops: usize| -> Option<Span> {
        b.stmts
            .iter()
            .find_map(|st| match st {
                Stmt::Let { init, .. } => leaves_in(init, loops),
                Stmt::Defer(x) | Stmt::Expr(x) => leaves_in(x, loops),
            })
            .or_else(|| b.tail.as_deref().and_then(|t| leaves_in(t, loops)))
    };
    match &e.kind {
        ExprKind::Return(_) => Some(e.span),
        ExprKind::Break | ExprKind::Continue if loops == 0 => Some(e.span),
        ExprKind::Lambda { .. } => None,
        ExprKind::Block(b) | ExprKind::Unsafe(b) | ExprKind::Region { body: b, .. } => block(b, loops),
        ExprKind::If { cond, then, otherwise } => {
            leaves_in(cond, loops).or_else(|| block(then, loops)).or_else(|| otherwise.as_deref().and_then(|o| leaves_in(o, loops)))
        }
        ExprKind::While { cond, body } => leaves_in(cond, loops).or_else(|| block(body, loops + 1)),
        ExprKind::For { iter, body, .. } => leaves_in(iter, loops).or_else(|| block(body, loops + 1)),
        ExprKind::Match { scrutinee, arms } => leaves_in(scrutinee, loops).or_else(|| arms.iter().find_map(|a| leaves_in(&a.body, loops))),
        ExprKind::Try { body, handler, .. } => block(body, loops).or_else(|| block(handler, loops)),
        ExprKind::Handle { body, arms, .. } => block(body, loops).or_else(|| arms.iter().find_map(|a| block(&a.body, loops))),
        _ => super::own::children(e).into_iter().find_map(|c| leaves_in(c, loops)),
    }
}
