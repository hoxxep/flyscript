//! Interfaces as bounds (§3.4): calling a method through a bound, choosing the impl for a type,
//! and checking that a type satisfies a bound.

use std::collections::HashMap;

use super::comptime::{CV, Expand};
use super::env::{DeclRef, DefKind, FnId, FnInfo, GParam, PKind, Program, Scheme, SubstMap, subst, subst_effs, subst_params};
use super::types::*;

/// The generic arguments an impl was matched with, by parameter symbol.
pub type Binds = HashMap<u32, GArg>;

impl Program {
    /// Registers each method of interface `iface` as a function callable through a bound. Its
    /// generic parameters are `Self`, then the interface's, then the method's own.
    pub(super) fn declare_iface_fns(&mut self, iface: DefId, module: usize, methods: &[(String, Scheme)], self_sym: &Sym) {
        let iparams = self.defs[iface].params.clone();
        let bound = Ty::Named(iface, iparams.iter().map(param_arg).collect());
        for (name, scheme) in methods {
            let mut tparams = vec![GParam { sym: self_sym.clone(), kind: PKind::Type, bounds: vec![bound.clone()], default: None, comptime: false }];
            tparams.extend(iparams.iter().cloned());
            tparams.extend(scheme.tparams.iter().cloned());
            let id = self.fns.len();
            self.fns.push(FnInfo {
                name: name.clone(),
                module,
                // An interface method states its effects; none means pure.
                scheme: Scheme { tparams, effects: Some(scheme.effects.clone().unwrap_or_else(EffRow::pure)), ..scheme.clone() },
                decl: DeclRef { module, item: usize::MAX, method: None },
                exported: true,
                impl_id: None,
                has_body: false,
                iface: Some(iface),
            });
            self.iface_fns.insert((iface, name.clone()), id);
        }
    }

    /// `iface` and every interface it extends, transitively.
    pub fn iface_closure(&self, iface: DefId) -> Vec<DefId> {
        let mut out = vec![iface];
        let mut i = 0;
        while i < out.len() {
            if let DefKind::Interface { extends, .. } = &self.defs[out[i]].kind {
                for e in extends {
                    if let Ty::Named(d, _) = e
                        && !out.contains(d) {
                            out.push(*d);
                        }
                }
            }
            i += 1;
        }
        out
    }

    /// The interface method `name` reachable from a bound, with the bound it came through.
    pub fn bound_method(&self, bounds: &[Ty], name: &str) -> Option<(FnId, Ty)> {
        for b in bounds {
            let Ty::Named(d, _) = b else { continue };
            for i in self.iface_closure(*d) {
                if let Some(f) = self.iface_fns.get(&(i, name.to_string())) {
                    // A method of an extended interface is reached through the bound's own
                    // arguments only when it is the bound itself.
                    let via = if i == *d { b.clone() } else { Ty::Named(i, self.defs[i].params.iter().map(param_arg).collect()) };
                    return Some((*f, via));
                }
            }
        }
        None
    }

    /// The impl of `iface` for the concrete type `ty`, with the arguments its parameters take.
    pub fn resolve_impl(&self, iface: DefId, ty: &Ty) -> Option<(usize, Binds)> {
        self.resolve_depth(iface, ty, 0)
    }

    fn resolve_depth(&self, iface: DefId, ty: &Ty, depth: usize) -> Option<(usize, Binds)> {
        if depth > 16 {
            return None;
        }
        let ty = strip_borrows(ty);
        // Specific impls first; a template impl only for structural types, and for nominal types
        // that ask for it with `impl I for T;` (§7.3).
        let candidates = (0..self.impls.len()).filter(|i| !self.is_template_impl(*i)).chain((0..self.impls.len()).filter(|i| self.is_template_impl(*i)));
        for i in candidates {
            let imp = &self.impls[i];
            if imp.derived || imp.interface.as_ref().map(|(d, _)| *d) != Some(iface) {
                continue;
            }
            if self.is_template_impl(i) && !self.derives(iface, ty) {
                continue;
            }
            let vars: Vec<u32> = imp.params.iter().map(|g| g.sym.id).collect();
            let mut binds = Binds::new();
            if !match_ty(&imp.target, ty, &vars, &mut binds) {
                continue;
            }
            let args: Vec<GArg> = imp.params.iter().map(|g| binds.get(&g.sym.id).cloned().unwrap_or_else(|| param_arg(g))).collect();
            let ok = imp.params.iter().zip(&args).all(|(g, a)| match a {
                GArg::Ty(t) => g.bounds.iter().all(|b| {
                    let b = subst_params(b, &imp.params, &args);
                    self.satisfies_depth(t, &b, &|_| Vec::new(), depth + 1)
                }),
                _ => true,
            });
            // Implementing an interface means meeting the interfaces it extends (§3.4).
            let supers = self.iface_closure(iface);
            let supers_ok = supers.iter().skip(1).all(|s| self.satisfies_depth(ty, &Ty::Named(*s, Vec::new()), &|_| Vec::new(), depth + 1));
            // The first impl whose head matches is the one: if its bounds fail, the type does
            // not implement the interface, rather than falling back to a derivation (§7.3).
            return (ok && supers_ok).then_some((i, binds));
        }
        None
    }

    /// Whether `ty` satisfies `bound`, where `assumed` gives the bounds of type parameters in scope.
    pub fn satisfies(&self, ty: &Ty, bound: &Ty, assumed: &dyn Fn(u32) -> Vec<Ty>) -> bool {
        self.satisfies_depth(ty, bound, assumed, 0)
    }

    fn satisfies_depth(&self, ty: &Ty, bound: &Ty, assumed: &dyn Fn(u32) -> Vec<Ty>, depth: usize) -> bool {
        let Ty::Named(d, _) = bound else { return true };
        let send = self.known.get("Send").copied();
        let send_params: Vec<u32> = match ty {
            Ty::Param(s) if assumed(s.id).iter().any(|b| matches!(b, Ty::Named(x, _) if self.iface_closure(*x).iter().any(|i| Some(*i) == send))) => vec![s.id],
            _ => Vec::new(),
        };
        match self.defs[*d].name.as_str() {
            "Send" if self.is_std_def(*d) => return self.is_send_given(ty, &send_params) || matches!(ty, Ty::Error | Ty::Var(_)),
            "Copy" if self.is_std_def(*d) => return self.is_copy(ty) || matches!(ty, Ty::Param(_) | Ty::Var(_)),
            // `Q extends LentBy<K>`: a `Q` is what a `K` lends, to look it up (§3.3).
            "LentBy" if self.is_std_def(*d) => {
                let Ty::Named(_, args) = bound else { return true };
                let Some(GArg::Ty(k)) = args.first() else { return true };
                return self.lent_by(strip_borrows(ty), strip_borrows(k));
            }
            _ => {}
        }
        if !matches!(self.defs[*d].kind, DefKind::Interface { .. }) {
            return true;
        }
        match strip_borrows(ty) {
            Ty::Param(s) => assumed(s.id).iter().any(|b| matches!(b, Ty::Named(x, _) if self.iface_closure(*x).contains(d))),
            Ty::Var(_) | Ty::Error => true,
            t => self.resolve_depth(*d, t, depth).is_some(),
        }
    }

    fn lent_by(&self, q: &Ty, k: &Ty) -> bool {
        if q == k || matches!(q, Ty::Var(_) | Ty::Param(_) | Ty::Error) || matches!(k, Ty::Var(_) | Ty::Param(_)) {
            return true;
        }
        match (q, k) {
            (Ty::Prim(Prim::Str), Ty::Named(d, _)) => self.known.get("String") == Some(d),
            (Ty::Slice(e), Ty::Named(d, args)) => {
                self.known.get("Vec") == Some(d) && matches!(args.first(), Some(GArg::Ty(t)) if t == e.as_ref())
            }
            _ => false,
        }
    }

    fn is_std_def(&self, d: DefId) -> bool {
        self.modules[self.defs[d].module].is_std
    }

    /// The method `name` of impl `imp`.
    pub fn impl_method(&self, imp: usize, name: &str) -> Option<FnId> {
        self.impls[imp].methods.iter().copied().find(|f| self.fns[*f].name == name)
    }

    pub fn is_template_impl(&self, imp: usize) -> bool {
        self.impls[imp].params.iter().any(|g| g.comptime)
    }

    /// Whether `iface`'s template impl applies to `ty`.
    fn derives(&self, iface: DefId, ty: &Ty) -> bool {
        match ty {
            // Types that belong to no module: primitives, records, tuples, tag unions (§7.3).
            Ty::Prim(_) | Ty::Record(_) | Ty::Union(_) | Ty::Tuple(_) => true,
            Ty::Named(d, _) => self.derive_request(iface, *d),
            _ => false,
        }
    }

    fn derive_request(&self, iface: DefId, d: DefId) -> bool {
        self.impls.iter().any(|r| r.derived && r.interface.as_ref().map(|(i, _)| *i) == Some(iface) && matches!(&r.target, Ty::Named(x, _) if *x == d))
    }

    /// A function with `comptime` type parameters that has not been specialized.
    pub fn is_template(&self, fid: FnId) -> bool {
        !self.spec_of.contains_key(&fid) && self.fns[fid].scheme.tparams.iter().any(|g| g.comptime)
    }

    /// The `comptime` arguments of `fid` among `args`, in its parameter order.
    pub fn comptime_args(&self, fid: FnId, args: &Binds) -> Option<Vec<(Sym, Ty)>> {
        self.fns[fid]
            .scheme
            .tparams
            .iter()
            .filter(|g| g.comptime)
            .map(|g| match args.get(&g.sym.id) {
                Some(GArg::Ty(t)) => Some((g.sym.clone(), t.clone())),
                _ => None,
            })
            .collect()
    }

    /// The method `name` of impl `imp` matched with `binds`: for a template impl, its
    /// specialization, which must exist.
    pub fn method_for(&self, imp: usize, name: &str, binds: &Binds) -> Option<FnId> {
        let m = self.impl_method(imp, name)?;
        if !self.is_template(m) {
            return Some(m);
        }
        let ct = self.comptime_args(m, binds)?;
        self.specs.get(&(m, spec_key(&ct))).copied()
    }

    /// Like `method_for`, specializing the template impl's method if it has not been.
    pub fn method_for_mut(&mut self, imp: usize, name: &str, binds: &Binds) -> Option<FnId> {
        let m = self.impl_method(imp, name)?;
        if !self.is_template(m) {
            return Some(m);
        }
        let ct = self.comptime_args(m, binds)?;
        Some(self.specialize_for(m, &ct))
    }

    /// Specializes `fid`; a template impl's method is specialized on behalf of the type that
    /// asked for the derivation, which may then see its private fields (§7.3).
    pub fn specialize_for(&mut self, fid: FnId, ct: &[(Sym, Ty)]) -> FnId {
        let from_template_impl = self.fns[fid].impl_id.is_some_and(|i| self.is_template_impl(i));
        let requested = match ct.first().map(|(_, t)| strip_borrows(t)) {
            Some(Ty::Named(d, _)) if from_template_impl => Some(*d),
            _ => None,
        };
        self.specialize(fid, ct, requested)
    }

    /// Makes sure every impl that `ty` satisfying `iface` relies on is specialized, so a call
    /// through a bound finds it at run time.
    pub fn ensure_impl(&mut self, iface: DefId, ty: &Ty, depth: usize) {
        if depth > 16 || contains_params(ty) {
            return;
        }
        let Some((imp, binds)) = self.resolve_impl(iface, ty) else { return };
        if self.is_template_impl(imp) {
            let names: Vec<String> = self.impls[imp].methods.iter().map(|f| self.fns[*f].name.clone()).collect();
            for n in names {
                self.method_for_mut(imp, &n, &binds);
            }
        }
        let params = self.impls[imp].params.clone();
        let args: Vec<GArg> = params.iter().map(|g| binds.get(&g.sym.id).cloned().unwrap_or_else(|| param_arg(g))).collect();
        for (g, a) in params.iter().zip(&args) {
            if let GArg::Ty(t) = a {
                for b in &g.bounds {
                    if let Ty::Named(d, _) = subst_params(b, &params, &args)
                        && matches!(self.defs[d].kind, DefKind::Interface { .. }) {
                            self.ensure_impl(d, t, depth + 1);
                        }
                }
            }
        }
    }

    /// The specialization of template `fid` for its `comptime` arguments (§7.1): its signature
    /// with them substituted, and its body expanded. Memoized, and registered before its body is
    /// expanded, so a recursive type's derivation refers to itself.
    pub fn specialize(&mut self, fid: FnId, ct: &[(Sym, Ty)], requested: Option<DefId>) -> FnId {
        let key = (fid, spec_key(ct));
        if let Some(f) = self.specs.get(&key) {
            return *f;
        }
        let info = &self.fns[fid];
        let args: Vec<GArg> = ct.iter().map(|(_, t)| GArg::Ty(t.clone())).collect();
        let map: SubstMap<'_> = ct.iter().map(|(s, _)| s.id).zip(args.iter()).collect();
        let scheme = Scheme {
            tparams: info.scheme.tparams.iter().filter(|g| !g.comptime).cloned().collect(),
            params: info.scheme.params.iter().map(|(n, t)| (n.clone(), subst(t, &map))).collect(),
            ret: subst(&info.scheme.ret, &map),
            effects: info.scheme.effects.as_ref().map(|e| subst_effs(e, &map)),
            ret_from: info.scheme.ret_from.clone(),
        };
        let spec = FnInfo { scheme, has_body: true, iface: None, name: info.name.clone(), decl: info.decl, ..*info };
        let module = spec.module;
        let id = self.fns.len();
        self.fns.push(spec);
        self.specs.insert(key, id);
        self.spec_of.insert(id, fid);
        let shown: Vec<String> = ct.iter().map(|(_, t)| format!("{}", super::types::Show(t, &*self))).collect();
        let mut note = format!("in `{}` for `{}`", self.fns[fid].name, shown.join(", "));
        // The specialization that needed this one, and so on, three deep at most.
        if let Some(outer) = &self.note {
            let chain: Vec<&str> = outer.split(", from ").take(2).collect();
            note = format!("{note}, from {}", chain.join(", from ").trim_start_matches("in "));
        }
        self.spec_notes.insert(id, note.clone());
        if let Some(d) = requested {
            self.spec_requested.insert(id, d);
        }
        // Errors found while expanding the body belong to this specialization too.
        let saved = self.note.replace(note);
        if let Some(mut decl) = self.fn_decl(fid) {
            let env = ct.iter().map(|(s, t)| (s.name.clone(), CV::Type(t.clone()))).collect();
            decl.body = decl.body.as_ref().and_then(|b| Expand::new(self, module, requested, env).body(b));
            self.bodies.insert(id, decl);
        }
        self.note = saved;
        id
    }
}

pub fn spec_key(ct: &[(Sym, Ty)]) -> String {
    format!("{:?}", ct.iter().map(|(_, t)| t).collect::<Vec<_>>())
}

pub fn contains_params(t: &Ty) -> bool {
    match t {
        Ty::Param(_) | Ty::Var(_) => true,
        Ty::Named(_, args) => args.iter().any(|a| matches!(a, GArg::Ty(t) if contains_params(t))),
        Ty::Tuple(ts) => ts.iter().any(contains_params),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(contains_params),
        Ty::Array(e, _) | Ty::Slice(e) | Ty::Borrow(_, e) => contains_params(e),
        _ => false,
    }
}

pub fn param_arg(g: &GParam) -> GArg {
    match g.kind {
        PKind::Type => GArg::Ty(Ty::Param(g.sym.clone())),
        PKind::Region => GArg::Region(Region::Param(g.sym.clone())),
        PKind::Row => GArg::Row(EffRow { effs: Vec::new(), tail: Tail::Param(g.sym.clone()) }),
        PKind::Len => GArg::Len(Len::Param(g.sym.clone())),
    }
}

fn strip_borrows(t: &Ty) -> &Ty {
    match t {
        Ty::Borrow(_, inner) => strip_borrows(inner),
        t => t,
    }
}

/// One-way matching of an impl's target against a concrete type, binding the impl's parameters.
pub fn match_ty(pat: &Ty, ty: &Ty, vars: &[u32], binds: &mut Binds) -> bool {
    match (pat, ty) {
        (Ty::Param(s), _) if vars.contains(&s.id) => match binds.get(&s.id) {
            Some(GArg::Ty(prev)) => prev == ty,
            _ => {
                binds.insert(s.id, GArg::Ty(ty.clone()));
                true
            }
        },
        (Ty::Named(a, xs), Ty::Named(b, ys)) => a == b && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| match_arg(x, y, vars, binds)),
        (Ty::Tuple(xs), Ty::Tuple(ys)) => xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| match_ty(x, y, vars, binds)),
        (Ty::Record(a), Ty::Record(b)) | (Ty::Union(a), Ty::Union(b)) => {
            a.labels.len() == b.labels.len()
                && a.labels.iter().zip(&b.labels).all(|((k1, x), (k2, y))| k1 == k2 && match_ty(x, y, vars, binds))
        }
        (Ty::Array(x, _), Ty::Array(y, _)) | (Ty::Slice(x), Ty::Slice(y)) => match_ty(x, y, vars, binds),
        (Ty::Borrow(m1, x), Ty::Borrow(m2, y)) => m1 == m2 && match_ty(x, y, vars, binds),
        _ => pat == ty,
    }
}

fn match_arg(pat: &GArg, arg: &GArg, vars: &[u32], binds: &mut Binds) -> bool {
    match (pat, arg) {
        (GArg::Ty(p), GArg::Ty(t)) => match_ty(p, t, vars, binds),
        (GArg::Region(Region::Param(s)), a) | (GArg::Len(Len::Param(s)), a) if vars.contains(&s.id) => {
            binds.insert(s.id, a.clone());
            true
        }
        (GArg::Row(r), a) => {
            if let Tail::Param(s) = &r.tail
                && vars.contains(&s.id) {
                    binds.insert(s.id, a.clone());
                }
            true
        }
        _ => true,
    }
}
