//! Interfaces as bounds (§3.4): calling a method through a bound, choosing the impl for a type,
//! and checking that a type satisfies a bound.

use std::collections::HashMap;

use super::env::{DeclRef, DefKind, FnId, FnInfo, GParam, PKind, Program, Scheme, subst_params};
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
            let mut tparams = vec![GParam { sym: self_sym.clone(), kind: PKind::Type, bounds: vec![bound.clone()], default: None }];
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
        for (i, imp) in self.impls.iter().enumerate() {
            if imp.interface.as_ref().map(|(d, _)| *d) != Some(iface) {
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
            if ok {
                return Some((i, binds));
            }
        }
        None
    }

    /// Whether `ty` satisfies `bound`, where `assumed` gives the bounds of type parameters in scope.
    pub fn satisfies(&self, ty: &Ty, bound: &Ty, assumed: &dyn Fn(u32) -> Vec<Ty>) -> bool {
        self.satisfies_depth(ty, bound, assumed, 0)
    }

    fn satisfies_depth(&self, ty: &Ty, bound: &Ty, assumed: &dyn Fn(u32) -> Vec<Ty>, depth: usize) -> bool {
        let Ty::Named(d, _) = bound else { return true };
        let send_params: Vec<u32> = match ty {
            Ty::Param(s) if assumed(s.id).iter().any(|b| matches!(b, Ty::Named(x, _) if self.known.get("Send") == Some(x))) => vec![s.id],
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
            // Derived for every type built from parts that have them (§3.5).
            "Eq" | "Hash" | "Show" | "Clone" if self.is_std_def(*d) && !matches!(strip_borrows(ty), Ty::Param(_)) => {
                return !matches!(strip_borrows(ty), Ty::Fn(_));
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
