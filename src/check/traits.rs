//! Structural properties of types: `Copy`, class (§4.2) and `Send` (§4.4).

use super::env::{DefKind, Program};
use super::types::*;

impl Program {
    fn is_known(&self, d: DefId, name: &str) -> bool {
        self.known.get(name) == Some(&d)
    }

    fn def_named(&self, d: DefId, names: &[&str]) -> bool {
        names.contains(&self.defs[d].name.as_str()) && self.modules[self.defs[d].module].is_std
    }

    /// Whether the nominal type `d` has a `Drop` implementation.
    pub fn has_drop(&self, d: DefId) -> bool {
        self.impls.iter().any(|imp| {
            matches!(&imp.target, Ty::Named(t, _) if *t == d)
                && imp.interface.as_ref().is_some_and(|(i, _)| self.defs[*i].name == "Drop")
        })
    }

    /// The fields of a nominal struct, or the payloads of an enum, with arguments substituted.
    fn components(&self, d: DefId, args: &[GArg]) -> Option<Vec<Ty>> {
        let params = &self.defs[d].params;
        match &self.defs[d].kind {
            DefKind::Struct { fields: Some(_) } => Some(self.struct_fields(d, args)?.into_iter().map(|(_, t)| t).collect()),
            DefKind::Enum { tags } => Some(tags.values().map(|t| super::env::subst_params(t, params, args)).collect()),
            _ => None,
        }
    }

    fn arg_types(args: &[GArg]) -> impl Iterator<Item = &Ty> {
        args.iter().filter_map(|a| match a {
            GArg::Ty(t) => Some(t),
            _ => None,
        })
    }

    /// `Copy`: copying the bits is the whole meaning of a copy (§4.4). Expects a zonked type.
    pub fn is_copy(&self, t: &Ty) -> bool {
        self.copy_depth(t, 0)
    }

    fn copy_depth(&self, t: &Ty, depth: usize) -> bool {
        if depth > 32 {
            return false;
        }
        let rec = |t: &Ty| self.copy_depth(t, depth + 1);
        match t {
            Ty::Prim(_) => true,
            Ty::Borrow(m, _) => !m,
            Ty::Tuple(ts) => ts.iter().all(rec),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().all(rec),
            Ty::Array(e, _) => rec(e),
            Ty::Slice(_) => true,
            Ty::Named(d, args) => {
                // Region references and region handles are `Copy` (§4.6).
                if self.is_known(*d, "Ref") || self.def_named(*d, &["Cell", "RegionList"]) {
                    return true;
                }
                if self.has_drop(*d) {
                    return false;
                }
                match self.components(*d, args) {
                    Some(cs) => cs.iter().all(rec),
                    // Opaque library types own resources unless declared otherwise.
                    None => self.def_named(*d, &["Hasher"]),
                }
            }
            Ty::Param(_) | Ty::Var(_) | Ty::Fn(_) | Ty::Assoc(..) => false,
            Ty::Error => true,
        }
    }

    /// The class of a type: 2 if it contains a borrow, anywhere (§4.2).
    pub fn class(&self, t: &Ty) -> u8 {
        self.class_depth(t, 0)
    }

    fn class_depth(&self, t: &Ty, depth: usize) -> u8 {
        if depth > 32 {
            return 1;
        }
        let rec = |t: &Ty| self.class_depth(t, depth + 1);
        match t {
            Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str) => 2,
            Ty::Tuple(ts) => ts.iter().map(rec).max().unwrap_or(1),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().map(rec).max().unwrap_or(1),
            Ty::Array(e, _) => rec(e),
            // A region reference points into its region, not at a loan: it is class 1 whatever it
            // points to (§4.6).
            Ty::Named(d, _) if self.is_known(*d, "Ref") => 1,
            Ty::Named(d, args) => {
                let from_args = Self::arg_types(args).map(rec).max().unwrap_or(1);
                let from_fields = self.components(*d, args).map_or(1, |cs| cs.iter().map(rec).max().unwrap_or(1));
                from_args.max(from_fields)
            }
            Ty::Fn(f) => f.params.iter().chain(std::iter::once(&f.ret)).map(|_| 1).max().unwrap_or(1),
            // `C.Slice` may be a borrow until `C` is known (§4.2).
            Ty::Assoc(..) => 2,
            _ => 1,
        }
    }

    /// A borrow held by a nominal type that is not a `view` (§4.2): `Vec<str>`. Containers
    /// release what they hold on every change, so their type parameters range over class-1 types.
    pub fn borrow_in_container(&self, t: &Ty) -> Option<(DefId, Ty)> {
        self.container_depth(t, 0)
    }

    fn container_depth(&self, t: &Ty, depth: usize) -> Option<(DefId, Ty)> {
        if depth > 32 {
            return None;
        }
        let rec = |t: &Ty| self.container_depth(t, depth + 1);
        match t {
            Ty::Borrow(_, e) | Ty::Slice(e) | Ty::Array(e, _) => rec(e),
            Ty::Tuple(ts) => ts.iter().find_map(rec),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().find_map(rec),
            Ty::Fn(f) => f.params.iter().chain(std::iter::once(&f.ret)).find_map(rec),
            Ty::Named(d, args) => {
                // A region reference is class 1 whatever it points at (§4.6).
                if !self.defs[*d].view && !self.is_known(*d, "Ref")
                    && let Some(a) = Self::arg_types(args).find(|a| self.class(a) == 2) {
                        return Some((*d, a.clone()));
                    }
                Self::arg_types(args).find_map(rec)
            }
            _ => None,
        }
    }

    /// `Send`: may move to another task, and `readonly T` may be shared with one (§4.4).
    pub fn is_send(&self, t: &Ty) -> bool {
        self.is_send_given(t, &[])
    }

    /// `Send`, given type parameters declared `extends Send` (by symbol id).
    pub fn is_send_given(&self, t: &Ty, send_params: &[u32]) -> bool {
        self.class(t) == 1 && self.send_depth(t, send_params, 0)
    }

    fn send_depth(&self, t: &Ty, send_params: &[u32], depth: usize) -> bool {
        if depth > 32 {
            return false;
        }
        let rec = |t: &Ty| self.send_depth(t, send_params, depth + 1);
        match t {
            Ty::Prim(_) | Ty::Error => true,
            Ty::Tuple(ts) => ts.iter().all(rec),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().all(rec),
            Ty::Array(e, _) | Ty::Slice(e) | Ty::Borrow(_, e) => rec(e),
            Ty::Named(d, args) => {
                // Outer regions are frozen while tasks run (§6.1), so region data is always
                // shareable; the runtime's own handles are not.
                if self.def_named(*d, &["Gen", "Fiber", "Scope"]) {
                    return false;
                }
                Self::arg_types(args).all(rec) && self.components(*d, args).is_none_or(|cs| cs.iter().all(rec))
            }
            // An escaping closure owns only `Send` values, and a lent one carries loans that keep
            // it from crossing to a task (§4.3), so every function value is `Send`.
            Ty::Fn(_) => true,
            Ty::Param(sym) => send_params.contains(&sym.id),
            Ty::Var(_) | Ty::Assoc(..) => false,
        }
    }
}
