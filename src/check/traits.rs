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

    /// The `drop` method of the nominal type `d`'s `Drop` implementation.
    pub fn drop_method(&self, d: DefId) -> Option<super::env::FnId> {
        self.impls
            .iter()
            .find(|imp| matches!(&imp.target, Ty::Named(t, _) if *t == d) && imp.interface.as_ref().is_some_and(|(i, _)| self.defs[*i].name == "Drop"))
            .and_then(|imp| imp.methods.iter().copied().find(|f| self.fns[*f].name == "drop"))
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
        self.copy_in(t, &[], &mut Vec::new())
    }

    /// `Copy` in generic code, where the type parameters `copies` are bounded by it.
    pub fn is_copy_given(&self, t: &Ty, copies: &[u32]) -> bool {
        self.copy_in(t, copies, &mut Vec::new())
    }

    // Each walk below keeps the nominal types it has visited: recursion goes through them (§3.3).
    // Each property is an `all`, `any` or `max` over every type reachable from the one asked
    // about, so meeting a visited type again — on a cycle, or on another path to it — adds
    // nothing, and is decided as the property's neutral value. Keeping only the current path
    // instead would revisit a type once per path to it: exponential in mutually recursive types.
    fn copy_in(&self, t: &Ty, copies: &[u32], inside: &mut Vec<Ty>) -> bool {
        match t {
            Ty::Prim(_) => true,
            Ty::Borrow(m, _) => !m,
            Ty::Tuple(ts) => ts.iter().all(|t| self.copy_in(t, copies, inside)),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().all(|t| self.copy_in(t, copies, inside)),
            Ty::Array(e, _) => self.copy_in(e, copies, inside),
            Ty::Slice(_) => true,
            Ty::Named(d, args) => {
                // Region references and region handles are `Copy` (§4.6), as is a raw pointer (§8.2).
                if self.is_known(*d, "Ref") || self.is_known(*d, "Ptr") || self.def_named(*d, &["Cell", "RegionList"]) {
                    return true;
                }
                if self.has_drop(*d) {
                    return false;
                }
                if inside.contains(t) {
                    return true;
                }
                inside.push(t.clone());
                match self.components(*d, args) {
                    Some(cs) => cs.iter().all(|c| self.copy_in(c, copies, inside)),
                    // Opaque library types own resources unless declared otherwise.
                    None => self.def_named(*d, &["Hasher"]),
                }
            }
            Ty::Param(s) => copies.contains(&s.id),
            Ty::Var(_) | Ty::Fn(_) | Ty::Assoc(..) => false,
            Ty::Error => true,
        }
    }

    /// The class of a type: 2 if it contains a borrow, anywhere (§4.2).
    pub fn class(&self, t: &Ty) -> u8 {
        self.class_in(t, &mut Vec::new())
    }

    fn class_in(&self, t: &Ty, inside: &mut Vec<Ty>) -> u8 {
        match t {
            Ty::Borrow(..) | Ty::Slice(_) | Ty::Prim(Prim::Str) => 2,
            Ty::Tuple(ts) => ts.iter().map(|t| self.class_in(t, inside)).max().unwrap_or(1),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().map(|t| self.class_in(t, inside)).max().unwrap_or(1),
            Ty::Array(e, _) => self.class_in(e, inside),
            // A region reference points into its region, not at a loan: it is class 1 whatever it
            // points to (§4.6).
            // A raw pointer is an address, not a loan, whatever it points to (§8.2).
            Ty::Named(d, _) if self.is_known(*d, "Ref") || self.is_known(*d, "Ptr") => 1,
            Ty::Named(d, args) => {
                if inside.contains(t) {
                    return 1;
                }
                inside.push(t.clone());
                let mut c = Self::arg_types(args).map(|a| self.class_in(a, inside)).max().unwrap_or(1);
                if c < 2 {
                    c = c.max(self.components(*d, args).map_or(1, |cs| cs.iter().map(|x| self.class_in(x, inside)).max().unwrap_or(1)));
                }
                c
            }
            Ty::Fn(_) => 1,
            // `C.Slice` may be a borrow until `C` is known (§4.2).
            Ty::Assoc(..) => 2,
            _ => 1,
        }
    }

    /// A borrow held by a nominal type that is not a `view` (§4.2): `Vec<str>`. Containers
    /// release what they hold on every change, so their type parameters range over class-1 types.
    pub fn borrow_in_container(&self, t: &Ty) -> Option<(DefId, Ty)> {
        self.container_in(t, &mut Vec::new())
    }

    fn container_in(&self, t: &Ty, inside: &mut Vec<Ty>) -> Option<(DefId, Ty)> {
        match t {
            Ty::Borrow(_, e) | Ty::Slice(e) | Ty::Array(e, _) => self.container_in(e, inside),
            Ty::Tuple(ts) => ts.iter().find_map(|t| self.container_in(t, inside)),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().find_map(|t| self.container_in(t, inside)),
            Ty::Fn(f) => f.params.iter().chain(std::iter::once(&f.ret)).find_map(|t| self.container_in(t, inside)),
            Ty::Named(d, args) => {
                // A region reference is class 1 whatever it points at (§4.6).
                if !self.defs[*d].view && !self.is_known(*d, "Ref") && !self.is_known(*d, "Ptr")
                    && let Some(a) = Self::arg_types(args).find(|a| self.class(a) == 2) {
                        return Some((*d, a.clone()));
                    }
                if inside.contains(t) {
                    return None;
                }
                inside.push(t.clone());
                Self::arg_types(args).find_map(|a| self.container_in(a, inside))
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
        self.class(t) == 1 && self.send_in(t, send_params, &mut Vec::new())
    }

    fn send_in(&self, t: &Ty, send_params: &[u32], inside: &mut Vec<Ty>) -> bool {
        match t {
            Ty::Prim(_) | Ty::Error => true,
            Ty::Tuple(ts) => ts.iter().all(|t| self.send_in(t, send_params, inside)),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().all(|t| self.send_in(t, send_params, inside)),
            Ty::Array(e, _) | Ty::Slice(e) | Ty::Borrow(_, e) => self.send_in(e, send_params, inside),
            Ty::Named(d, args) => {
                // Outer regions are frozen while tasks run (§6.1), so region data is always
                // shareable; the runtime's own handles are not.
                if self.def_named(*d, &["Gen", "Fiber", "Scope", "Cont"]) || self.is_known(*d, "Ptr") {
                    return false;
                }
                if inside.contains(t) {
                    return true;
                }
                inside.push(t.clone());
                Self::arg_types(args).all(|a| self.send_in(a, send_params, inside))
                    && self.components(*d, args).is_none_or(|cs| cs.iter().all(|c| self.send_in(c, send_params, inside)))
            }
            // An escaping closure owns only `Send` values, and a lent one carries loans that keep
            // it from crossing to a task (§4.3), so every function value is `Send`.
            Ty::Fn(_) => true,
            Ty::Param(sym) => send_params.contains(&sym.id),
            Ty::Var(_) | Ty::Assoc(..) => false,
        }
    }
}
