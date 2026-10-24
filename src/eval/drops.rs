//! Destructors (§5.6). A binding's value is dropped when its block ends, unless it was moved
//! out: the ownership pass records each move (`Typed::moves`), and the evaluator keeps a drop
//! flag per binding and field path. Dropping a value runs its type's `Drop.drop`, then drops its
//! parts — fields, payloads, elements — skipping parts that were moved out.

use std::collections::HashSet;
use std::sync::Arc;

use super::interp::{Ctl, Interp, TEnv, end_program, is_panic};
use super::value::*;
use crate::check::env::{DefKind, Program, SubstMap, subst_params};
use crate::check::types::*;

/// Whether dropping a value of type `t` can run any code.
pub fn needs_drop(p: &Program, t: &Ty) -> bool {
    needs(p, t, false, &mut HashSet::new())
}

// `params` decides a type parameter: whether it may stand for a type that needs dropping.
fn needs(p: &Program, t: &Ty, params: bool, seen: &mut HashSet<DefId>) -> bool {
    match t {
        Ty::Named(d, args) => {
            // A continuation's body has cleanup to run when it is dropped (§5.3).
            if p.has_drop(*d) || p.known.get("Cont") == Some(d) {
                return true;
            }
            if !seen.insert(*d) {
                return false;
            }
            let arg_needs = args.iter().any(|a| matches!(a, GArg::Ty(t) if needs(p, t, params, seen)));
            let parts = match &p.defs[*d].kind {
                DefKind::Struct { .. } => p.struct_fields(*d, args).unwrap_or_default().into_iter().map(|(_, t)| t).collect(),
                DefKind::Enum { tags } => tags.values().map(|t| subst_params(t, &p.defs[*d].params, args)).collect(),
                _ => Vec::new(),
            };
            arg_needs || parts.iter().any(|t| needs(p, t, params, seen))
        }
        Ty::Tuple(ts) => ts.iter().any(|t| needs(p, t, params, seen)),
        Ty::Record(r) | Ty::Union(r) => r.labels.values().any(|t| needs(p, t, params, seen)),
        Ty::Array(e, _) => needs(p, e, params, seen),
        Ty::Param(_) => params,
        _ => false,
    }
}

/// A destructor does not unwind (§5.7): a panic that escapes one — a `Drop` impl, or the cleanup
/// of a continuation a value's dropping unwinds — ends the program, for dropping a value halfway
/// would leave the rest of it undropped.
fn destructor(r: Result<(), Ctl>) -> Result<(), Ctl> {
    match r {
        Err(Ctl::Panic(m)) if is_panic(&Err(Ctl::Panic(m.clone()))) => Err(end_program(format!("{m}, in a destructor"))),
        other => other,
    }
}

impl Interp {
    /// `needs_drop`, deciding most nominal types from a fact kept per definition.
    pub fn needs_drop(&self, t: &Ty) -> bool {
        match t {
            Ty::Named(d, _) => match self.may_drop(*d) {
                false => false,
                true if self.prog.defs[*d].params.is_empty() => true,
                true => needs_drop(&self.prog, t),
            },
            Ty::Tuple(ts) => ts.iter().any(|t| self.needs_drop(t)),
            Ty::Record(r) | Ty::Union(r) => r.labels.values().any(|t| self.needs_drop(t)),
            Ty::Array(e, _) => self.needs_drop(e),
            _ => false,
        }
    }

    /// Whether some arguments make the definition `d` need dropping: whether it, or a part of it,
    /// implements Drop or is a type parameter. A template's parts depend on its arguments.
    fn may_drop(&self, d: DefId) -> bool {
        if let Some(&b) = self.memo.drop_shapes.lock().expect("drop shapes").get(&d) {
            return b;
        }
        let b = self.prog.defs[d].template_fields.is_some() || needs(&self.prog, &Ty::Named(d, Vec::new()), true, &mut HashSet::new());
        self.memo.drop_shapes.lock().expect("drop shapes").insert(d, b);
        b
    }

    /// Drops `v`, of type `ty`, except the field paths in `moved`.
    pub fn drop_value(&mut self, v: Value, ty: &Ty, moved: &[Vec<String>]) -> Result<(), Ctl> {
        if moved.iter().any(|m| m.is_empty()) || matches!(v, Value::Ptr(_)) || !self.needs_drop(ty) {
            return Ok(());
        }
        let below = |name: &str| -> Vec<Vec<String>> {
            moved.iter().filter(|m| m.first().is_some_and(|f| f == name)).map(|m| m[1..].to_vec()).collect()
        };
        match ty {
            Ty::Named(d, _) if self.prog.known.get("Cont") == Some(d) => {
                if let Value::Native("Cont", co) = v.deref() {
                    destructor(super::coroutine::drop_cont(self, co))?;
                }
                Ok(())
            }
            Ty::Named(d, args) => {
                // The type's own destructor first, then its parts.
                if let Some(f) = self.prog.drop_method(*d) {
                    let place = Place { root: shared(v.clone()), path: Vec::new() };
                    let params = &self.prog.fns[f].scheme.tparams;
                    let tenv: TEnv = std::sync::Arc::new(params.iter().zip(args).map(|(g, a)| (g.sym.id, a.clone())).collect());
                    destructor(self.call_fn_with(f, vec![Value::Ptr(place)], tenv).map(|_| ()))?;
                }
                let def_kind = &self.prog.defs[*d].kind;
                match (def_kind, v.deref()) {
                    (DefKind::Struct { .. }, Value::Record(fs)) => {
                        for (name, fty) in self.prog.struct_fields(*d, args).unwrap_or_default() {
                            if let Some(fv) = fs.get(&name) {
                                self.drop_value(fv.clone(), &fty, &below(&name))?;
                            }
                        }
                    }
                    (DefKind::Enum { tags }, Value::Tag(t, payload)) => {
                        if let Some(pt) = tags.get(&*t) {
                            let pt = subst_params(pt, &self.prog.defs[*d].params, args);
                            self.drop_payload(*payload, &pt)?;
                        }
                    }
                    _ => {
                        // A library container: drop what it holds.
                        if let (Some(GArg::Ty(elem)), Value::List(items)) = (args.first(), v.deref()) {
                            for item in Arc::unwrap_or_clone(items) {
                                self.drop_value(item, elem, &[])?;
                            }
                        }
                    }
                }
                Ok(())
            }
            Ty::Tuple(ts) => {
                if let Value::Tuple(vs) | Value::List(vs) = v.deref() {
                    for (i, (x, t)) in Arc::unwrap_or_clone(vs).into_iter().zip(ts).enumerate() {
                        self.drop_value(x, t, &below(&i.to_string()))?;
                    }
                }
                Ok(())
            }
            Ty::Record(r) => {
                if let Value::Record(fs) = v.deref() {
                    for (name, t) in &r.labels {
                        if let Some(x) = fs.get(name) {
                            self.drop_value(x.clone(), t, &below(name))?;
                        }
                    }
                }
                Ok(())
            }
            Ty::Union(r) => {
                if let Value::Tag(t, payload) = v.deref()
                    && let Some(pt) = r.labels.get(&*t) {
                        return self.drop_payload(*payload, pt);
                    }
                Ok(())
            }
            Ty::Array(e, _) => {
                if let Value::List(vs) = v.deref() {
                    for x in Arc::unwrap_or_clone(vs) {
                        self.drop_value(x, e, &[])?;
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn drop_payload(&mut self, payload: Value, pt: &Ty) -> Result<(), Ctl> {
        match (pt, payload) {
            (Ty::Tuple(ts), Value::Tuple(vs)) => {
                for (x, t) in Arc::unwrap_or_clone(vs).into_iter().zip(ts) {
                    self.drop_value(x, t, &[])?;
                }
                Ok(())
            }
            (t, v) => self.drop_value(v, t, &[]),
        }
    }

    /// A type in this frame's terms, for a binding's static type.
    pub fn frame_ty(&self, t: &Ty) -> Ty {
        let map: SubstMap<'_> = self.lex.tenv.iter().map(|(k, v)| (*k, v)).collect();
        crate::check::env::subst(t, &map)
    }
}
