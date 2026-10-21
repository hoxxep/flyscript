//! Inference variables and unification.
//!
//! Records and tag unions use Rémy-style row unification. Effect rows are sets (§3.2): a
//! body's effects are checked by *subsumption* into an allowed row, where region arguments are
//! part of an effect's label and its other arguments unify, and `Fail` payloads (tag unions)
//! are compared by inclusion so error sets compose by union.

use std::collections::BTreeMap;

use super::types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VarKind {
    Any,
    Int,
    Float,
}

#[derive(Clone, Default)]
pub struct Subst {
    tys: Vec<(Option<Ty>, VarKindSlot)>,
    rows: Vec<Option<Row>>,
    effs: Vec<Option<EffRow>>,
    regions: Vec<Option<Region>>,
    lens: Vec<Option<Len>>,
}

#[derive(Clone, Copy, Debug)]
struct VarKindSlot(VarKind);

impl Default for VarKindSlot {
    fn default() -> Self {
        VarKindSlot(VarKind::Any)
    }
}

/// Unification failed; the caller reports the types it was comparing.
#[derive(Debug)]
pub struct Mismatch;

pub type UResult = Result<(), Mismatch>;

impl Subst {
    pub fn snapshot(&self) -> Subst {
        self.clone()
    }

    pub fn restore(&mut self, s: Subst) {
        *self = s;
    }

    // ---- fresh variables ----

    pub fn fresh(&mut self) -> Ty {
        self.fresh_kind(VarKind::Any)
    }

    pub fn fresh_kind(&mut self, kind: VarKind) -> Ty {
        self.tys.push((None, VarKindSlot(kind)));
        Ty::Var(self.tys.len() as u32 - 1)
    }

    pub fn fresh_row_tail(&mut self) -> Tail {
        self.rows.push(None);
        Tail::Var(self.rows.len() as u32 - 1)
    }

    pub fn fresh_eff_tail(&mut self) -> Tail {
        self.effs.push(None);
        Tail::Var(self.effs.len() as u32 - 1)
    }

    pub fn fresh_effs(&mut self) -> EffRow {
        EffRow { effs: Vec::new(), tail: self.fresh_eff_tail() }
    }

    pub fn fresh_region(&mut self) -> Region {
        self.regions.push(None);
        Region::Var(self.regions.len() as u32 - 1)
    }

    pub fn fresh_len(&mut self) -> Len {
        self.lens.push(None);
        Len::Var(self.lens.len() as u32 - 1)
    }

    pub fn kind(&self, v: u32) -> VarKind {
        self.tys[v as usize].1.0
    }

    // ---- resolution ----

    /// Follows variable bindings at the top of a type.
    pub fn resolve(&self, t: &Ty) -> Ty {
        let mut t = t.clone();
        while let Ty::Var(v) = t {
            match &self.tys[v as usize].0 {
                Some(b) => t = b.clone(),
                None => return t,
            }
        }
        t
    }

    pub fn resolve_region(&self, r: &Region) -> Region {
        let mut r = r.clone();
        while let Region::Var(v) = r {
            match &self.regions[v as usize] {
                Some(b) => r = b.clone(),
                None => return r,
            }
        }
        r
    }

    pub fn resolve_len(&self, l: &Len) -> Len {
        let mut l = l.clone();
        while let Len::Var(v) = l {
            match &self.lens[v as usize] {
                Some(b) => l = b.clone(),
                None => return l,
            }
        }
        l
    }

    /// A row with every bound tail variable folded in.
    pub fn expand_row(&self, r: &Row) -> Row {
        let mut labels = r.labels.clone();
        let mut tail = r.tail.clone();
        while let Tail::Var(v) = tail {
            match &self.rows[v as usize] {
                Some(b) => {
                    for (k, t) in &b.labels {
                        labels.insert(k.clone(), t.clone());
                    }
                    tail = b.tail.clone();
                }
                None => break,
            }
        }
        Row { labels, tail }
    }

    pub fn expand_effs(&self, r: &EffRow) -> EffRow {
        let mut effs = r.effs.clone();
        let mut tail = r.tail.clone();
        while let Tail::Var(v) = tail {
            match &self.effs[v as usize] {
                Some(b) => {
                    effs.extend(b.effs.iter().cloned());
                    tail = b.tail.clone();
                }
                None => break,
            }
        }
        EffRow { effs, tail }
    }

    /// Fully resolves a type, for printing and for final checks.
    pub fn zonk(&self, t: &Ty) -> Ty {
        match self.resolve(t) {
            Ty::Named(d, args) => Ty::Named(d, args.iter().map(|a| self.zonk_arg(a)).collect()),
            Ty::Record(r) => Ty::Record(self.zonk_row(&r)),
            Ty::Union(r) => Ty::Union(self.zonk_row(&r)),
            Ty::Tuple(ts) => match ts.iter().map(|t| self.zonk(t)).collect::<Vec<_>>() {
                ts if ts.len() == 1 && ts[0] == Ty::void() => Ty::void(),
                ts => Ty::Tuple(ts),
            },
            Ty::Array(t, l) => Ty::Array(Box::new(self.zonk(&t)), self.resolve_len(&l)),
            Ty::Slice(t) => Ty::Slice(Box::new(self.zonk(&t))),
            Ty::Borrow(m, t) => Ty::Borrow(m, Box::new(self.zonk(&t))),
            Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
                mode: f.mode,
                params: f.params.iter().map(|t| self.zonk(t)).collect(),
                ret: self.zonk(&f.ret),
                effects: self.zonk_effs(&f.effects),
            })),
            Ty::Assoc(t, n) => Ty::Assoc(Box::new(self.zonk(&t)), n),
            t => t,
        }
    }

    pub fn zonk_arg(&self, a: &GArg) -> GArg {
        match a {
            GArg::Ty(t) => GArg::Ty(self.zonk(t)),
            GArg::Region(r) => GArg::Region(self.resolve_region(r)),
            GArg::Row(r) => GArg::Row(self.zonk_effs(r)),
            GArg::Len(l) => GArg::Len(self.resolve_len(l)),
        }
    }

    pub fn zonk_row(&self, r: &Row) -> Row {
        let r = self.expand_row(r);
        Row { labels: r.labels.iter().map(|(k, t)| (k.clone(), self.zonk(t))).collect(), tail: r.tail }
    }

    pub fn zonk_effs(&self, r: &EffRow) -> EffRow {
        let r = self.expand_effs(r);
        EffRow {
            effs: r
                .effs
                .iter()
                .map(|e| Eff {
                    def: e.def,
                    regions: e.regions.iter().map(|r| self.resolve_region(r)).collect(),
                    args: e.args.iter().map(|t| self.zonk(t)).collect(),
                })
                .collect(),
            tail: r.tail,
        }
    }

    // ---- binding ----

    fn occurs(&self, v: u32, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Var(w) => w == v,
            Ty::Named(_, args) => args.iter().any(|a| matches!(a, GArg::Ty(t) if self.occurs(v, t))),
            Ty::Record(r) | Ty::Union(r) => self.expand_row(&r).labels.values().any(|t| self.occurs(v, t)),
            Ty::Tuple(ts) => ts.iter().any(|t| self.occurs(v, t)),
            Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) | Ty::Assoc(t, _) => self.occurs(v, &t),
            Ty::Fn(f) => f.params.iter().any(|t| self.occurs(v, t)) || self.occurs(v, &f.ret),
            _ => false,
        }
    }

    fn bind_ty(&mut self, v: u32, t: Ty) -> UResult {
        if let Ty::Var(w) = t {
            if w == v {
                return Ok(());
            }
            let (a, b) = (self.kind(v), self.kind(w));
            let merged = match (a, b) {
                (VarKind::Any, k) | (k, VarKind::Any) => k,
                (x, y) if x == y => x,
                _ => return Err(Mismatch),
            };
            self.tys[w as usize].1 = VarKindSlot(merged);
            self.tys[v as usize].0 = Some(Ty::Var(w));
            return Ok(());
        }
        match (self.kind(v), &t) {
            (VarKind::Any, _) => {}
            (VarKind::Int, Ty::Prim(p)) if p.is_int() => {}
            (VarKind::Float, Ty::Prim(p)) if p.is_float() => {}
            (_, Ty::Error) => {}
            _ => return Err(Mismatch),
        }
        if self.occurs(v, &t) {
            return Err(Mismatch);
        }
        self.tys[v as usize].0 = Some(t);
        Ok(())
    }

    // ---- unification ----

    pub fn unify(&mut self, a: &Ty, b: &Ty) -> UResult {
        let (a, b) = (self.resolve(a), self.resolve(b));
        match (&a, &b) {
            (Ty::Error, _) | (_, Ty::Error) => Ok(()),
            (Ty::Prim(Prim::Never), _) | (_, Ty::Prim(Prim::Never)) => Ok(()),
            (Ty::Var(v), _) => self.bind_ty(*v, b.clone()),
            (_, Ty::Var(v)) => self.bind_ty(*v, a.clone()),
            // A payload of one `void` is no payload: `#Ok` is a `Result<void, E>`'s `#Ok`.
            (Ty::Tuple(ts), v) | (v, Ty::Tuple(ts)) if ts.len() == 1 && *v == Ty::void() => self.unify(&ts[0], v),
            (Ty::Param(x), Ty::Param(y)) if x == y => Ok(()),
            (Ty::Prim(x), Ty::Prim(y)) if x == y => Ok(()),
            (Ty::Named(d1, a1), Ty::Named(d2, a2)) if d1 == d2 && a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(a2) {
                    self.unify_arg(x, y)?;
                }
                Ok(())
            }
            (Ty::Record(r1), Ty::Record(r2)) | (Ty::Union(r1), Ty::Union(r2)) => self.unify_rows(r1, r2),
            (Ty::Tuple(t1), Ty::Tuple(t2)) if t1.len() == t2.len() => {
                for (x, y) in t1.iter().zip(t2) {
                    self.unify(x, y)?;
                }
                Ok(())
            }
            (Ty::Array(t1, l1), Ty::Array(t2, l2)) => {
                self.unify(t1, t2)?;
                self.unify_len(l1, l2)
            }
            (Ty::Slice(t1), Ty::Slice(t2)) => self.unify(t1, t2),
            (Ty::Borrow(m1, t1), Ty::Borrow(m2, t2)) if m1 == m2 => self.unify(t1, t2),
            (Ty::Fn(f1), Ty::Fn(f2)) if f1.params.len() == f2.params.len() => {
                for (x, y) in f1.params.iter().zip(&f2.params) {
                    self.unify(x, y)?;
                }
                self.unify(&f1.ret, &f2.ret)?;
                self.eff_sub(&f1.effects, &f2.effects).map_err(|_| Mismatch)?;
                self.eff_sub(&f2.effects, &f1.effects).map_err(|_| Mismatch)
            }
            (Ty::Assoc(t1, n1), Ty::Assoc(t2, n2)) if n1 == n2 => self.unify(t1, t2),
            _ => Err(Mismatch),
        }
    }

    pub fn unify_arg(&mut self, a: &GArg, b: &GArg) -> UResult {
        match (a, b) {
            (GArg::Ty(x), GArg::Ty(y)) => self.unify(x, y),
            (GArg::Region(x), GArg::Region(y)) => self.unify_region(x, y),
            (GArg::Row(x), GArg::Row(y)) => {
                // A row that is only a variable becomes the other row.
                let (ex, ey) = (self.expand_effs(x), self.expand_effs(y));
                for (var, other) in [(&ex, &ey), (&ey, &ex)] {
                    if let (true, Tail::Var(v)) = (var.effs.is_empty(), &var.tail) {
                        if other.tail != Tail::Var(*v) {
                            self.effs[*v as usize] = Some(other.clone());
                        }
                        return Ok(());
                    }
                }
                self.eff_sub(x, y).map_err(|_| Mismatch)?;
                self.eff_sub(y, x).map_err(|_| Mismatch)
            }
            (GArg::Len(x), GArg::Len(y)) => self.unify_len(x, y),
            _ => Err(Mismatch),
        }
    }

    pub fn unify_region(&mut self, a: &Region, b: &Region) -> UResult {
        let (a, b) = (self.resolve_region(a), self.resolve_region(b));
        match (&a, &b) {
            _ if a == b => Ok(()),
            (Region::Var(v), _) => {
                self.regions[*v as usize] = Some(b);
                Ok(())
            }
            (_, Region::Var(v)) => {
                self.regions[*v as usize] = Some(a);
                Ok(())
            }
            _ => Err(Mismatch),
        }
    }

    pub fn unify_len(&mut self, a: &Len, b: &Len) -> UResult {
        let (a, b) = (self.resolve_len(a), self.resolve_len(b));
        match (&a, &b) {
            _ if a == b => Ok(()),
            (Len::Var(v), _) => {
                self.lens[*v as usize] = Some(b);
                Ok(())
            }
            (_, Len::Var(v)) => {
                self.lens[*v as usize] = Some(a);
                Ok(())
            }
            _ => Err(Mismatch),
        }
    }

    fn bind_row_tail(&mut self, tail: &Tail, labels: BTreeMap<String, Ty>, rest: Tail) -> UResult {
        match tail {
            Tail::Var(v) => {
                if labels.is_empty() && rest == *tail {
                    return Ok(());
                }
                self.rows[*v as usize] = Some(Row { labels, tail: rest });
                Ok(())
            }
            Tail::Closed | Tail::Param(_) if labels.is_empty() && rest == *tail => Ok(()),
            _ => Err(Mismatch),
        }
    }

    /// Rémy row unification for records and tag unions.
    pub fn unify_rows(&mut self, a: &Row, b: &Row) -> UResult {
        let (a, b) = (self.expand_row(a), self.expand_row(b));
        for (k, ta) in &a.labels {
            if let Some(tb) = b.labels.get(k) {
                self.unify(ta, tb)?;
            }
        }
        let only_a: BTreeMap<String, Ty> =
            a.labels.iter().filter(|(k, _)| !b.labels.contains_key(*k)).map(|(k, t)| (k.clone(), t.clone())).collect();
        let only_b: BTreeMap<String, Ty> =
            b.labels.iter().filter(|(k, _)| !a.labels.contains_key(*k)).map(|(k, t)| (k.clone(), t.clone())).collect();
        match (&a.tail, &b.tail) {
            (Tail::Var(x), Tail::Var(y)) if x == y => {
                if only_a.is_empty() && only_b.is_empty() { Ok(()) } else { Err(Mismatch) }
            }
            (Tail::Var(_), Tail::Var(_)) => {
                let fresh = self.fresh_row_tail();
                self.bind_row_tail(&a.tail, only_b, fresh.clone())?;
                self.bind_row_tail(&b.tail, only_a, fresh)
            }
            (Tail::Var(_), _) => {
                if !only_a.is_empty() {
                    return Err(Mismatch);
                }
                self.bind_row_tail(&a.tail, only_b, b.tail.clone())
            }
            (_, Tail::Var(_)) => {
                if !only_b.is_empty() {
                    return Err(Mismatch);
                }
                self.bind_row_tail(&b.tail, only_a, a.tail.clone())
            }
            (x, y) if x == y && only_a.is_empty() && only_b.is_empty() => Ok(()),
            _ => Err(Mismatch),
        }
    }

    /// Tag-union inclusion: every tag `actual` may carry is allowed by `allowed`. Used for
    /// `Fail` payloads, so that failure sets compose by union.
    pub fn union_sub(&mut self, actual: &Ty, allowed: &Ty) -> UResult {
        let (a, b) = (self.resolve(actual), self.resolve(allowed));
        let (Ty::Union(ra), Ty::Union(rb)) = (&a, &b) else {
            return self.unify(&a, &b);
        };
        let (ra, mut rb) = (self.expand_row(ra), self.expand_row(rb));
        for (k, ta) in &ra.labels {
            if let Some(tb) = rb.labels.get(k).cloned() {
                self.unify(ta, &tb)?;
            } else if let Tail::Var(_) = rb.tail {
                let rest = self.fresh_row_tail();
                let mut one = BTreeMap::new();
                one.insert(k.clone(), ta.clone());
                self.bind_row_tail(&rb.tail.clone(), one, rest)?;
                rb = self.expand_row(&rb);
            } else {
                return Err(Mismatch);
            }
        }
        match (&ra.tail, &rb.tail) {
            (Tail::Var(_), t) => {
                let t = t.clone();
                self.bind_row_tail(&ra.tail, BTreeMap::new(), t)
            }
            (Tail::Closed, _) => Ok(()),
            (Tail::Param(p), Tail::Param(q)) if p == q => Ok(()),
            (Tail::Param(_), Tail::Var(_)) => {
                let t = ra.tail.clone();
                self.bind_row_tail(&rb.tail.clone(), BTreeMap::new(), t)
            }
            _ => Err(Mismatch),
        }
    }

    /// Closes the open tail of a tag union (handling `Fail`, §5.4).
    /// Closes every record and union row in `t` whose tail is still a variable: once a
    /// function's types are final, nothing can add labels to them (§3.2).
    pub fn close_rows(&mut self, t: &Ty) {
        match self.resolve(t) {
            Ty::Record(r) | Ty::Union(r) => {
                let r = self.expand_row(&r);
                if let Tail::Var(_) = r.tail {
                    let _ = self.bind_row_tail(&r.tail, BTreeMap::new(), Tail::Closed);
                }
                for t in r.labels.values() {
                    self.close_rows(t);
                }
            }
            Ty::Named(_, args) => {
                for a in &args {
                    if let GArg::Ty(t) = a {
                        self.close_rows(t);
                    }
                }
            }
            Ty::Tuple(ts) => ts.iter().for_each(|t| self.close_rows(t)),
            Ty::Array(t, _) | Ty::Slice(t) | Ty::Borrow(_, t) => self.close_rows(&t),
            _ => {}
        }
    }

    pub fn close_union(&mut self, t: &Ty) {
        if let Ty::Union(r) = self.resolve(t) {
            let r = self.expand_row(&r);
            if let Tail::Var(_) = r.tail {
                let _ = self.bind_row_tail(&r.tail, BTreeMap::new(), Tail::Closed);
            }
        }
    }

    /// Binds an unbound record- or union-row variable to `row`.
    pub fn bind_row(&mut self, v: u32, row: Row) {
        self.rows[v as usize] = Some(row);
    }

    /// Binds an unbound effect-row variable to `row`.
    pub fn bind_effs(&mut self, v: u32, row: EffRow) {
        self.effs[v as usize] = Some(row);
    }

    pub fn regions_equal(&self, a: &[Region], b: &[Region]) -> bool {
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| self.resolve_region(x) == self.resolve_region(y))
    }

    /// Effect-row subsumption: every effect of `actual` is in `allowed`, extending `allowed`'s
    /// open tail where needed. On failure, returns the effect that does not fit.
    pub fn eff_sub(&mut self, actual: &EffRow, allowed: &EffRow) -> Result<(), Eff> {
        let actual = self.expand_effs(actual);
        for eff in &actual.effs {
            let row = self.expand_effs(allowed);
            // Prefer an exact region match; otherwise the first (innermost) effect of the same
            // name whose regions unify.
            let candidate = row
                .effs
                .iter()
                .find(|c| c.def == eff.def && self.regions_equal(&c.regions, &eff.regions))
                .or_else(|| {
                    row.effs.iter().find(|c| {
                        c.def == eff.def && {
                            let mut probe = self.clone();
                            c.regions.iter().zip(&eff.regions).all(|(x, y)| probe.unify_region(x, y).is_ok())
                        }
                    })
                })
                .cloned();
            match candidate {
                Some(c) => {
                    for (x, y) in c.regions.iter().zip(&eff.regions) {
                        self.unify_region(x, y).map_err(|_| eff.clone())?;
                    }
                    for (x, y) in eff.args.iter().zip(&c.args) {
                        let ok = match (self.resolve(x), self.resolve(y)) {
                            (Ty::Union(_), Ty::Union(_)) => self.union_sub(x, y),
                            _ => self.unify(x, y),
                        };
                        ok.map_err(|_| eff.clone())?;
                    }
                }
                None => match &row.tail {
                    Tail::Var(v) => {
                        let rest = self.fresh_eff_tail();
                        self.effs[*v as usize] = Some(EffRow { effs: vec![eff.clone()], tail: rest });
                    }
                    _ => return Err(eff.clone()),
                },
            }
        }
        // An open tail on the actual side stands for unknown further effects; they must be
        // allowed by the other side's tail.
        let row = self.expand_effs(allowed);
        match (&actual.tail, &row.tail) {
            (Tail::Var(x), Tail::Var(y)) if x == y => Ok(()),
            (Tail::Var(v), t) => {
                self.effs[*v as usize] = Some(EffRow { effs: Vec::new(), tail: t.clone() });
                Ok(())
            }
            (Tail::Closed, _) => Ok(()),
            (Tail::Param(p), Tail::Param(q)) if p == q => Ok(()),
            (Tail::Param(_), Tail::Var(v)) => {
                self.effs[*v as usize] = Some(EffRow { effs: Vec::new(), tail: actual.tail.clone() });
                Ok(())
            }
            (Tail::Param(p), _) => Err(Eff { def: usize::MAX, regions: Vec::new(), args: vec![Ty::Param(p.clone())] }),
        }
    }

    /// Integer and float variables left unconstrained take their defaults (§2.2).
    pub fn default_literals(&mut self) {
        for i in 0..self.tys.len() {
            if self.tys[i].0.is_none() {
                match self.tys[i].1.0 {
                    VarKind::Int => self.tys[i].0 = Some(Ty::Prim(Prim::I32)),
                    VarKind::Float => self.tys[i].0 = Some(Ty::Prim(Prim::F64)),
                    VarKind::Any => {}
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rec(s: &mut Subst, fields: &[(&str, Ty)], open: bool) -> Ty {
        let labels = fields.iter().map(|(k, t)| (k.to_string(), t.clone())).collect();
        let tail = if open { s.fresh_row_tail() } else { Tail::Closed };
        Ty::Record(Row { labels, tail })
    }

    fn tag(s: &mut Subst, tags: &[&str], open: bool) -> Ty {
        let labels = tags.iter().map(|k| (k.to_string(), Ty::void())).collect();
        let tail = if open { s.fresh_row_tail() } else { Tail::Closed };
        Ty::Union(Row { labels, tail })
    }

    #[test]
    fn row_polymorphic_record() {
        let mut s = Subst::default();
        let f64t = Ty::Prim(Prim::F64);
        let want = rec(&mut s, &[("x", f64t.clone()), ("y", f64t.clone())], true);
        let have = rec(&mut s, &[("x", f64t.clone()), ("y", f64t.clone()), ("label", Ty::Prim(Prim::Str))], false);
        s.unify(&want, &have).unwrap();
        let closed_missing = rec(&mut s, &[("x", f64t)], false);
        let mut s2 = s.clone();
        let want2 = rec(&mut s2, &[("y", Ty::Prim(Prim::F64))], false);
        assert!(s2.unify(&want2, &closed_missing).is_err());
    }

    #[test]
    fn open_unions_merge_and_close() {
        let mut s = Subst::default();
        let a = tag(&mut s, &["Eof"], true);
        let b = tag(&mut s, &["Bad"], true);
        s.unify(&a, &b).unwrap();
        s.close_union(&a);
        let Ty::Union(r) = s.zonk(&a) else { panic!() };
        assert_eq!(r.labels.keys().cloned().collect::<Vec<_>>(), vec!["Bad", "Eof"]);
        assert_eq!(r.tail, Tail::Closed);
    }

    #[test]
    fn union_inclusion() {
        let mut s = Subst::default();
        let declared = tag(&mut s, &["Eof", "Bad"], false);
        let thrown = tag(&mut s, &["Eof"], true);
        s.union_sub(&thrown, &declared).unwrap();
        let other = tag(&mut s, &["Other"], true);
        assert!(s.union_sub(&other, &declared).is_err());
    }

    #[test]
    fn effects_are_sets_with_region_labels() {
        let mut s = Subst::default();
        let (io, region) = (0usize, 1usize);
        let r1 = Region::Param(Sym { id: 1, name: "R1".into() });
        let r2 = Region::Param(Sym { id: 2, name: "R2".into() });
        let allowed = EffRow {
            effs: vec![
                Eff { def: region, regions: vec![r2.clone()], args: vec![] },
                Eff { def: region, regions: vec![r1.clone()], args: vec![] },
                Eff { def: io, regions: vec![], args: vec![] },
            ],
            tail: Tail::Closed,
        };
        let outer = EffRow { effs: vec![Eff { def: region, regions: vec![r1.clone()], args: vec![] }], tail: Tail::Closed };
        s.eff_sub(&outer, &allowed).unwrap();
        // An unresolved region is solved by the innermost handler.
        let v = s.fresh_region();
        let fresh = EffRow { effs: vec![Eff { def: region, regions: vec![v.clone()], args: vec![] }], tail: Tail::Closed };
        s.eff_sub(&fresh, &allowed).unwrap();
        assert_eq!(s.resolve_region(&v), r2);
        // Io twice is still Io.
        let twice = EffRow { effs: vec![Eff { def: io, regions: vec![], args: vec![] }; 2], tail: Tail::Closed };
        s.eff_sub(&twice, &allowed).unwrap();
        let undeclared = EffRow { effs: vec![Eff { def: 9, regions: vec![], args: vec![] }], tail: Tail::Closed };
        assert!(s.eff_sub(&undeclared, &allowed).is_err());
    }

    #[test]
    fn open_effect_rows_extend() {
        let mut s = Subst::default();
        let open = s.fresh_effs();
        let body = EffRow { effs: vec![Eff { def: 3, regions: vec![], args: vec![] }], tail: Tail::Closed };
        s.eff_sub(&body, &open).unwrap();
        assert_eq!(s.expand_effs(&open).effs.len(), 1);
    }
}
