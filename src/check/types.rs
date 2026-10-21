//! Types as the checker sees them.

use std::collections::BTreeMap;
use std::fmt;

/// A rigid type, region or row parameter: unique per declaration, with a display name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sym {
    pub id: u32,
    pub name: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Prim {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    F32,
    F64,
    Bool,
    Str,
    Void,
    Never,
    Type,
}

impl Prim {
    pub fn from_name(s: &str) -> Option<Prim> {
        Some(match s {
            "i8" => Prim::I8,
            "i16" => Prim::I16,
            "i32" => Prim::I32,
            "i64" => Prim::I64,
            "isize" => Prim::Isize,
            "u8" => Prim::U8,
            "u16" => Prim::U16,
            "u32" => Prim::U32,
            "u64" => Prim::U64,
            "usize" => Prim::Usize,
            "f32" => Prim::F32,
            "f64" => Prim::F64,
            "bool" => Prim::Bool,
            "str" => Prim::Str,
            "void" => Prim::Void,
            "never" => Prim::Never,
            "Type" => Prim::Type,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            Prim::I8 => "i8",
            Prim::I16 => "i16",
            Prim::I32 => "i32",
            Prim::I64 => "i64",
            Prim::Isize => "isize",
            Prim::U8 => "u8",
            Prim::U16 => "u16",
            Prim::U32 => "u32",
            Prim::U64 => "u64",
            Prim::Usize => "usize",
            Prim::F32 => "f32",
            Prim::F64 => "f64",
            Prim::Bool => "bool",
            Prim::Str => "str",
            Prim::Void => "void",
            Prim::Never => "never",
            Prim::Type => "Type",
        }
    }

    pub fn is_int(self) -> bool {
        matches!(
            self,
            Prim::I8 | Prim::I16 | Prim::I32 | Prim::I64 | Prim::Isize | Prim::U8 | Prim::U16 | Prim::U32 | Prim::U64 | Prim::Usize
        )
    }

    pub fn is_float(self) -> bool {
        matches!(self, Prim::F32 | Prim::F64)
    }
}

/// Index of a declaration (struct, enum, alias, interface, effect) in the program.
pub type DefId = usize;

#[derive(Clone, Debug, PartialEq)]
pub enum Region {
    Var(u32),
    Param(Sym),
    Heap,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Tail {
    Closed,
    Var(u32),
    Param(Sym),
}

/// A record or tag-union row. For a union, a tag's payload is `void` (none), a tuple or a record.
#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    pub labels: BTreeMap<String, Ty>,
    pub tail: Tail,
}

impl Row {
    pub fn closed(labels: BTreeMap<String, Ty>) -> Row {
        Row { labels, tail: Tail::Closed }
    }
}

/// One effect in a row: its declaration, its region arguments (part of its label, §3.2) and
/// its other arguments (determined by the label).
#[derive(Clone, Debug, PartialEq)]
pub struct Eff {
    pub def: DefId,
    pub regions: Vec<Region>,
    pub args: Vec<Ty>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EffRow {
    pub effs: Vec<Eff>,
    /// `Tail::Var` indexes the effect-row variables, not the record-row variables.
    pub tail: Tail,
}

impl EffRow {
    pub fn pure() -> EffRow {
        EffRow { effs: Vec::new(), tail: Tail::Closed }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FnMode {
    Shared,
    Mut,
    Once,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FnTy {
    pub mode: FnMode,
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub effects: EffRow,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Len {
    Known(u64),
    Var(u32),
    Param(Sym),
}

/// A generic argument: generic parameters are types, regions or rows.
#[derive(Clone, Debug, PartialEq)]
pub enum GArg {
    Ty(Ty),
    Region(Region),
    /// A row argument; whether it is used as an effect row or a record row depends on the
    /// parameter's uses, so both forms are carried.
    Row(EffRow),
    Len(Len),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Ty {
    Var(u32),
    Param(Sym),
    Prim(Prim),
    Named(DefId, Vec<GArg>),
    Record(Row),
    Union(Row),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, Len),
    Slice(Box<Ty>),
    Borrow(bool, Box<Ty>),
    Fn(Box<FnTy>),
    /// An associated type projection, `C.View`, normalized once `C` is known.
    Assoc(Box<Ty>, String),
    /// A type that has already produced an error; unifies with anything.
    Error,
}

impl Ty {
    pub fn void() -> Ty {
        Ty::Prim(Prim::Void)
    }
    pub fn never() -> Ty {
        Ty::Prim(Prim::Never)
    }
    pub fn bool() -> Ty {
        Ty::Prim(Prim::Bool)
    }
    pub fn is_never(&self) -> bool {
        matches!(self, Ty::Prim(Prim::Never))
    }
}

/// Names for printing types, supplied by the checker.
pub trait Names {
    fn def_name(&self, def: DefId) -> String;
}

pub struct Show<'a, T: ?Sized>(pub &'a T, pub &'a dyn Names);

fn list<T>(f: &mut fmt::Formatter<'_>, names: &dyn Names, items: &[T], show: impl Fn(&T, &mut fmt::Formatter<'_>, &dyn Names) -> fmt::Result) -> fmt::Result {
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        show(item, f, names)?;
    }
    Ok(())
}

impl fmt::Display for Show<'_, Ty> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = self.1;
        match self.0 {
            Ty::Var(v) => write!(f, "?{v}"),
            Ty::Param(s) => write!(f, "{}", s.name),
            Ty::Prim(p) => write!(f, "{}", p.name()),
            Ty::Named(d, args) => {
                write!(f, "{}", n.def_name(*d))?;
                if !args.is_empty() {
                    write!(f, "<")?;
                    list(f, n, args, |a, f, n| write!(f, "{}", Show(a, n)))?;
                    write!(f, ">")?;
                }
                Ok(())
            }
            Ty::Record(r) => {
                write!(f, "{{ ")?;
                for (k, v) in &r.labels {
                    write!(f, "{k}: {}; ", Show(v, n))?;
                }
                show_tail(f, &r.tail, "...")?;
                write!(f, "}}")
            }
            Ty::Union(r) => {
                let mut first = true;
                for (k, v) in &r.labels {
                    if !first {
                        write!(f, " | ")?;
                    }
                    first = false;
                    write!(f, "#{k}")?;
                    match v {
                        Ty::Prim(Prim::Void) => {}
                        Ty::Tuple(ts) => {
                            write!(f, "(")?;
                            list(f, n, ts, |t, f, n| write!(f, "{}", Show(t, n)))?;
                            write!(f, ")")?;
                        }
                        other => write!(f, " {}", Show(other, n))?,
                    }
                }
                match &r.tail {
                    Tail::Closed => Ok(()),
                    t => {
                        write!(f, " | ")?;
                        show_tail(f, t, "...")
                    }
                }
            }
            Ty::Tuple(ts) => {
                write!(f, "[")?;
                list(f, n, ts, |t, f, n| write!(f, "{}", Show(t, n)))?;
                write!(f, "]")
            }
            Ty::Array(t, len) => {
                write!(f, "{}[", Show(&**t, n))?;
                match len {
                    Len::Known(k) => write!(f, "{k}")?,
                    Len::Var(v) => write!(f, "?{v}")?,
                    Len::Param(s) => write!(f, "{}", s.name)?,
                }
                write!(f, "]")
            }
            Ty::Slice(t) => write!(f, "{}[]", Show(&**t, n)),
            Ty::Borrow(m, t) => write!(f, "{} {}", if *m { "mut" } else { "readonly" }, Show(&**t, n)),
            Ty::Fn(ft) => {
                let mode = match ft.mode {
                    FnMode::Shared => "",
                    FnMode::Mut => "mut ",
                    FnMode::Once => "once ",
                };
                write!(f, "{mode}(")?;
                list(f, n, &ft.params, |t, f, n| write!(f, "{}", Show(t, n)))?;
                write!(f, ") => {}", Show(&ft.ret, n))?;
                if !ft.effects.effs.is_empty() || ft.effects.tail != Tail::Closed {
                    write!(f, " uses {}", Show(&ft.effects, n))?;
                }
                Ok(())
            }
            Ty::Assoc(t, name) => write!(f, "{}.{name}", Show(&**t, n)),
            Ty::Error => write!(f, "{{error}}"),
        }
    }
}

fn show_tail(f: &mut fmt::Formatter<'_>, tail: &Tail, prefix: &str) -> fmt::Result {
    // Row and effect variables print as `?r3` and `?e3`, distinct from type variables `?3`.
    let kind = if prefix.ends_with('e') { "e" } else { "r" };
    let prefix = prefix.trim_end_matches('e');
    match tail {
        Tail::Closed => Ok(()),
        Tail::Var(v) => write!(f, "{prefix}?{kind}{v}"),
        Tail::Param(s) => write!(f, "{prefix}{}", s.name),
    }
}

impl fmt::Display for Show<'_, GArg> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            GArg::Ty(t) => write!(f, "{}", Show(t, self.1)),
            GArg::Region(r) => write!(f, "{}", Show(r, self.1)),
            GArg::Row(r) => write!(f, "[{}]", Show(r, self.1)),
            GArg::Len(Len::Known(k)) => write!(f, "{k}"),
            GArg::Len(Len::Var(v)) => write!(f, "?{v}"),
            GArg::Len(Len::Param(s)) => write!(f, "{}", s.name),
        }
    }
}

impl fmt::Display for Show<'_, Region> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Region::Var(v) => write!(f, "'?{v}"),
            Region::Param(s) => write!(f, "{}", s.name),
            Region::Heap => write!(f, "Heap"),
        }
    }
}

impl fmt::Display for Show<'_, Eff> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let e = self.0;
        write!(f, "{}", self.1.def_name(e.def))?;
        if !e.regions.is_empty() || !e.args.is_empty() {
            write!(f, "<")?;
            list(f, self.1, &e.regions, |r, f, n| write!(f, "{}", Show(r, n)))?;
            if !e.regions.is_empty() && !e.args.is_empty() {
                write!(f, ", ")?;
            }
            list(f, self.1, &e.args, |t, f, n| write!(f, "{}", Show(t, n)))?;
            write!(f, ">")?;
        }
        Ok(())
    }
}

impl fmt::Display for Show<'_, EffRow> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        list(f, self.1, &self.0.effs, |e, f, n| write!(f, "{}", Show(e, n)))?;
        if self.0.tail != Tail::Closed {
            if !self.0.effs.is_empty() {
                write!(f, ", ")?;
            }
            show_tail(f, &self.0.tail, "...e")?;
        }
        Ok(())
    }
}
