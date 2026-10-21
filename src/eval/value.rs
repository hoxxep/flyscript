//! Runtime values. Ownership was checked statically, so the runtime shares freely: every local is
//! a cell, and a borrow is a pointer to a place (a cell and a path into it).

use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Arc, Mutex};

use crate::syntax::ast;

pub type Shared = Arc<Mutex<Value>>;

pub fn shared(v: Value) -> Shared {
    Arc::new(Mutex::new(v))
}

#[derive(Clone, Debug, PartialEq)]
pub enum Seg {
    Field(String),
    Index(usize),
    /// A slice of a list or string, `lo..hi`.
    Range(usize, usize),
}

#[derive(Clone)]
pub struct Place {
    pub root: Shared,
    pub path: Vec<Seg>,
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "&{:?}", self.path)
    }
}

pub struct Closure {
    pub params: Vec<String>,
    pub body: ast::Expr,
    pub env: Vec<(String, Shared)>,
    pub module: usize,
    /// The function whose body the closure appears in, for its recorded types.
    pub owner: usize,
}

#[derive(Clone)]
pub enum Value {
    Unit,
    Bool(bool),
    Int(i128),
    Float(f64),
    /// A string: `str` and `String` alike.
    Text(Arc<str>),
    Tuple(Vec<Value>),
    Record(BTreeMap<String, Value>),
    /// A tag and its payload (`Unit`, a `Tuple` or a `Record`).
    Tag(Arc<str>, Box<Value>),
    /// Arrays, `Vec`s and slices.
    List(Vec<Value>),
    /// A `HashMap`, kept in insertion order.
    Map(Vec<(Value, Value)>),
    /// A borrow: transparent, it reads and writes through to its place.
    Ptr(Place),
    /// A region reference (§4.6): a `Copy` pointer that stays a pointer when stored or passed.
    Ref(Shared),
    /// A mutable slot (`Cell`) or a shared container such as a channel.
    Cell(Shared),
    Closure(Arc<Closure>),
    /// A function by id, or a resumption of handler `n` (a tail-resumptive continuation).
    Func(usize),
    Resume(u64),
    /// A runtime object (a socket, a generator, a fiber, …), by kind and id.
    Native(&'static str, u64),
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.show())
    }
}

impl Value {
    pub fn tag(name: &str, payload: Value) -> Value {
        Value::Tag(Arc::from(name), Box::new(payload))
    }

    pub fn text(s: &str) -> Value {
        Value::Text(Arc::from(s))
    }

    /// Follows borrows and region references to the value they point at.
    pub fn deref(&self) -> Value {
        match self {
            Value::Ptr(p) => get(p).deref(),
            Value::Ref(r) => r.lock().expect("ref").clone().deref(),
            v => v.clone(),
        }
    }

    pub fn as_int(&self) -> i128 {
        match self.deref() {
            Value::Int(i) => i,
            Value::Float(f) => f as i128,
            Value::Bool(b) => b as i128,
            other => panic!("expected an integer, found {}", other.show()),
        }
    }

    pub fn as_float(&self) -> f64 {
        match self.deref() {
            Value::Float(f) => f,
            Value::Int(i) => i as f64,
            other => panic!("expected a number, found {}", other.show()),
        }
    }

    pub fn as_bool(&self) -> bool {
        matches!(self.deref(), Value::Bool(true))
    }

    pub fn as_text(&self) -> Arc<str> {
        match self.deref() {
            Value::Text(s) => s,
            Value::List(bytes) => Arc::from(String::from_utf8_lossy(&bytes.iter().map(|b| b.as_int() as u8).collect::<Vec<u8>>()).as_ref()),
            other => Arc::from(other.show().as_str()),
        }
    }

    /// `Show` (§3.5): how a value prints, for template literals and `println`.
    pub fn show(&self) -> String {
        match self {
            Value::Unit => "void".into(),
            Value::Bool(b) => b.to_string(),
            Value::Int(i) => i.to_string(),
            Value::Float(f) => {
                if f.fract() == 0.0 && f.abs() < 1e15 { format!("{f:.1}") } else { f.to_string() }
            }
            Value::Text(s) => s.to_string(),
            Value::Tuple(vs) | Value::List(vs) => {
                format!("[{}]", vs.iter().map(|v| v.show_nested()).collect::<Vec<_>>().join(", "))
            }
            Value::Record(fields) => format!(
                "{{ {} }}",
                fields.iter().map(|(k, v)| format!("{k}: {}", v.show_nested())).collect::<Vec<_>>().join(", ")
            ),
            Value::Tag(name, payload) => match &**payload {
                Value::Unit => format!("#{name}"),
                Value::Tuple(vs) => format!("#{name}({})", vs.iter().map(|v| v.show_nested()).collect::<Vec<_>>().join(", ")),
                other => format!("#{name} {}", other.show_nested()),
            },
            Value::Map(entries) => format!(
                "{{ {} }}",
                entries.iter().map(|(k, v)| format!("{}: {}", k.show_nested(), v.show_nested())).collect::<Vec<_>>().join(", ")
            ),
            Value::Ptr(p) => get(p).show(),
            Value::Ref(r) => r.lock().expect("ref").show(),
            Value::Cell(c) => c.lock().expect("cell").show(),
            Value::Closure(_) | Value::Func(_) | Value::Resume(_) => "<function>".into(),
            Value::Native(kind, id) => format!("<{kind} {id}>"),
        }
    }

    fn show_nested(&self) -> String {
        match self.deref() {
            Value::Text(s) => format!("{s:?}"),
            v => v.show(),
        }
    }

    /// Structural equality (`Eq`, §3.5), through borrows.
    pub fn equals(&self, other: &Value) -> bool {
        match (self.deref(), other.deref()) {
            (Value::Unit, Value::Unit) => true,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Int(a), Value::Float(b)) | (Value::Float(b), Value::Int(a)) => a as f64 == b,
            (Value::Text(a), Value::Text(b)) => a == b,
            (Value::Text(a), Value::List(b)) | (Value::List(b), Value::Text(a)) => {
                a.len() == b.len() && a.as_bytes().iter().zip(&b).all(|(x, y)| *x as i128 == y.as_int())
            }
            (Value::Tuple(a), Value::Tuple(b)) | (Value::List(a), Value::List(b)) => {
                a.len() == b.len() && a.iter().zip(&b).all(|(x, y)| x.equals(y))
            }
            (Value::Record(a), Value::Record(b)) => a.len() == b.len() && a.iter().all(|(k, v)| b.get(k).is_some_and(|w| v.equals(w))),
            (Value::Tag(a, p), Value::Tag(b, q)) => a == b && p.equals(&q),
            (Value::Native(k, a), Value::Native(l, b)) => k == l && a == b,
            _ => false,
        }
    }
}

// ---- places ----

fn step(v: &Value, seg: &Seg) -> Value {
    match (v, seg) {
        (Value::Record(fs), Seg::Field(f)) => fs.get(f).cloned().unwrap_or(Value::Unit),
        (Value::Tag(_, payload), _) => step(payload, seg),
        (Value::List(vs) | Value::Tuple(vs), Seg::Index(i)) => vs.get(*i).cloned().unwrap_or_else(|| panic!("index {i} out of bounds (length {})", vs.len())),
        (Value::Text(s), Seg::Index(i)) => Value::Int(*s.as_bytes().get(*i).unwrap_or_else(|| panic!("index {i} out of bounds")) as i128),
        (Value::List(vs), Seg::Range(lo, hi)) => Value::List(vs[*lo..*hi].to_vec()),
        (Value::Text(s), Seg::Range(lo, hi)) => Value::Text(Arc::from(&s[*lo..*hi])),
        (other, seg) => panic!("cannot follow {seg:?} into {}", other.show()),
    }
}

/// Reads the value at a place, following borrows met along the path.
pub fn get(p: &Place) -> Value {
    let mut v = p.root.lock().expect("place").clone();
    for (i, seg) in p.path.iter().enumerate() {
        if let Value::Ptr(inner) = &v {
            let mut q = inner.clone();
            q.path.extend(p.path[i..].iter().cloned());
            return get(&q);
        }
        if let Value::Cell(c) | Value::Ref(c) = &v {
            let q = Place { root: c.clone(), path: p.path[i..].to_vec() };
            return get(&q);
        }
        v = step(&v, seg);
    }
    v
}

/// Writes the value at a place, following borrows met along the path.
pub fn set(p: &Place, new: Value) {
    // Find a borrow on the way; if there is one, write through it instead.
    let mut v = p.root.lock().expect("place").clone();
    for (i, seg) in p.path.iter().enumerate() {
        if let Value::Ptr(inner) = &v {
            let mut q = inner.clone();
            q.path.extend(p.path[i..].iter().cloned());
            return set(&q, new);
        }
        if let Value::Cell(c) | Value::Ref(c) = &v {
            let q = Place { root: c.clone(), path: p.path[i..].to_vec() };
            return set(&q, new);
        }
        v = step(&v, seg);
    }
    let mut root = p.root.lock().expect("place");
    write_at(&mut root, &p.path, new);
}

fn write_at(v: &mut Value, path: &[Seg], new: Value) {
    let Some((first, rest)) = path.split_first() else {
        *v = new;
        return;
    };
    match (v, first) {
        (Value::Record(fs), Seg::Field(f)) => write_at(fs.entry(f.clone()).or_insert(Value::Unit), rest, new),
        (Value::Tag(_, payload), _) => write_at(payload, path, new),
        (Value::List(vs) | Value::Tuple(vs), Seg::Index(i)) => write_at(&mut vs[*i], rest, new),
        (Value::List(vs), Seg::Range(lo, _)) => {
            if let Some((Seg::Index(i), rest2)) = rest.split_first() {
                write_at(&mut vs[lo + i], rest2, new);
            }
        }
        (other, seg) => panic!("cannot write {seg:?} into {}", other.show()),
    }
}

/// Applies `f` to the value at a place, in place (used for `push`-like operations).
pub fn update(p: &Place, f: impl FnOnce(&mut Value)) {
    let mut v = get(p);
    f(&mut v);
    set(p, v);
}
