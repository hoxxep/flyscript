//! The native bodies of the standard library's declarations (`std/*.d.fly`).

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use super::generators::{self as gens_mod, GenKind};
use super::interp::{Ctl, Handler, Interp, R, panic, EXITED};
use super::value::*;
use crate::check::env::FnId;
use crate::check::types::{GArg, Prim, Ty};

/// A structured-concurrency scope (§6.1). Tasks run to completion when started, in order, which
/// keeps runs deterministic; a forked task's failure is rethrown by the scope.
#[derive(Default)]
pub struct ScopeState {
    /// The task running the scope's body, cancelled with the rest when a task fails.
    pub owner: u64,
    pub failure: Option<Value>,
    /// Every task started in the scope; the scope waits for all of them.
    pub tasks: Vec<u64>,
    /// Forked tasks' outcomes, by task.
    pub fibers: HashMap<u64, Result<Value, Value>>,
}

fn none() -> Value {
    Value::tag("None", Value::Unit)
}

fn some(v: Value) -> Value {
    Value::tag("Some", Value::Tuple(vec![v].into()))
}

pub(crate) fn place_of(v: &Value) -> Result<Place, Ctl> {
    match v {
        Value::Ptr(p) => Ok(resolve(p.clone())),
        Value::Ref(r) => Ok(Place { root: r.clone(), path: Vec::new() }),
        other => Ok(Place { root: shared(other.clone()), path: Vec::new() }),
    }
}

/// The place a borrow ultimately refers to: a binding that holds a borrow is followed to what
/// that borrow refers to, so a view of a view is one place.
fn resolve(mut p: Place) -> Place {
    for _ in 0..64 {
        let next = match &*p.root.lock().expect("place") {
            Value::Ptr(q) => q.clone(),
            _ => break,
        };
        let mut path = next.path;
        path.extend(p.path);
        p = Place { root: next.root, path };
    }
    p
}

fn native(v: &Value, kind: &str) -> Result<u64, Ctl> {
    match v.deref() {
        Value::Native(k, id) if k == kind => Ok(id),
        other => Err(panic(format!("expected a {kind}, found {}", other.show()))),
    }
}

/// A string's bytes, as `asBytes` lends them: the string itself stands for its byte slice.
fn bytes_of(s: &str) -> Vec<Value> {
    s.bytes().map(|b| Value::Int(b as i128)).collect()
}

fn list(v: &Value) -> Vec<Value> {
    match v.deref() {
        Value::List(vs) | Value::Tuple(vs) => Arc::unwrap_or_clone(vs),
        Value::Text(s) => bytes_of(&s),
        Value::Cell(c) => match &*c.lock().expect("cell") {
            Value::List(vs) => vs.to_vec(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

/// Applies `f` to the list a value is or lends, without copying it.
fn with_list<R>(v: &Value, f: impl FnOnce(&[Value]) -> R) -> R {
    match v {
        Value::List(vs) | Value::Tuple(vs) => f(vs),
        Value::Ptr(p) => view(p, |x| with_list(x, f)),
        Value::Cell(c) | Value::Ref(c) => with_list(&c.lock().expect("cell"), f),
        Value::Text(s) => f(&bytes_of(s)),
        _ => f(&[]),
    }
}

/// The number of entries in a map, without copying it.
fn map_len(v: &Value) -> usize {
    match v {
        Value::Map(d) => d.len(),
        Value::Ptr(p) => view(p, map_len),
        Value::Cell(c) | Value::Ref(c) => map_len(&c.lock().expect("cell")),
        _ => 0,
    }
}

/// The length of a list, or of the bytes a string stands for, without copying either.
fn len_of(v: &Value) -> usize {
    match v {
        Value::Text(s) => s.len(),
        Value::Ptr(p) => view(p, len_of),
        Value::Cell(c) | Value::Ref(c) => len_of(&c.lock().expect("cell")),
        _ => with_list(v, <[Value]>::len),
    }
}

impl Interp {
    /// The name a builtin is known by: `Type.function`, or `function` for a free function.
    fn builtin_key(&self, fid: FnId) -> String {
        let info = &self.prog.fns[fid];
        let Some(i) = info.impl_id else { return info.name.clone() };
        let target = match &self.prog.impls[i].target {
            Ty::Named(d, _) => self.prog.defs[*d].name.clone(),
            Ty::Prim(Prim::Str) => "str".into(),
            Ty::Prim(p) => p.name().into(),
            Ty::Slice(_) => "slice".into(),
            Ty::Array(..) => "array".into(),
            Ty::Union(r) if r.labels.contains_key("Some") => "Option".into(),
            Ty::Union(r) if r.labels.contains_key("Ok") => "Result".into(),
            _ => "?".into(),
        };
        format!("{target}.{}", info.name)
    }

    /// Type argument `i` of the builtin `fid` being called, its impl's first: what a builtin that
    /// drops values drops them as.
    fn type_arg(&self, fid: FnId, i: usize) -> Option<Ty> {
        let g = self.prog.fns[fid].scheme.tparams.get(i)?;
        match self.lex.tenv.get(&g.sym.id)? {
            GArg::Ty(t) => Some(t.clone()),
            _ => None,
        }
    }

    pub fn builtin(&mut self, fid: FnId, mut args: Vec<Value>) -> R {
        let key = self.builtin_key(fid);
        // Raw memory and C exist only where the program runs as machine code (§8.2).
        if self.prog.fns[fid].foreign || key.starts_with("Ptr.") || ["sizeOf", "alignOf", "zeroed", "fence", "fenceAcquire", "fenceRelease"].contains(&key.as_str()) {
            return Err(panic(format!("`{}` runs only in a native program", self.prog.fns[fid].name)));
        }
        let a = |i: usize| args.get(i).cloned().unwrap_or(Value::Unit);
        match key.as_str() {
            // ---- Option, Result, Fail ----
            "Option.isSome" => Ok(Value::Bool(matches!(a(0).deref(), Value::Tag(t, _) if &*t == "Some"))),
            "Option.take" => {
                let p = place_of(&a(0))?;
                let old = get(&p);
                set(&p, none());
                Ok(old)
            }
            "Option.unwrapOr" => match a(0).deref() {
                Value::Tag(t, payload) if &*t == "Some" => Ok(list(&payload).into_iter().next().unwrap_or(Value::Unit)),
                _ => Ok(a(1)),
            },
            "Option.cloned" => match a(0).deref() {
                Value::Tag(t, payload) if &*t == "Some" => Ok(some(list(&payload).into_iter().next().unwrap_or(Value::Unit).deref())),
                _ => Ok(none()),
            },
            "Result.unwrap" => match a(0).deref() {
                Value::Tag(t, payload) if &*t == "Ok" => Ok(list(&payload).into_iter().next().unwrap_or(Value::Unit)),
                Value::Tag(_, payload) => self.raise(list(&payload).into_iter().next().unwrap_or(Value::Unit)),
                other => Err(panic(format!("not a Result: {}", other.show()))),
            },
            "Fail.capture" => {
                let id = self.fresh_id();
                self.handlers.push(Handler::Fail { id });
                let r = self.call_value(&a(0), Vec::new());
                self.handlers.pop();
                match r {
                    Ok(v) => Ok(Value::tag("Ok", Value::Tuple(vec![v].into()))),
                    Err(Ctl::Unwind(h, e)) if h == id => Ok(Value::tag("Err", Value::Tuple(vec![e].into()))),
                    Err(e) => Err(e),
                }
            }
            "Fail.map" => {
                let id = self.fresh_id();
                self.handlers.push(Handler::Fail { id });
                let r = self.call_value(&a(0), Vec::new());
                self.handlers.pop();
                match r {
                    Err(Ctl::Unwind(h, e)) if h == id => {
                        let wrapped = self.call_value(&a(1), vec![e])?;
                        self.raise(wrapped)
                    }
                    other => other,
                }
            }

            // ---- structured concurrency ----
            "Io.scope" => {
                let sid = self.fresh_id();
                self.scopes.lock().expect("scopes").insert(sid, ScopeState { owner: self.task, ..Default::default() });
                let r = self.call_value(&a(0), vec![Value::Native("Scope", sid)]);
                // A panic ends the program at once, not waiting for the tasks (§5.7).
                if let Err(Ctl::Panic(m)) = &r
                    && !m.starts_with('\u{0}')
                {
                    self.sched.abort(m);
                    return r;
                }
                // The body unwound because a task failed: the scope rethrows that.
                let r = match r {
                    Err(Ctl::Cancelled) if self.scopes.lock().expect("scopes").get(&sid).is_some_and(|s| s.failure.is_some()) => {
                        self.sched.uncancel(self.task);
                        Ok(Value::Unit)
                    }
                    other => other,
                };
                // A scope returns only when every task started in it has finished (§6.1).
                let tasks = self.scopes.lock().expect("scopes").get(&sid).map(|s| s.tasks.clone()).unwrap_or_default();
                for t in tasks {
                    // A failing task cancels the body even while it waits here; it waits on.
                    loop {
                        match self.sched.join(self.task, t) {
                            Err(Ctl::Cancelled) => self.sched.uncancel(self.task),
                            other => break other?,
                        }
                    }
                }
                self.sched.uncancel(self.task);
                let st = self.scopes.lock().expect("scopes").remove(&sid).unwrap_or_default();
                match (r, st.failure) {
                    (Ok(_), Some(f)) => self.raise(f),
                    (r, _) => r,
                }
            }
            "Scope.spawn" | "Scope.fork" => {
                let sid = native(&a(0), "Scope")?;
                let forked = key == "Scope.fork";
                let tid = self.sched.spawn();
                self.scopes.lock().expect("scopes").entry(sid).or_default().tasks.push(tid);
                let mut child = self.fork_thread();
                child.task = tid;
                child.handlers.clear();
                let task = a(1);
                std::thread::spawn(move || {
                    // A task cancelled before it starts does not run, but still finishes.
                    let id = child.fresh_id();
                    let r = match child.sched.start(tid) {
                        Ok(()) => {
                            child.handlers.push(Handler::Fail { id });
                            let r = child.call_value(&task, Vec::new());
                            child.handlers.pop();
                            r
                        }
                        Err(e) => Err(e),
                    };
                    // A panic ends the program, every task with it (§5.7).
                    if let Err(Ctl::Panic(m)) = &r
                        && !m.starts_with('\u{0}')
                    {
                        child.sched.abort(m);
                    }
                    {
                        let mut scopes = child.scopes.lock().expect("scopes");
                        let st = scopes.entry(sid).or_default();
                        // The first failure cancels the scope: its body and other tasks.
                        let ends = matches!(&r, Err(Ctl::Unwind(h, _)) if *h == id);
                        if ends && st.failure.is_none() {
                            child.sched.cancel(st.owner);
                            for t in st.tasks.iter().filter(|t| **t != tid) {
                                child.sched.cancel(*t);
                            }
                        }
                        match r {
                            Ok(v) => {
                                st.fibers.insert(tid, Ok(v));
                            }
                            Err(Ctl::Unwind(h, e)) if h == id => {
                                st.failure.get_or_insert_with(|| e.clone());
                                st.fibers.insert(tid, Err(e));
                            }
                            Err(_) => {}
                        }
                    }
                    child.sched.finish(tid);
                });
                // Starting a task is a scheduling point.
                self.sched.yield_now(self.task)?;
                Ok(if forked { Value::Native("Fiber", tid) } else { Value::Unit })
            }
            "Fiber.join" => {
                let tid = native(&a(0), "Fiber")?;
                self.sched.join(self.task, tid)?;
                let outcome = self.scopes.lock().expect("scopes").values().find_map(|s| s.fibers.get(&tid).cloned());
                match outcome {
                    Some(Ok(v)) => Ok(v),
                    // The scope is cancelled; its first failure is rethrown (§6.1).
                    Some(Err(e)) => self.raise(e),
                    None => Err(panic("a joined task did not finish")),
                }
            }

            // ---- channels (§6.2) ----
            "channel" => {
                let ch = self.sched.channel();
                Ok(Value::Tuple(vec![Value::Native("Sender", ch), Value::Native("Receiver", ch)].into()))
            }
            "Reply.new" => {
                let ch = self.sched.channel();
                Ok(Value::Tuple(vec![Value::Native("Reply", ch), Value::Native("Pending", ch)].into()))
            }
            "Sender.send" | "Reply.send" => {
                let ch = match a(0).deref() {
                    Value::Native(_, ch) => ch,
                    other => return Err(panic(format!("not a sender: {}", other.show()))),
                };
                let rejected = self.sched.deliver(ch, a(1));
                let sent = rejected.is_none();
                if let Some((v, t)) = rejected {
                    self.drop_value(v, &t, &[])?;
                }
                // A reply sent is done with: its channel's sending end is gone.
                if key == "Reply.send" {
                    self.sched.sender_gone(ch);
                }
                self.sched.yield_now(self.task)?;
                Ok(if key == "Reply.send" { Value::Unit } else { Value::Bool(sent) })
            }
            // A dropped receiving end drops what is in its channel, and what is sent to it later:
            // a message may hold a reply someone waits for.
            "Receiver.drop" | "Pending.drop" => {
                let Value::Native(_, ch) = a(0).deref() else { return Ok(Value::Unit) };
                let Some(elem) = self.type_arg(fid, 0) else { return Ok(Value::Unit) };
                let mut result = Ok(Value::Unit);
                for m in self.sched.receiver_gone(ch, elem.clone()) {
                    if let Err(e) = self.drop_value(m, &elem, &[])
                        && result.is_ok() {
                            result = Err(e);
                        }
                }
                result
            }
            "Reply.drop" => {
                let ch = native(&a(0), "Reply")?;
                self.sched.sender_gone(ch);
                Ok(Value::Unit)
            }
            "Receiver.recv" => {
                let ch = native(&a(0), "Receiver")?;
                Ok(match self.sched.recv(self.task, ch)? {
                    Some(v) => some(v),
                    None => none(),
                })
            }
            "Pending.wait" => {
                let ch = native(&a(0), "Pending")?;
                self.sched.recv(self.task, ch)?.ok_or_else(|| panic("the reply was dropped unsent"))
            }
            "Gen.drop" => {
                if let Ok(id) = gens_mod::gen_id(&a(0)) {
                    gens_mod::drop_gen(self, id);
                }
                Ok(Value::Unit)
            }
            "Sender.clone" => {
                let ch = native(&a(0), "Sender")?;
                self.sched.add_sender(ch);
                Ok(Value::Native("Sender", ch))
            }
            // `std/par`'s two pure halves, here one after the other: the order cannot be seen (§6.5).
            "join" => {
                let x = self.call_value(&a(0), Vec::new())?;
                let y = self.call_value(&a(1), Vec::new())?;
                Ok(Value::Tuple(vec![x, y].into()))
            }
            // A mutex is a cell its clones share; `lock` lends the value to the body (§6.2).
            "Mutex.new" => Ok(Value::Ref(shared(a(0)))),
            "Mutex.lock" => {
                let root = match a(0).deref_once() {
                    Value::Ref(r) => r,
                    other => return Err(panic(format!("not a mutex: {}", other.show()))),
                };
                self.sched.yield_now(self.task)?;
                self.call_value(&a(1), vec![Value::Ptr(Place { root, path: Vec::new() })])
            }
            // An atomic is a cell its borrowers share; each operation is a scheduling point and
            // then takes effect whole, under the cell's lock (§6.2).
            "Atomic.new" => Ok(Value::Ref(shared(a(0)))),
            "Atomic.load" | "Atomic.store" | "Atomic.swap" | "Atomic.compareExchange" | "Atomic.fetchAdd" => {
                let root = match a(0).deref_once() {
                    Value::Ref(r) => r,
                    other => return Err(panic(format!("not an atomic: {}", other.show()))),
                };
                self.sched.yield_now(self.task)?;
                let mut cell = root.lock().unwrap();
                let old = cell.clone();
                match key.as_str() {
                    "Atomic.load" => Ok(old),
                    "Atomic.store" => {
                        *cell = a(1).deref();
                        Ok(Value::Unit)
                    }
                    "Atomic.swap" => {
                        *cell = a(1).deref();
                        Ok(old)
                    }
                    "Atomic.compareExchange" => {
                        let hit = old.equals(&a(1));
                        if hit {
                            *cell = a(2).deref();
                        }
                        Ok(Value::Tuple(vec![old, Value::Bool(hit)].into()))
                    }
                    _ => {
                        let sum = old.as_int() + a(1).as_int();
                        if sum < i64::MIN as i128 || sum > i64::MAX as i128 {
                            return Err(panic("arithmetic overflow"));
                        }
                        *cell = Value::Int(sum);
                        Ok(old)
                    }
                }
            }
            "Vec.drain" => {
                let p = place_of(&a(0))?;
                let items = list(&get(&p));
                set(&p, Value::List(Vec::new().into()));
                Ok(gens_mod::new_gen(self, GenKind::Items { items, pos: 0 }))
            }
            "Sender.close" => {
                let ch = native(&a(0), "Sender")?;
                self.sched.close(self.task, ch)?;
                Ok(Value::Unit)
            }
            "Sender.drop" => {
                let ch = native(&a(0), "Sender")?;
                self.sched.sender_gone(ch);
                Ok(Value::Unit)
            }
            "Receiver.each" => {
                let ch = native(&a(0), "Receiver")?;
                while let Some(v) = self.sched.recv(self.task, ch)? {
                    self.yield_value(v)?;
                }
                Ok(Value::Unit)
            }

            // ---- strings ----
            "String.new" => Ok(Value::text("")),
            "String.fromStr" | "str.toString" => Ok(Value::Text(a(0).as_text())),
            "String.len" | "str.len" => Ok(Value::Int(a(0).as_text().len() as i128)),
            "String.push" => {
                let p = place_of(&a(0))?;
                let tail = a(1).as_text();
                // In place, unless another value shares the string: pushing is amortized O(1).
                update(&p, |v| match v {
                    Value::Text(s) => std::sync::Arc::make_mut(s).push_str(&tail),
                    other => *other = Value::text(&format!("{}{}", other.as_text(), tail)),
                });
                Ok(Value::Unit)
            }
            "String.asStr" => Ok(Value::Text(a(0).as_text())),
            "String.clone" => Ok(Value::Text(a(0).as_text())),
            // A hasher is an FNV-1a state.
            "Hasher.new" => Ok(Value::Int(0xcbf29ce484222325)),
            "Hasher.writeInt" | "Hasher.writeFloat" | "Hasher.writeBool" | "Hasher.writeStr" => {
                let bytes: Vec<u8> = match a(1).deref() {
                    Value::Int(i) => (i as i64).to_le_bytes().to_vec(),
                    // As `Eq` sees floats: `-0.0` is `0.0`, and every `NaN` is one value.
                    Value::Float(f) => {
                        let f = if f == 0.0 { 0.0 } else if f.is_nan() { f64::NAN } else { f };
                        f.to_bits().to_le_bytes().to_vec()
                    }
                    Value::Bool(b) => vec![b as u8],
                    other => other.as_text().as_bytes().to_vec(),
                };
                let p = place_of(&a(0))?;
                let mut h = get(&p).as_int() as u64;
                for b in bytes {
                    h ^= b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
                set(&p, Value::Int(h as i128));
                Ok(Value::Unit)
            }
            "Hasher.finish" => Ok(Value::Int(a(0).deref().as_int() as u64 as i128)),
            "String.fromUtf8Lossy" => {
                let bytes: Vec<u8> = with_list(&a(0), |vs| vs.iter().map(|v| v.deref().as_int() as u8).collect());
                Ok(Value::text(&String::from_utf8_lossy(&bytes)))
            }
            "String.fromUtf8" => {
                let bytes: Vec<u8> = match a(0).deref() {
                    Value::List(vs) => vs.iter().map(|v| v.deref().as_int() as u8).collect(),
                    _ => Vec::new(),
                };
                Ok(match String::from_utf8(bytes) {
                    Ok(s) => some(Value::text(&s)),
                    Err(_) => none(),
                })
            }
            "str.slice" => {
                let s = a(0).as_text();
                let (lo, hi) = (a(1).as_int() as usize, a(2).as_int() as usize);
                match s.get(lo..hi) {
                    Some(t) => Ok(Value::text(t)),
                    None => Err(panic(format!("slice {lo}..{hi} is not on character boundaries of a string of {} bytes", s.len()))),
                }
            }
            "parseInt" => Ok(match a(0).as_text().parse::<i64>() {
                Ok(n) => some(Value::Int(n as i128)),
                Err(_) => none(),
            }),
            "parseFloat" => {
                let t = a(0).as_text();
                // Decimal text only: Rust also accepts `inf` and `NaN`.
                let decimal = t.bytes().all(|b| b.is_ascii_digit() || b"+-.eE".contains(&b)) && t.bytes().any(|b| b.is_ascii_digit());
                Ok(match t.parse::<f64>() {
                    Ok(x) if decimal => some(Value::Float(x)),
                    _ => none(),
                })
            }
            // The string itself: indexing it gives a byte, and its length is in bytes.
            "str.asBytes" => Ok(Value::Text(a(0).as_text())),
            "str.bytes" => {
                for b in a(0).as_text().bytes() {
                    self.yield_value(Value::Int(b as i128))?;
                }
                Ok(Value::Unit)
            }
            "str.split" => {
                let (s, sep) = (a(0).as_text(), a(1).as_text());
                Ok(Value::List(s.split(&*sep).map(Value::text).collect::<Vec<_>>().into()))
            }
            "str.trim" => Ok(Value::text(a(0).as_text().trim())),
            "str.includes" => Ok(Value::Bool(a(0).as_text().contains(&*a(1).as_text()))),
            "str.startsWith" => Ok(Value::Bool(a(0).as_text().starts_with(&*a(1).as_text()))),
            "str.endsWith" => Ok(Value::Bool(a(0).as_text().ends_with(&*a(1).as_text()))),
            "str.indexOf" => Ok(match a(0).as_text().find(&*a(1).as_text()) {
                Some(i) => some(Value::Int(i as i128)),
                None => none(),
            }),
            // ASCII letters only, as every back end does: other characters are themselves.
            "str.toUpperCase" => Ok(Value::text(&a(0).as_text().to_ascii_uppercase())),
            "str.toLowerCase" => Ok(Value::text(&a(0).as_text().to_ascii_lowercase())),
            "str.replaceAll" => Ok(Value::text(&a(0).as_text().replace(&*a(1).as_text(), &a(2).as_text()))),
            "str.lines" => {
                for l in a(0).as_text().lines() {
                    self.yield_value(Value::text(l))?;
                }
                Ok(Value::Unit)
            }
            "Vec.remove" | "Vec.insert" => {
                let p = place_of(&a(0))?;
                let mut items = list(&get(&p));
                let i = a(1).as_int() as usize;
                let limit = if key == "Vec.remove" { items.len() } else { items.len() + 1 };
                if i >= limit {
                    return Err(panic(format!("index {i} out of bounds for length {}", items.len())));
                }
                let out = if key == "Vec.remove" {
                    items.remove(i)
                } else {
                    items.insert(i, a(2));
                    Value::Unit
                };
                set(&p, Value::List(items.into()));
                Ok(out)
            }
            "Vec.truncate" => {
                let p = place_of(&a(0))?;
                let n = a(1).as_int().max(0) as usize;
                update(&p, |l| {
                    if let Value::List(vs) = l {
                        Arc::make_mut(vs).truncate(n);
                    }
                });
                Ok(Value::Unit)
            }
            "Vec.retain" => {
                let p = place_of(&a(0))?;
                let mut kept = Vec::new();
                for v in list(&get(&p)) {
                    if self.call_value(&a(1), vec![v.clone()])?.as_bool() {
                        kept.push(v);
                    }
                }
                set(&p, Value::List(kept.into()));
                Ok(Value::Unit)
            }
            "str.splitWhitespace" => {
                for w in a(0).as_text().split_whitespace() {
                    self.yield_value(Value::text(w))?;
                }
                Ok(Value::Unit)
            }

            // ---- collections ----
            "slice.len" | "Vec.len" => Ok(Value::Int(len_of(&a(0)) as i128)),
            "slice.iter" | "Vec.iter" => Ok(gens_mod::new_gen(self, GenKind::Items { items: list(&a(0)), pos: 0 })),
            // Each element as a place in the collection, so the loop body writes through it.
            "slice.iterMut" | "Vec.iterMut" => {
                let p = place_of(&a(0))?;
                let items = (0..list(&a(0)).len())
                    .map(|i| {
                        let mut q = p.clone();
                        q.path.push(Seg::Index(i));
                        Value::Ptr(q)
                    })
                    .collect();
                Ok(gens_mod::new_gen(self, GenKind::Items { items, pos: 0 }))
            }
            "slice.each" | "array.each" | "Vec.each" | "RegionList.each" => {
                for item in list(&a(0)) {
                    self.yield_value(item)?;
                }
                Ok(Value::Unit)
            }
            "Vec.new" => Ok(Value::List(Vec::new().into())),
            k if k.ends_with(".wrappingAdd") || k.ends_with(".wrappingSub") || k.ends_with(".wrappingMul") => {
                let (ty, op) = k.split_once('.').expect("a method key");
                let (x, y) = (a(0).as_int(), a(1).as_int());
                let r = match op {
                    "wrappingAdd" => x.wrapping_add(y),
                    "wrappingSub" => x.wrapping_sub(y),
                    _ => x.wrapping_mul(y),
                };
                Ok(Value::Int(wrap_to(ty, r)))
            }
            k if k.starts_with("f64.") || k.starts_with("f32.") => {
                let (ty, op) = k.split_once('.').expect("a method key");
                let x = a(0).as_float();
                if op == "toFixed" {
                    let digits = (a(1).as_int() as usize).min(100);
                    return Ok(Value::text(&format!("{x:.digits$}")));
                }
                let r = match op {
                    "sqrt" => x.sqrt(),
                    "abs" => x.abs(),
                    "floor" => x.floor(),
                    "ceil" => x.ceil(),
                    "round" => x.round(),
                    "trunc" => x.trunc(),
                    "sin" => x.sin(),
                    "cos" => x.cos(),
                    "tan" => x.tan(),
                    "exp" => x.exp(),
                    "ln" => x.ln(),
                    "atan2" => x.atan2(a(1).as_float()),
                    "pow" => x.powf(a(1).as_float()),
                    "min" => x.min(a(1).as_float()),
                    "max" => x.max(a(1).as_float()),
                    _ => return Err(panic(format!("no builtin `{k}`"))),
                };
                // An `f32` is an `f64` rounded to its precision.
                Ok(Value::Float(if ty == "f32" { r as f32 as f64 } else { r }))
            }
            "panic" => Err(panic(a(0).as_text().to_string())),
            "Ref.clone" | "Cell.clone" | "RegionList.clone" => Ok(a(0).deref_once()),
            "Ref.get" => Ok(a(0).deref()),
            "Vec.pop" => {
                let p = place_of(&a(0))?;
                let mut out = None;
                update(&p, |l| {
                    if let Value::List(vs) = l {
                        out = Arc::make_mut(vs).pop();
                    }
                });
                Ok(out.map_or_else(none, some))
            }
            "slice.reverse" => {
                let p = place_of(&a(0))?;
                update(&p, |l| {
                    if let Value::List(vs) = l {
                        Arc::make_mut(vs).reverse();
                    }
                });
                Ok(Value::Unit)
            }
            "slice.sortBy" => {
                let p = place_of(&a(0))?;
                let items = match get(&p).deref() {
                    Value::List(vs) => vs,
                    _ => return Err(panic("sortBy on something not a list")),
                };
                let sorted = merge_sort(self, Arc::unwrap_or_clone(items), &a(1))?;
                set(&p, Value::List(sorted.into()));
                Ok(Value::Unit)
            }
            "Vec.extend" => {
                let p = place_of(&a(0))?;
                let items: Vec<Value> = with_list(&a(1), |vs| vs.to_vec());
                update(&p, |l| {
                    if let Value::List(vs) = l {
                        Arc::make_mut(vs).extend(items);
                    }
                });
                Ok(Value::Unit)
            }
            "slice.copyFrom" => {
                let p = place_of(&a(0))?;
                let items: Vec<Value> = with_list(&a(1), |vs| vs.to_vec());
                let n = with_list(&get(&p), |vs| vs.len());
                if n != items.len() {
                    return Err(panic(format!("copyFrom: {} elements in place of {n}", items.len())));
                }
                set(&p, Value::List(items.into()));
                Ok(Value::Unit)
            }
            "Vec.push" => {
                let p = place_of(&a(0))?;
                let v = std::mem::replace(&mut args[1], Value::Unit);
                update(&p, |l| {
                    if let Value::List(vs) = l {
                        Arc::make_mut(vs).push(v);
                    }
                });
                Ok(Value::Unit)
            }
            "Box.new" | "Box.tryNew" | "Arc.new" | "Box.get" | "Arc.get" | "Box.into" => Ok(a(0).deref_once()),
            // The interpreter's memory is its own: room is always there.
            "String.tryReserve" | "Vec.tryReserve" | "HashMap.tryReserve" => Ok(Value::Unit),
            // The same shared value: through the borrow of the `Arc`, never into a cell it shares.
            "Arc.clone" => Ok(a(0).deref_once()),
            "HashMap.new" => Ok(Value::Map(Dict::default().into())),
            "HashMap.insert" => {
                let p = place_of(&a(0))?;
                let k = std::mem::replace(&mut args[1], Value::Unit).deref();
                let v = std::mem::replace(&mut args[2], Value::Unit);
                let mut old = None;
                update(&p, |m| {
                    if let Value::Map(d) = m {
                        old = Arc::make_mut(d).insert(k, v);
                    }
                });
                // The entry replaced is dropped, its key and its value.
                if let (Some(old), Some(kt), Some(vt)) = (old, self.type_arg(fid, 0), self.type_arg(fid, 1)) {
                    self.drop_value(old, &Ty::Tuple(vec![kt, vt]), &[])?;
                }
                Ok(Value::Unit)
            }
            "HashMap.get" | "HashMap.getMut" => {
                let p = place_of(&a(0))?;
                let key = a(1).deref();
                let found = view(&p, |m| match m {
                    Value::Map(d) => d.find(&key),
                    _ => None,
                });
                let Some(i) = found else { return Ok(none()) };
                let mut q = p.clone();
                q.path.extend([Seg::Index(i), Seg::Index(1)]);
                // A value lent where it is, unless it is `Copy`: a copy holds no loan (§4.4), so
                // the map may change while it lives.
                let copy = match self.call_span.and_then(|s| self.ty_of(s)).map(|t| self.frame_ty(&t)) {
                    Some(crate::check::types::Ty::Named(_, targs)) => match targs.first() {
                        Some(crate::check::types::GArg::Ty(crate::check::types::Ty::Borrow(false, inner))) => self.prog.is_copy(inner),
                        _ => false,
                    },
                    _ => false,
                };
                if self.builtin_key(fid) == "HashMap.getMut" || !copy {
                    Ok(some(Value::Ptr(q)))
                } else {
                    Ok(some(get(&q)))
                }
            }
            "HashMap.len" => Ok(Value::Int(map_len(&a(0)) as i128)),
            "HashMap.has" => {
                let key = a(1).deref();
                let p = place_of(&a(0))?;
                Ok(Value::Bool(view(&p, |m| matches!(m, Value::Map(d) if d.find(&key).is_some()))))
            }
            "HashMap.remove" => {
                let p = place_of(&a(0))?;
                let key = a(1).deref();
                let mut removed = none();
                update(&p, |m| {
                    if let Value::Map(d) = m
                        && let Some(v) = Arc::make_mut(d).remove(&key) {
                            removed = some(v);
                        }
                });
                Ok(removed)
            }
            "HashMap.keys" | "HashMap.values" | "HashMap.entries" | "HashMap.valuesMut" => {
                let p = place_of(&a(0))?;
                let n = view(&p, |m| match m {
                    Value::Map(d) => d.len(),
                    _ => 0,
                });
                let key = self.builtin_key(fid);
                // Each item lent where it is in the map.
                let at = |i: usize, j: usize| {
                    let mut q = p.clone();
                    q.path.extend([Seg::Index(i), Seg::Index(j)]);
                    Value::Ptr(q)
                };
                let items = (0..n)
                    .map(|i| match key.as_str() {
                        "HashMap.keys" => at(i, 0),
                        "HashMap.values" | "HashMap.valuesMut" => at(i, 1),
                        _ => Value::Tuple(vec![at(i, 0), at(i, 1)].into()),
                    })
                    .collect();
                Ok(gens_mod::new_gen(self, GenKind::Items { items, pos: 0 }))
            }
            "HashMap.intoEntries" => {
                let entries: Vec<Value> = match a(0).deref() {
                    Value::Map(d) => d.entries.iter().map(|e| Value::Tuple(vec![entry(e).0.clone(), entry(e).1.clone()].into())).collect(),
                    _ => Vec::new(),
                };
                Ok(Value::List(entries.into()))
            }

            // ---- regions (§4.6) ----
            "alloc" => Ok(Value::Ref(shared(a(0)))),
            "allocAll" => Ok(Value::Ref(shared(Value::List(list(&a(0)).into())))),
            "replace" => {
                let p = place_of(&a(0))?;
                let old = get(&p);
                set(&p, a(1));
                Ok(old)
            }
            "swap" => {
                let (p, q) = (place_of(&a(0))?, place_of(&a(1))?);
                let (x, y) = (get(&p), get(&q));
                set(&p, y);
                set(&q, x);
                Ok(Value::Unit)
            }
            "fmt" => Ok(Value::Ref(shared(Value::Text(a(0).as_text())))),
            "copyUtf8" => {
                let bytes: Vec<u8> = list(&a(0)).iter().map(|b| b.as_int() as u8).collect();
                match String::from_utf8(bytes) {
                    Ok(s) => Ok(Value::Ref(shared(Value::text(&s)))),
                    Err(_) => self.raise(Value::tag("MalformedUtf8", Value::Unit)),
                }
            }
            "repeat" => Ok(Value::List(vec![a(0); self.expected_len().unwrap_or(0)].into())),
            "Cell.new" => Ok(Value::Cell(shared(a(0)))),
            "Cell.get" => match a(0) {
                Value::Cell(c) => Ok(c.lock().expect("cell").clone()),
                other => Ok(other.deref()),
            },
            "Cell.set" => {
                if let Value::Cell(c) = a(0) {
                    *c.lock().expect("cell") = a(1);
                }
                Ok(Value::Unit)
            }
            "RegionList.new" => Ok(Value::Cell(shared(Value::List(Vec::new().into())))),
            "RegionList.push" => {
                if let Value::Cell(c) = a(0).deref_handle()
                    && let Value::List(vs) = &mut *c.lock().expect("cell") {
                        Arc::make_mut(vs).push(a(1));
                    }
                Ok(Value::Unit)
            }
            "RegionList.len" => Ok(Value::Int(with_list(&a(0), <[Value]>::len) as i128)),

            // ---- generators ----
            "generate" => Ok(gens_mod::generate(self, a(0))),
            "Gen.next" => {
                let id = gens_mod::gen_id(&a(0))?;
                Ok(match gens_mod::next(self, id)? {
                    Some(v) => some(v),
                    None => none(),
                })
            }
            "Gen.map" => Ok(gens_mod::new_gen(self, GenKind::Map { inner: gens_mod::gen_id(&a(0))?, f: a(1) })),
            "Gen.filter" => Ok(gens_mod::new_gen(self, GenKind::Filter { inner: gens_mod::gen_id(&a(0))?, f: a(1) })),
            "Gen.take" => Ok(gens_mod::new_gen(self, GenKind::Take { inner: gens_mod::gen_id(&a(0))?, left: a(1).as_int() as usize })),
            "Gen.zip" => Ok(gens_mod::new_gen(self, GenKind::Zip { a: gens_mod::gen_id(&a(0))?, b: gens_mod::gen_id(&a(1))? })),
            "Gen.enumerate" => Ok(gens_mod::new_gen(self, GenKind::Enumerate { inner: gens_mod::gen_id(&a(0))?, n: 0 })),
            "Gen.collect" => {
                let id = gens_mod::gen_id(&a(0))?;
                let mut out = Vec::new();
                while let Some(v) = gens_mod::next(self, id)? {
                    out.push(v);
                }
                Ok(Value::List(out.into()))
            }
            "Gen.each" => {
                let id = gens_mod::gen_id(&a(0))?;
                while let Some(v) = gens_mod::next(self, id)? {
                    self.yield_value(v)?;
                }
                Ok(Value::Unit)
            }

            // ---- slices as `ParSplit` (§6.5): views are places in the slice ----
            "slice.slice" | "array.slice" | "Vec.slice" => Ok(Value::Ptr(place_of(&a(0))?)),
            "array.len" => Ok(Value::Int(with_list(&a(0), <[Value]>::len) as i128)),
            "slice.split" | "array.split" | "Vec.split" | "slice.splitAt" => {
                let p = place_of(&a(0))?;
                let n = list(&Value::Ptr(p.clone())).len();
                let at = (a(1).as_int() as usize).min(n);
                // A part of a part is one range of the original.
                let half = |lo: usize, hi: usize| {
                    let mut q = p.clone();
                    match q.path.last_mut() {
                        Some(Seg::Range(l0, h0)) => {
                            let l = *l0;
                            *l0 = l + lo;
                            *h0 = l + hi;
                        }
                        _ => q.path.push(Seg::Range(lo, hi)),
                    }
                    Value::Ptr(q)
                };
                Ok(Value::Tuple(vec![half(0, at), half(at, n)].into()))
            }
            "slice.viewAt" | "slice.readAt" | "array.viewAt" | "array.readAt" | "Vec.viewAt" | "Vec.readAt" => {
                let mut p = place_of(&a(0))?;
                p.path.push(Seg::Index(a(1).as_int() as usize));
                Ok(Value::Ptr(p))
            }

            // ---- I/O against the world (§6.4) ----
            "println" => {
                let s = a(0).as_text().to_string();
                self.world.lock().expect("world").out.push(s);
                Ok(Value::Unit)
            }
            // Standard error is not the world's output: it goes straight out.
            "eprintln" => {
                eprintln!("{}", a(0).as_text());
                Ok(Value::Unit)
            }
            // The program ends at once, as for a panic, but with the status asked for.
            "exit" => {
                self.world.lock().expect("world").exit = Some(a(0).as_int() as i32);
                Err(panic(EXITED))
            }
            // A descriptor let go of, as a dropped file does.
            "Fd.release" => {
                if let Value::Record(fs) = a(0).deref() {
                    let n = fs.get("n").map_or(0, |n| n.as_int() as u32);
                    self.world.lock().expect("world").fds.remove(&n);
                }
                Ok(Value::Unit)
            }
            // `std/crypto`: OpenSSL's libcrypto, as natively.
            "sha256" | "sha384" | "sha512" | "hmacSha256" | "hmacSha512" | "hkdfSha256" | "aesGcmSeal" | "aesGcmOpen" | "ed25519PublicKey" | "ed25519Sign" | "ed25519Verify" | "constantTimeEqual" => {
                use super::crypto;
                let b = |i: usize| -> Vec<u8> { with_list(&a(i), |vs| vs.iter().map(|v| v.as_int() as u8).collect()) };
                let list = |v: Vec<u8>| Value::List(v.into_iter().map(|x| Value::Int(x as i128)).collect::<Vec<_>>().into());
                let r = match key.as_str() {
                    "sha256" => crypto::digest(256, &b(0)).map(list),
                    "sha384" => crypto::digest(384, &b(0)).map(list),
                    "sha512" => crypto::digest(512, &b(0)).map(list),
                    "hmacSha256" => crypto::hmac(256, &b(0), &b(1)).map(list),
                    "hmacSha512" => crypto::hmac(512, &b(0), &b(1)).map(list),
                    "hkdfSha256" => crypto::hkdf(&b(0), &b(1), &b(2), a(3).as_int() as usize).map(list),
                    "aesGcmSeal" => crypto::gcm(true, &b(0), &b(1), &b(2), &b(3)).map(|v| list(v.unwrap_or_default())),
                    "aesGcmOpen" => crypto::gcm(false, &b(0), &b(1), &b(2), &b(3)).map(|v| v.map_or_else(none, |v| some(list(v)))),
                    "ed25519PublicKey" => crypto::ed25519(&b(0), None).map(list),
                    "ed25519Sign" => crypto::ed25519(&b(0), Some(&b(1))).map(list),
                    "ed25519Verify" => crypto::ed25519_verify(&b(0), &b(1), &b(2)).map(Value::Bool),
                    _ => {
                        let (x, y) = (b(0), b(1));
                        Ok(Value::Bool(x.len() == y.len() && x.iter().zip(&y).fold(0u8, |d, (p, q)| d | (p ^ q)) == 0))
                    }
                };
                r.map_err(panic)
            }
            "Listener.bind" => Ok(Value::Native("Listener", a(0).as_int() as u64)),
            "Listener.port" => Ok(Value::Int(native(&a(0), "Listener")? as i128)),
            "Listener.accept" => loop {
                let next = self.world.lock().expect("world").incoming.pop_front();
                let Some(input) = next else { return Ok(Value::Unit) };
                let id = self.world.lock().expect("world").open_socket(input);
                self.yield_value(Value::Native("Socket", id))?;
            },
            // A simulated world's peers answer in the clear, as if TLS were there.
            "Socket.connect" | "Socket.connectTls" => {
                let peer = format!("{}:{}", a(0).as_text(), a(1).as_int());
                let mut w = self.world.lock().expect("world");
                if w.fault() {
                    drop(w);
                    return self.raise(Value::tag("TimedOut", Value::Unit));
                }
                let Some(input) = w.peers.get(&peer).cloned() else {
                    drop(w);
                    return self.raise(Value::tag("Refused", Value::Unit));
                };
                let id = w.open_socket(input);
                w.sockets[id as usize].peer = Some(peer);
                Ok(Value::Native("Socket", id))
            }
            "Socket.read" => {
                let id = native(&a(0), "Socket")? as usize;
                if self.world.lock().expect("world").fault() {
                    return self.raise(Value::tag("TimedOut", Value::Unit));
                }
                let buf = place_of(&a(1))?;
                let mut target = get(&buf);
                let n = {
                    let mut w = self.world.lock().expect("world");
                    let sock = &mut w.sockets[id];
                    let Value::List(cells) = &mut target else { return Err(panic("read into a non-buffer")) };
                    let n = cells.len().min(sock.input.len() - sock.pos);
                    for (i, cell) in Arc::make_mut(cells).iter_mut().enumerate().take(n) {
                        *cell = Value::Int(sock.input[sock.pos + i] as i128);
                    }
                    sock.pos += n;
                    n
                };
                set(&buf, target);
                Ok(Value::Int(n as i128))
            }
            "Socket.writeStatus" => {
                let id = native(&a(0), "Socket")? as usize;
                if self.world.lock().expect("world").fault() {
                    return self.raise(Value::tag("BrokenPipe", Value::Unit));
                }
                let (code, body) = (a(1).as_int() as u16, a(2).as_text().to_string());
                let mut w = self.world.lock().expect("world");
                // The simulated client's transcript doubles as the program's output.
                w.out.push(format!("-> {code} {body}"));
                w.sockets[id].written.push((code, body));
                Ok(Value::Unit)
            }
            "Socket.write" => {
                let id = native(&a(0), "Socket")? as usize;
                if self.world.lock().expect("world").fault() {
                    return self.raise(Value::tag("BrokenPipe", Value::Unit));
                }
                let bytes: Vec<u8> = with_list(&a(1), |vs| vs.iter().map(|v| v.as_int() as u8).collect());
                self.world.lock().expect("world").sockets[id].bytes.extend(bytes);
                Ok(Value::Unit)
            }
            // What was written to the simulated client is the program's output, once it is all
            // there: one line of it, `\r\n` shown as a line break.
            "Socket.close" => {
                let id = native(&a(0), "Socket")? as usize;
                let mut w = self.world.lock().expect("world");
                let bytes = std::mem::take(&mut w.sockets[id].bytes);
                if !bytes.is_empty() {
                    let text = String::from_utf8_lossy(&bytes).replace("\r\n", "\n");
                    let to = w.sockets[id].peer.as_ref().map(|p| format!("{p}: ")).unwrap_or_default();
                    w.out.push(format!("-> {to}{}", text.trim_end_matches('\n')));
                }
                Ok(Value::Unit)
            }
            "Db.connect" => Ok(Value::Native("Db", 0)),
            "Db.fetchProfile" => {
                let user = a(1).as_text().to_string();
                let mut w = self.world.lock().expect("world");
                if w.fault() {
                    drop(w);
                    return self.raise(Value::tag("TimedOut", Value::Unit));
                }
                match w.profiles.get(&user).cloned() {
                    Some(name) => Ok(Value::Record([("displayName".to_string(), Value::text(&name))].into_iter().collect::<BTreeMap<_, _>>().into())),
                    None => {
                        drop(w);
                        self.raise(Value::tag("NotFound", Value::Unit))
                    }
                }
            }
            "Db.checkQuota" => {
                let token = a(1).as_text().to_string();
                let mut w = self.world.lock().expect("world");
                if w.fault() {
                    drop(w);
                    return self.raise(Value::tag("TimedOut", Value::Unit));
                }
                let allowed = w.quotas.get(&token).copied().unwrap_or(false);
                Ok(Value::Record([("allowed".to_string(), Value::Bool(allowed))].into_iter().collect::<BTreeMap<_, _>>().into()))
            }
            other => Err(panic(format!("no native implementation of `{other}` yet"))),
        }
    }
}

impl Value {
    /// A region handle, seen through a borrow if it arrived as one.
    fn deref_handle(&self) -> Value {
        match self {
            Value::Ptr(p) => get(p).deref_handle(),
            v => v.clone(),
        }
    }
}

/// A stable merge sort whose comparison is Flyscript code, which may fail.
fn merge_sort(it: &mut Interp, v: Vec<Value>, cmp: &Value) -> Result<Vec<Value>, Ctl> {
    if v.len() <= 1 {
        return Ok(v);
    }
    let mut left = v;
    let right = left.split_off(left.len() / 2);
    let (left, right) = (merge_sort(it, left, cmp)?, merge_sort(it, right, cmp)?);
    let mut out = Vec::with_capacity(left.len() + right.len());
    let (mut l, mut r) = (left.into_iter().peekable(), right.into_iter().peekable());
    while let (Some(a), Some(b)) = (l.peek(), r.peek()) {
        // Only a strictly smaller right element goes first, which keeps equal ones in order.
        let less = matches!(it.call_value(cmp, vec![b.clone(), a.clone()])?.deref(), Value::Tag(t, _) if &*t == "Less");
        out.push(if less { r.next() } else { l.next() }.expect("peeked"));
    }
    out.extend(l);
    out.extend(r);
    Ok(out)
}

/// Wraps an integer into the range of the named type, two's complement.
fn wrap_to(ty: &str, i: i128) -> i128 {
    match ty {
        "u8" => i & 0xff,
        "u16" => i & 0xffff,
        "u32" => i & 0xffff_ffff,
        "u64" | "usize" => i & 0xffff_ffff_ffff_ffff,
        "i8" => i as i8 as i128,
        "i16" => i as i16 as i128,
        "i32" => i as i32 as i128,
        "i128" => i,
        _ => i as i64 as i128,
    }
}
