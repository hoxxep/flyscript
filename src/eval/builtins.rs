//! The native bodies of the standard library's declarations (`std/*.d.fly`).

use std::collections::HashMap;

use super::generators::{self as gens_mod, GenKind};
use super::interp::{Ctl, Handler, Interp, R, panic};
use super::value::*;
use crate::check::env::FnId;
use crate::check::types::{Prim, Ty};

/// A structured-concurrency scope (§6.1). Tasks run to completion when started, in order, which
/// keeps runs deterministic; a forked task's failure is rethrown by the scope.
#[derive(Default)]
pub struct ScopeState {
    pub failure: Option<Value>,
    pub panic: Option<String>,
    /// Every task started in the scope; the scope waits for all of them.
    pub tasks: Vec<u64>,
    /// Forked tasks' outcomes, by task.
    pub fibers: HashMap<u64, Result<Value, Value>>,
}

fn none() -> Value {
    Value::tag("None", Value::Unit)
}

fn some(v: Value) -> Value {
    Value::tag("Some", Value::Tuple(vec![v]))
}

fn place_of(v: &Value) -> Result<Place, Ctl> {
    match v {
        Value::Ptr(p) => Ok(p.clone()),
        Value::Ref(r) => Ok(Place { root: r.clone(), path: Vec::new() }),
        other => Ok(Place { root: shared(other.clone()), path: Vec::new() }),
    }
}

fn native(v: &Value, kind: &str) -> Result<u64, Ctl> {
    match v.deref() {
        Value::Native(k, id) if k == kind => Ok(id),
        other => Err(panic(format!("expected a {kind}, found {}", other.show()))),
    }
}

fn list(v: &Value) -> Vec<Value> {
    match v.deref() {
        Value::List(vs) | Value::Tuple(vs) => vs,
        Value::Cell(c) => match &*c.lock().expect("cell") {
            Value::List(vs) => vs.clone(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
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
            Ty::Slice(_) => "slice".into(),
            Ty::Union(r) if r.labels.contains_key("Some") => "Option".into(),
            Ty::Union(r) if r.labels.contains_key("Ok") => "Result".into(),
            _ => "?".into(),
        };
        format!("{target}.{}", info.name)
    }

    pub fn builtin(&mut self, fid: FnId, args: Vec<Value>) -> R {
        let key = self.builtin_key(fid);
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
                    Ok(v) => Ok(Value::tag("Ok", Value::Tuple(vec![v]))),
                    Err(Ctl::Unwind(h, e)) if h == id => Ok(Value::tag("Err", Value::Tuple(vec![e]))),
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
                self.scopes.lock().expect("scopes").insert(sid, ScopeState::default());
                let r = self.call_value(&a(0), vec![Value::Native("Scope", sid)]);
                // A scope returns only when every task started in it has finished (§6.1).
                let tasks = self.scopes.lock().expect("scopes").get(&sid).map(|s| s.tasks.clone()).unwrap_or_default();
                for t in tasks {
                    self.sched.join(self.task, t)?;
                }
                let st = self.scopes.lock().expect("scopes").remove(&sid).unwrap_or_default();
                if let Some(p) = st.panic {
                    return Err(panic(p));
                }
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
                    if child.sched.start(tid).is_err() {
                        return;
                    }
                    let id = child.fresh_id();
                    child.handlers.push(Handler::Fail { id });
                    let r = child.call_value(&task, Vec::new());
                    child.handlers.pop();
                    {
                        let mut scopes = child.scopes.lock().expect("scopes");
                        let st = scopes.entry(sid).or_default();
                        match r {
                            Ok(v) => {
                                st.fibers.insert(tid, Ok(v));
                            }
                            Err(Ctl::Unwind(h, e)) if h == id => {
                                st.failure.get_or_insert_with(|| e.clone());
                                st.fibers.insert(tid, Err(e));
                            }
                            Err(Ctl::Panic(m)) => {
                                st.panic.get_or_insert(m);
                            }
                            Err(other) => {
                                st.panic.get_or_insert(format!("{other:?}"));
                            }
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
                Ok(Value::Tuple(vec![Value::Native("Sender", ch), Value::Native("Receiver", ch)]))
            }
            "Reply.new" => {
                let ch = self.sched.channel();
                Ok(Value::Tuple(vec![Value::Native("Reply", ch), Value::Native("Pending", ch)]))
            }
            "Sender.send" | "Reply.send" => {
                let ch = match a(0).deref() {
                    Value::Native(_, ch) => ch,
                    other => return Err(panic(format!("not a sender: {}", other.show()))),
                };
                self.sched.send(self.task, ch, a(1))?;
                Ok(Value::Unit)
            }
            "Pending.wait" | "Receiver.recv" => {
                let ch = match a(0).deref() {
                    Value::Native(_, ch) => ch,
                    other => return Err(panic(format!("not a receiver: {}", other.show()))),
                };
                self.sched.recv(self.task, ch)
            }
            "Receiver.each" => {
                let ch = native(&a(0), "Receiver")?;
                loop {
                    let v = self.sched.recv(self.task, ch)?;
                    self.yield_value(v)?;
                }
            }

            // ---- strings ----
            "String.new" => Ok(Value::text("")),
            "String.fromStr" | "str.toString" => Ok(Value::Text(a(0).as_text())),
            "String.len" | "str.len" => Ok(Value::Int(a(0).as_text().len() as i128)),
            "String.push" => {
                let p = place_of(&a(0))?;
                let s = format!("{}{}", get(&p).as_text(), a(1).as_text());
                set(&p, Value::text(&s));
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
            "str.asBytes" => Ok(Value::List(a(0).as_text().bytes().map(|b| Value::Int(b as i128)).collect())),
            "str.bytes" => {
                for b in a(0).as_text().bytes() {
                    self.yield_value(Value::Int(b as i128))?;
                }
                Ok(Value::Unit)
            }
            "str.splitWhitespace" => {
                for w in a(0).as_text().split_whitespace() {
                    self.yield_value(Value::text(w))?;
                }
                Ok(Value::Unit)
            }

            // ---- collections ----
            "slice.len" | "Vec.len" | "Soa.len" => Ok(Value::Int(list(&a(0)).len() as i128)),
            "slice.iter" | "Vec.iter" => Ok(gens_mod::new_gen(self, GenKind::Items { items: list(&a(0)), pos: 0 })),
            "slice.each" | "Vec.each" | "RegionList.each" => {
                for item in list(&a(0)) {
                    self.yield_value(item)?;
                }
                Ok(Value::Unit)
            }
            "Vec.new" | "Soa.new" => Ok(Value::List(Vec::new())),
            "Vec.push" | "Soa.push" => {
                let p = place_of(&a(0))?;
                let v = a(1);
                update(&p, |l| {
                    if let Value::List(vs) = l {
                        vs.push(v);
                    }
                });
                Ok(Value::Unit)
            }
            "Box.new" | "Arc.new" | "Box.get" | "Arc.get" => Ok(a(0)),
            "Arc.clone" => Ok(a(0).deref()),
            "HashMap.new" => Ok(Value::List(Vec::new())),
            "HashMap.insert" => {
                let p = place_of(&a(0))?;
                let (k, v) = (a(1), a(2));
                update(&p, |m| {
                    if let Value::List(entries) = m {
                        match entries.iter_mut().find(|e| matches!(e, Value::Tuple(kv) if kv[0].equals(&k))) {
                            Some(Value::Tuple(kv)) => kv[1] = v,
                            _ => entries.push(Value::Tuple(vec![k, v])),
                        }
                    }
                });
                Ok(Value::Unit)
            }
            "HashMap.get" | "HashMap.getMut" => {
                let p = place_of(&a(0))?;
                let key = a(1);
                let entries = list(&Value::Ptr(p.clone()));
                match entries.iter().position(|e| matches!(e, Value::Tuple(kv) if kv[0].equals(&key))) {
                    Some(i) if key.deref().equals(&key) && self.builtin_key(fid) == "HashMap.getMut" => {
                        let mut q = p.clone();
                        q.path.extend([Seg::Index(i), Seg::Index(1)]);
                        Ok(some(Value::Ptr(q)))
                    }
                    Some(i) => Ok(some(list(&entries[i])[1].clone())),
                    None => Ok(none()),
                }
            }
            "HashMap.sortedByValue" => {
                let mut entries: Vec<(Value, Value)> = list(&a(0))
                    .into_iter()
                    .map(|e| {
                        let kv = list(&e);
                        (kv[0].clone(), kv[1].clone())
                    })
                    .collect();
                entries.sort_by(|(k1, v1), (k2, v2)| {
                    v2.as_int().cmp(&v1.as_int()).then_with(|| k1.as_text().cmp(&k2.as_text()))
                });
                Ok(Value::List(entries.into_iter().map(|(k, v)| Value::Tuple(vec![k, v])).collect()))
            }

            // ---- regions (§4.6) ----
            "alloc" => Ok(Value::Ref(shared(a(0)))),
            "fmt" => Ok(Value::Ref(shared(Value::Text(a(0).as_text())))),
            "copyUtf8" => {
                let bytes: Vec<u8> = list(&a(0)).iter().map(|b| b.as_int() as u8).collect();
                match String::from_utf8(bytes) {
                    Ok(s) => Ok(Value::Ref(shared(Value::text(&s)))),
                    Err(_) => self.raise(Value::tag("MalformedUtf8", Value::Unit)),
                }
            }
            "repeat" => Ok(Value::List(vec![a(0); self.expected_len().unwrap_or(0)])),
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
            "RegionList.new" => Ok(Value::Cell(shared(Value::List(Vec::new())))),
            "RegionList.push" => {
                if let Value::Cell(c) = a(0).deref_handle()
                    && let Value::List(vs) = &mut *c.lock().expect("cell") {
                        vs.push(a(1));
                    }
                Ok(Value::Unit)
            }
            "RegionList.len" => Ok(Value::Int(list(&a(0)).len() as i128)),

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
                Ok(Value::List(out))
            }
            "Gen.each" => {
                let id = gens_mod::gen_id(&a(0))?;
                while let Some(v) = gens_mod::next(self, id)? {
                    self.yield_value(v)?;
                }
                Ok(Value::Unit)
            }

            // ---- data parallelism (§6.5), run in order ----
            "par" => {
                let p = place_of(&a(0))?;
                let n = list(&Value::Ptr(p.clone())).len();
                for i in 0..n {
                    let mut q = p.clone();
                    q.path.push(Seg::Index(i));
                    self.call_value(&a(1), vec![Value::Ptr(q), Value::Int(i as i128)])?;
                }
                Ok(Value::Unit)
            }
            "parReduce" => {
                let mut acc = a(1);
                for (i, item) in list(&a(0)).into_iter().enumerate() {
                    let one = self.call_value(&a(2), vec![item, Value::Int(i as i128)])?;
                    acc = self.call_value(&a(3), vec![acc, one])?;
                }
                Ok(acc)
            }

            // ---- I/O against the world (§6.4) ----
            "println" => {
                let s = a(0).as_text().to_string();
                self.world.lock().expect("world").out.push(s);
                Ok(Value::Unit)
            }
            "File.open" => {
                let path = a(0).as_text().to_string();
                let mut w = self.world.lock().expect("world");
                match w.files.get(&path).cloned() {
                    Some(content) => {
                        let id = w.open_socket(content.into_bytes());
                        Ok(Value::Native("File", id))
                    }
                    None => {
                        drop(w);
                        self.raise(Value::tag("NotFound", Value::Unit))
                    }
                }
            }
            "File.lines" => {
                let id = native(&a(0), "File")? as usize;
                let content = String::from_utf8_lossy(&self.world.lock().expect("world").sockets[id].input).to_string();
                for line in content.lines() {
                    self.yield_value(Value::text(line))?;
                }
                Ok(Value::Unit)
            }
            "Listener.bind" => Ok(Value::Native("Listener", 0)),
            "Listener.accept" => loop {
                let next = self.world.lock().expect("world").incoming.pop_front();
                let Some(input) = next else { return Ok(Value::Unit) };
                let id = self.world.lock().expect("world").open_socket(input);
                self.yield_value(Value::Native("Socket", id))?;
            },
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
                    for (i, cell) in cells.iter_mut().enumerate().take(n) {
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
            "Socket.close" => Ok(Value::Unit),
            "Db.connect" => Ok(Value::Native("Db", 0)),
            "Db.fetchProfile" => {
                let user = a(1).as_text().to_string();
                let mut w = self.world.lock().expect("world");
                if w.fault() {
                    drop(w);
                    return self.raise(Value::tag("TimedOut", Value::Unit));
                }
                match w.profiles.get(&user).cloned() {
                    Some(name) => Ok(Value::Record([("displayName".to_string(), Value::text(&name))].into_iter().collect())),
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
                Ok(Value::Record([("allowed".to_string(), Value::Bool(allowed))].into_iter().collect()))
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
