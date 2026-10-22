//! Generators as values (§5.5).
//!
//! A `Gen` built by `generate(f)` holds a suspended computation: `f` runs on its own thread and
//! hands each item to the consumer, which resumes it with `next()`. This is the one place the
//! evaluator needs a stored continuation. Effects the generator performs other than `Yield`
//! go to whoever resumes it (§5.3): a failure surfaces from `next()`. Chains (`map`, `filter`,
//! `take`, `zip`, `enumerate`) and iteration over a collection pull lazily in the consumer's
//! own thread and need no thread at all.

use std::collections::HashMap;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::sync::{Arc, Mutex};

use super::interp::{Ctl, Handler, Interp, panic};
use super::value::*;

pub enum Cmd {
    Next,
}

pub enum Evt {
    Item(Value),
    Done,
    Failed(Value),
    Panicked(String),
}

/// What a `Gen` value pulls from.
pub enum GenKind {
    Thread { to: Sender<Cmd>, from: Arc<Mutex<Receiver<Evt>>>, started: bool },
    Items { items: Vec<Value>, pos: usize },
    Map { inner: u64, f: Value },
    Filter { inner: u64, f: Value },
    Take { inner: u64, left: usize },
    Zip { a: u64, b: u64 },
    Enumerate { inner: u64, n: usize },
    Done,
}

/// The producer's side of a threaded generator.
struct Producer {
    to: Sender<Evt>,
    from: Arc<Mutex<Receiver<Cmd>>>,
}

#[derive(Default)]
pub struct Gens {
    consumers: Mutex<HashMap<u64, GenKind>>,
    producers: Mutex<HashMap<u64, Producer>>,
}

pub fn new_gen(it: &Interp, kind: GenKind) -> Value {
    let id = it.fresh_id();
    it.gens.consumers.lock().expect("gens").insert(id, kind);
    Value::Native("Gen", id)
}

pub fn gen_id(v: &Value) -> Result<u64, Ctl> {
    match v.deref() {
        Value::Native("Gen", id) => Ok(id),
        other => Err(panic(format!("{} is not a generator", other.show()))),
    }
}

/// `generate(f)`: runs `f` on its own thread, suspended at each `yield`.
pub fn generate(it: &Interp, f: Value) -> Value {
    let (to_gen, gen_rx) = channel::<Cmd>();
    let (gen_tx, from_gen) = channel::<Evt>();
    let id = it.fresh_id();
    it.gens.producers.lock().expect("gens").insert(id, Producer { to: gen_tx.clone(), from: Arc::new(Mutex::new(gen_rx)) });
    let mut child = it.fork_thread();
    std::thread::spawn(move || {
        let from = child.gens.producers.lock().expect("gens").get(&id).map(|p| p.from.clone());
        let Some(from) = from else { return };
        // Wait to be started by the first `next()`.
        if from.lock().expect("rx").recv().is_err() {
            return;
        }
        child.handlers = vec![Handler::GenYield { generator: id }];
        let evt = match child.call_value(&f, Vec::new()) {
            Ok(_) => Some(Evt::Done),
            Err(Ctl::Panic(m)) if m == FAILED => None,
            // Unwound because the generator was dropped: say so, so the drop can go on.
            Err(Ctl::Panic(m)) if m == CANCELLED => Some(Evt::Done),
            Err(Ctl::Panic(m)) => Some(Evt::Panicked(m)),
            Err(other) => Some(Evt::Panicked(format!("{other:?}"))),
        };
        child.gens.producers.lock().expect("gens").remove(&id);
        if let Some(evt) = evt {
            let _ = gen_tx.send(evt);
        }
    });
    it.gens.consumers.lock().expect("gens").insert(id, GenKind::Thread { to: to_gen, from: Arc::new(Mutex::new(from_gen)), started: false });
    Value::Native("Gen", id)
}

const FAILED: &str = "\u{0}generator failed";
const CANCELLED: &str = "\u{0}generator cancelled";

/// On a generator's thread: hand an item to the consumer and wait to be resumed.
pub fn hand_over(it: &mut Interp, generator: u64, v: Value) -> Result<Value, Ctl> {
    let (to, from) = {
        let producers = it.gens.producers.lock().expect("gens");
        let p = producers.get(&generator).ok_or_else(|| panic("generator gone"))?;
        (p.to.clone(), p.from.clone())
    };
    to.send(Evt::Item(v)).map_err(|_| panic(CANCELLED))?;
    match from.lock().expect("rx").recv() {
        Ok(Cmd::Next) => Ok(Value::Unit),
        // The consumer dropped the generator: unwind it, running its cleanup.
        Err(_) => Err(panic(CANCELLED)),
    }
}

/// On a generator's thread: a failure nothing inside handled goes to the consumer.
pub fn fail_out(it: &mut Interp, generator: u64, v: Value) -> Result<Value, Ctl> {
    if let Some(p) = it.gens.producers.lock().expect("gens").get(&generator) {
        let _ = p.to.send(Evt::Failed(v));
    }
    Err(panic(FAILED))
}

/// Drops generator `id`: a suspended producer is told to unwind, and waited for, so its cleanup
/// runs before the program goes on; a chain drops what it pulls from.
pub fn drop_gen(it: &mut Interp, id: u64) {
    let kind = it.gens.consumers.lock().expect("gens").remove(&id);
    match kind {
        Some(GenKind::Thread { to, from, started }) => {
            drop(to);
            if started {
                // The producer unwinds on its own thread; wait until it has finished.
                while let Ok(Evt::Item(_)) = from.lock().expect("rx").recv() {}
            }
        }
        Some(GenKind::Map { inner, .. } | GenKind::Filter { inner, .. } | GenKind::Take { inner, .. } | GenKind::Enumerate { inner, .. }) => {
            drop_gen(it, inner)
        }
        Some(GenKind::Zip { a, b }) => {
            drop_gen(it, a);
            drop_gen(it, b);
        }
        _ => {}
    }
}

/// `g.next()`: the next item, or `None` when the generator is done.
pub fn next(it: &mut Interp, id: u64) -> Result<Option<Value>, Ctl> {
    let kind = it.gens.consumers.lock().expect("gens").remove(&id);
    let Some(mut kind) = kind else { return Ok(None) };
    let r = step(it, &mut kind);
    if !matches!(r, Ok(None)) || !matches!(kind, GenKind::Done) {
        it.gens.consumers.lock().expect("gens").insert(id, kind);
    }
    r
}

fn step(it: &mut Interp, kind: &mut GenKind) -> Result<Option<Value>, Ctl> {
    match kind {
        GenKind::Thread { to, from, started } => {
            *started = true;
            if to.send(Cmd::Next).is_err() {
                *kind = GenKind::Done;
                return Ok(None);
            }
            let evt = from.lock().expect("rx").recv();
            match evt {
                Ok(Evt::Item(v)) => Ok(Some(v)),
                Ok(Evt::Done) | Err(_) => {
                    *kind = GenKind::Done;
                    Ok(None)
                }
                Ok(Evt::Failed(v)) => {
                    *kind = GenKind::Done;
                    it.raise(v).map(|_| None)
                }
                Ok(Evt::Panicked(m)) => {
                    *kind = GenKind::Done;
                    Err(panic(m))
                }
            }
        }
        GenKind::Items { items, pos } => {
            let r = items.get(*pos).cloned();
            *pos += 1;
            Ok(r)
        }
        GenKind::Map { inner, f } => match next(it, *inner)? {
            Some(v) => {
                let f = f.clone();
                Ok(Some(it.call_value(&f, vec![v])?))
            }
            None => Ok(None),
        },
        GenKind::Filter { inner, f } => loop {
            match next(it, *inner)? {
                Some(v) => {
                    let f = f.clone();
                    if it.call_value(&f, vec![v.clone()])?.as_bool() {
                        return Ok(Some(v));
                    }
                }
                None => return Ok(None),
            }
        },
        GenKind::Take { inner, left } => {
            if *left == 0 {
                return Ok(None);
            }
            *left -= 1;
            next(it, *inner)
        }
        GenKind::Zip { a, b } => match (next(it, *a)?, next(it, *b)?) {
            (Some(x), Some(y)) => Ok(Some(Value::Tuple(vec![x, y]))),
            _ => Ok(None),
        },
        GenKind::Enumerate { inner, n } => match next(it, *inner)? {
            Some(v) => {
                let i = *n;
                *n += 1;
                Ok(Some(Value::Tuple(vec![Value::Int(i as i128), v])))
            }
            None => Ok(None),
        },
        GenKind::Done => Ok(None),
    }
}

pub type Pull = Box<dyn FnMut(&mut Interp) -> Result<Option<Value>, Ctl>>;

/// How `for…of` pulls items from a value that is not a generator call: a collection, a region
/// list, or a `Gen`.
pub fn items_of(_it: &mut Interp, v: &Value) -> Result<Pull, Ctl> {
    let snapshot = |items: Vec<Value>| -> Pull {
        let mut pos = 0;
        Box::new(move |_| {
            let r = items.get(pos).cloned();
            pos += 1;
            Ok(r)
        })
    };
    match v {
        Value::Native("Gen", id) => {
            let id = *id;
            Ok(Box::new(move |it| next(it, id)))
        }
        Value::Cell(c) => {
            let items = match &*c.lock().expect("cell") {
                Value::List(vs) => vs.clone(),
                other => return Err(panic(format!("cannot iterate {}", other.show()))),
            };
            Ok(snapshot(items))
        }
        // A channel's receiver: each message, until the loop ends.
        Value::Native("Receiver", ch) => {
            let ch = *ch;
            Ok(Box::new(move |it| it.sched.recv(it.task, ch)))
        }
        other => match other.deref() {
            Value::List(vs) | Value::Tuple(vs) => Ok(snapshot(vs)),
            Value::Text(s) => Ok(snapshot(s.bytes().map(|b| Value::Int(b as i128)).collect())),
            Value::Native("Gen", id) => Ok(Box::new(move |it| next(it, id))),
            Value::Cell(c) => {
                let items = match &*c.lock().expect("cell") {
                    Value::List(vs) => vs.clone(),
                    _ => Vec::new(),
                };
                Ok(snapshot(items))
            }
            v => Err(panic(format!("cannot iterate {}", v.show()))),
        },
    }
}
