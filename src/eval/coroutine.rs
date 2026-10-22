//! First-class continuations (§5.3).
//!
//! A resumptive arm that only resumes its continuation as its last act runs where the effect was
//! performed (see `Interp::perform`). Any other — one that stores `k`, returns it, or does work
//! after `k(a)` — needs the body suspended for real, so its `handle` runs the body as a
//! coroutine on a thread of its own. The handler's side drives it: an operation of the handled
//! effect runs its arm there, with `k` standing for the coroutine; calling `k(a)` resumes the
//! coroutine until its next operation or its end, whose value is `k(a)`'s. Effects the body
//! performs that the `handle` does not handle go to whoever resumed it, as a deep handler's do.

use std::collections::HashMap;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::sync::{Arc, Mutex};

use super::interp::{Ctl, Env, Handler, Interp, Lex, R, panic};
use super::value::*;
use crate::syntax::ast;

/// What the coroutine tells its driver.
pub enum Evt {
    /// The handled effect's operation `op`: run its arm.
    Op(String, Vec<Value>),
    /// Another effect's operation: perform it where the coroutine was resumed.
    Perform(usize, String, Vec<Value>),
    Yield(Value),
    Done(Value),
    Failed(Value),
    Panicked(String),
}

/// What the driver tells the coroutine.
pub enum Cmd {
    Start,
    /// Resume after an operation of the handled effect, with its result.
    Resume(Value),
    /// The result of an effect the driver performed for it, or a failure to raise there.
    Reply(Result<Value, Value>),
}

struct Co {
    to: Sender<Cmd>,
    from: Arc<Mutex<Receiver<Evt>>>,
    arms: Vec<ast::HandlerArm>,
    env: Env,
    lex: Lex,
}

/// The coroutine's own end of its channels, used on its thread.
struct Inside {
    to: Sender<Evt>,
    from: Arc<Mutex<Receiver<Cmd>>>,
}

#[derive(Default)]
pub struct Cos {
    drivers: Mutex<HashMap<u64, Co>>,
    insides: Mutex<HashMap<u64, Inside>>,
}

const ENDED: &str = "\u{0}coroutine ended";

/// Whether a `handle`'s arms need its body run as a coroutine: some resumptive arm uses its
/// continuation other than by calling it as its last act.
pub fn needed(arms: &[ast::HandlerArm]) -> bool {
    arms.iter().any(|a| {
        let Some(k) = &a.resumes else { return false };
        let tail_call = matches!(a.body.tail.as_deref(), Some(ast::Expr { kind: ast::ExprKind::Call { callee, args, .. }, .. })
            if matches!(&callee.kind, ast::ExprKind::Ident(c) if c == &k.name) && !args.iter().any(|x| mentions(x, &k.name)));
        let in_stmts = a.body.stmts.iter().any(|s| match s {
            ast::Stmt::Let { init, .. } => mentions(init, &k.name),
            ast::Stmt::Defer(e) | ast::Stmt::Expr(e) => mentions(e, &k.name),
        });
        let used = in_stmts || a.body.tail.as_deref().is_some_and(|t| mentions(t, &k.name));
        used && (!tail_call || in_stmts)
    })
}

/// Whether `name` occurs in an expression (conservatively: as any identifier).
fn mentions(e: &ast::Expr, name: &str) -> bool {
    format!("{e:?}").contains(&format!("Ident(\"{name}\")"))
}

/// Starts `body` as a coroutine handling `effect` with `arms`, and drives it to its first
/// operation or its end.
pub fn handle(it: &mut Interp, body: &ast::Block, effect: usize, arms: &[ast::HandlerArm], env: &Env) -> R {
    let co = it.fresh_id();
    let (to_co, co_rx) = channel::<Cmd>();
    let (co_tx, from_co) = channel::<Evt>();
    it.cos.drivers.lock().expect("cos").insert(
        co,
        Co { to: to_co, from: Arc::new(Mutex::new(from_co)), arms: arms.to_vec(), env: env.clone(), lex: it.lex.clone() },
    );
    it.cos.insides.lock().expect("cos").insert(co, Inside { to: co_tx.clone(), from: Arc::new(Mutex::new(co_rx)) });
    let mut child = it.fork_thread();
    let body = body.clone();
    let env = env.clone();
    std::thread::spawn(move || {
        if wait(&child, co).is_err() {
            return;
        }
        child.handlers = vec![Handler::Coroutine { co, effect }];
        let evt = match child.home(|c| c.block(&body, &env)) {
            Ok(v) => Some(Evt::Done(v)),
            Err(Ctl::Panic(m)) if m == ENDED => None,
            Err(Ctl::Panic(m)) => Some(Evt::Panicked(m)),
            Err(other) => Some(Evt::Panicked(format!("cannot leave a suspended `handle` with {other:?}"))),
        };
        if let Some(evt) = evt {
            let _ = co_tx.send(evt);
        }
    });
    drive(it, co, Cmd::Start)
}

/// On the coroutine's thread: wait for the driver's next command.
fn wait(it: &Interp, co: u64) -> Result<Cmd, Ctl> {
    let from = it.cos.insides.lock().expect("cos").get(&co).map(|i| i.from.clone()).ok_or_else(|| panic(ENDED))?;
    from.lock().expect("rx").recv().map_err(|_| panic(ENDED))
}

fn tell(it: &Interp, co: u64, evt: Evt) -> Result<(), Ctl> {
    let to = it.cos.insides.lock().expect("cos").get(&co).map(|i| i.to.clone()).ok_or_else(|| panic(ENDED))?;
    to.send(evt).map_err(|_| panic(ENDED))
}

/// On the coroutine's thread: an operation of the handled effect. Its result is what the arm
/// resumes it with.
pub fn op(it: &mut Interp, co: u64, name: &str, args: Vec<Value>) -> R {
    tell(it, co, Evt::Op(name.to_string(), args))?;
    match wait(it, co)? {
        Cmd::Resume(v) => Ok(v),
        _ => Err(panic("a coroutine resumed out of turn")),
    }
}

/// On the coroutine's thread: an effect the `handle` does not handle, performed by the driver.
pub fn forward(it: &mut Interp, co: u64, evt: Evt) -> R {
    tell(it, co, evt)?;
    match wait(it, co)? {
        Cmd::Reply(Ok(v)) => Ok(v),
        Cmd::Reply(Err(e)) => it.raise(e),
        _ => Err(panic("a coroutine resumed out of turn")),
    }
}

/// On the coroutine's thread: a failure nothing inside it handles goes to the driver.
pub fn fail(it: &mut Interp, co: u64, v: Value) -> R {
    tell(it, co, Evt::Failed(v))?;
    Err(panic(ENDED))
}

/// Resumes the coroutine with `cmd`, serving what it asks for, until an arm gives a value or the
/// body ends: that is the value of the `handle`, or of the `k(a)` that resumed it.
pub fn drive(it: &mut Interp, co: u64, mut cmd: Cmd) -> R {
    loop {
        let (to, from) = {
            let cos = it.cos.drivers.lock().expect("cos");
            let c = cos.get(&co).ok_or_else(|| panic("a continuation was resumed twice"))?;
            (c.to.clone(), c.from.clone())
        };
        to.send(cmd).map_err(|_| panic("a continuation was resumed after its computation ended"))?;
        let evt = from.lock().expect("rx").recv().map_err(|_| panic("a continuation's computation vanished"))?;
        match evt {
            Evt::Op(name, args) => return arm(it, co, &name, args),
            Evt::Perform(effect, name, args) => {
                cmd = Cmd::Reply(Ok(it.perform_op(effect, &name, args)?));
            }
            Evt::Yield(v) => {
                it.yield_value(v)?;
                cmd = Cmd::Reply(Ok(Value::Unit));
            }
            Evt::Done(v) => {
                it.cos.drivers.lock().expect("cos").remove(&co);
                return Ok(v);
            }
            Evt::Failed(v) => {
                it.cos.drivers.lock().expect("cos").remove(&co);
                return it.raise(v);
            }
            Evt::Panicked(m) => {
                it.cos.drivers.lock().expect("cos").remove(&co);
                return Err(panic(m));
            }
        }
    }
}

/// Whether coroutine `co`'s `handle` has an arm for operation `name`: one it has not passes on.
pub fn has_arm(it: &Interp, co: u64, name: &str) -> bool {
    it.cos.drivers.lock().expect("cos").get(&co).is_some_and(|c| c.arms.iter().any(|a| a.op.name == name))
}

/// Runs the arm for operation `name` where the coroutine was resumed, lexically in its `handle`.
fn arm(it: &mut Interp, co: u64, name: &str, args: Vec<Value>) -> R {
    let (arms, env, lex) = {
        let cos = it.cos.drivers.lock().expect("cos");
        let c = cos.get(&co).ok_or_else(|| panic("a continuation vanished"))?;
        (c.arms.clone(), c.env.clone(), c.lex.clone())
    };
    let Some(arm) = arms.iter().find(|a| a.op.name == name) else { return Err(panic(format!("no arm for `{name}`"))) };
    let aenv = super::interp::new_env(Some(env));
    for (p, a) in arm.params.iter().zip(args) {
        super::interp::define(&aenv, &p.name, a);
    }
    if let Some(k) = &arm.resumes {
        super::interp::define(&aenv, &k.name, Value::Native("Cont", co));
    }
    let saved = std::mem::replace(&mut it.lex, lex);
    let r = it.home(|i| i.block(&arm.body, &aenv));
    it.lex = saved;
    r
}
