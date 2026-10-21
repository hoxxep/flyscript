//! A direct-style interpreter with effect handlers.
//!
//! Abortive handlers unwind (`Ctl::Unwind`); tail-resumptive ones run at the point the effect is
//! performed, so a `for…of` over a generator, or an `Ask` handler that answers and resumes, costs
//! no stack capture. Continuations that must be stored — a `Gen` pulled with `next()` — run the
//! generator on its own thread, handing control back and forth (see `gen`).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use super::value::*;
use super::world::World;
use crate::check::env::{Binding, DefKind, FnId, Program, SubstMap, subst, subst_arg};
use crate::check::types::{GArg, Len, Prim, Show, Ty};
use crate::diag::Span;
use crate::syntax::ast::{self, Expr, ExprKind, Pattern, PatternKind, Stmt, TagArgs, TagPatArgs};

/// Non-local control flow.
#[derive(Debug)]
pub enum Ctl {
    Return(u64, Value),
    Break(u64),
    Continue(u64),
    /// Unwind to handler `id` with a value (a failure's payload, or a handler's result).
    Unwind(u64, Value),
    /// Unwind to handler `id` and run its abortive arm `arm` with these arguments.
    Abort(u64, usize, Vec<Value>),
    /// A tail-resumptive continuation was called: return this value where the effect was
    /// performed for handler `id`.
    Resume(u64, Value),
    /// A runtime error (a panic, §5.7).
    Panic(String),
    /// The task's scope was cancelled, because another of its tasks failed (§6.1): unwind to it.
    Cancelled,
}

pub type R = Result<Value, Ctl>;

/// A lexical scope of bindings.
pub struct Scope {
    vars: Mutex<HashMap<String, Shared>>,
    parent: Option<Env>,
    /// The bindings made here that may need dropping, in order, with their types (§5.6).
    owned: Mutex<Vec<(String, Ty)>>,
    /// Field paths moved out of this scope's bindings (a whole move is the empty path).
    moved: Mutex<HashMap<String, Vec<Vec<String>>>>,
}

pub type Env = Arc<Scope>;

pub fn new_env(parent: Option<Env>) -> Env {
    Arc::new(Scope { vars: Mutex::new(HashMap::new()), parent, owned: Mutex::new(Vec::new()), moved: Mutex::new(HashMap::new()) })
}

fn lookup(env: &Env, name: &str) -> Option<Shared> {
    let mut e = Some(env.clone());
    while let Some(s) = e {
        if let Some(v) = s.vars.lock().expect("env").get(name) {
            return Some(v.clone());
        }
        e = s.parent.clone();
    }
    None
}

pub fn define(env: &Env, name: &str, v: Value) {
    env.vars.lock().expect("env").insert(name.to_string(), shared(v));
}

/// Binds `name` to an owned value of type `ty`, to be dropped when its scope ends.
fn define_owned(env: &Env, name: &str, v: Value, ty: Ty) {
    env.moved.lock().expect("env").remove(name);
    env.owned.lock().expect("env").push((name.to_string(), ty));
    define(env, name, v);
}

/// Records that `path` of binding `name` was moved out, in the scope that has the binding.
fn mark_moved(env: &Env, name: &str, path: Vec<String>) {
    let mut e = Some(env.clone());
    while let Some(s) = e {
        if s.vars.lock().expect("env").contains_key(name) {
            s.moved.lock().expect("env").entry(name.to_string()).or_default().push(path);
            return;
        }
        e = s.parent.clone();
    }
}

/// The parts of binding `name` under field path `prefix` that were moved out, relative to
/// `prefix`; the empty path if the whole of it was.
fn moved_under(env: &Env, name: &str, prefix: &[String]) -> Vec<Vec<String>> {
    let mut e = Some(env.clone());
    while let Some(s) = e {
        if s.vars.lock().expect("env").contains_key(name) {
            let moved = s.moved.lock().expect("env").get(name).cloned().unwrap_or_default();
            if moved.iter().any(|m| prefix.starts_with(m)) {
                return vec![Vec::new()];
            }
            return moved.iter().filter(|m| m.starts_with(prefix)).map(|m| m[prefix.len()..].to_vec()).collect();
        }
        e = s.parent.clone();
    }
    Vec::new()
}

/// A place assigned anew owns a value again.
fn mark_assigned(env: &Env, name: &str, prefix: &[String]) {
    let mut e = Some(env.clone());
    while let Some(s) = e {
        if s.vars.lock().expect("env").contains_key(name) {
            if let Some(moved) = s.moved.lock().expect("env").get_mut(name) {
                moved.retain(|m| !m.starts_with(prefix));
            }
            return;
        }
        e = s.parent.clone();
    }
}

/// Where `break`, `continue` and `return` go, lexically.
#[derive(Clone)]
pub struct Lex {
    pub frame: u64,
    pub loops: Vec<u64>,
    /// The function whose recorded types apply.
    pub owner: FnId,
    pub module: usize,
    /// The generic arguments of the running function, by parameter symbol: what a call
    /// through a bound dispatches on (§3.4).
    pub tenv: TEnv,
}

pub type TEnv = Arc<HashMap<u32, GArg>>;

#[derive(Clone)]
pub enum Handler {
    /// `try`/`catch`, `Fail.capture`, a forked task: catches failures.
    Fail { id: u64 },
    /// A `for…of` over a generator: each `yield` runs the loop body where it is performed.
    Loop { id: u64, pat: Pattern, body: ast::Block, env: Env, lex: Lex },
    /// A `handle` expression.
    User { id: u64, effect: usize, arms: Vec<ast::HandlerArm>, env: Env, lex: Lex },
    /// The bottom of a generator's thread: `yield` hands an item to the consumer.
    GenYield { generator: u64 },
    /// The bottom of a coroutine's thread (§5.3): `effect` goes to its arms, and anything else no
    /// handler inside takes goes to whoever resumed it.
    Coroutine { co: u64, effect: usize },
}

pub struct Interp {
    pub prog: Arc<Program>,
    pub world: Arc<Mutex<World>>,
    pub handlers: Vec<Handler>,
    pub lex: Lex,
    pub ids: Arc<AtomicU64>,
    pub gens: Arc<super::generators::Gens>,
    pub cos: Arc<super::coroutine::Cos>,
    pub scopes: Arc<Mutex<HashMap<u64, super::builtins::ScopeState>>>,
    /// The span of the call being made, so a builtin can see its expected result type.
    pub call_span: Option<Span>,
    pub sched: Arc<super::sched::Sched>,
    /// The task this interpreter is running (0 is the program's first task).
    pub task: u64,
}

pub fn panic(msg: impl Into<String>) -> Ctl {
    Ctl::Panic(msg.into())
}

impl Interp {
    pub fn new(prog: Arc<Program>, world: Arc<Mutex<World>>) -> Interp {
        let seed = world.lock().expect("world").seed;
        Interp {
            prog,
            world,
            handlers: Vec::new(),
            lex: Lex { frame: 0, loops: Vec::new(), owner: 0, module: 0, tenv: TEnv::default() },
            ids: Arc::new(AtomicU64::new(1)),
            gens: Arc::new(super::generators::Gens::default()),
            cos: Arc::new(super::coroutine::Cos::default()),
            scopes: Arc::new(Mutex::new(HashMap::new())),
            call_span: None,
            sched: super::sched::Sched::new(seed),
            task: 0,
        }
    }

    /// A fresh interpreter sharing this one's program, world and registries (for a generator's
    /// thread).
    pub fn fork_thread(&self) -> Interp {
        Interp {
            prog: self.prog.clone(),
            world: self.world.clone(),
            handlers: Vec::new(),
            lex: self.lex.clone(),
            ids: self.ids.clone(),
            gens: self.gens.clone(),
            cos: self.cos.clone(),
            scopes: self.scopes.clone(),
            call_span: None,
            sched: self.sched.clone(),
            task: self.task,
        }
    }

    pub fn fresh_id(&self) -> u64 {
        self.ids.fetch_add(1, Ordering::Relaxed)
    }

    fn ty_of(&self, span: Span) -> Option<Ty> {
        self.prog.typed.get(&self.lex.owner).and_then(|t| t.exprs.get(&span)).cloned()
    }

    fn binding_ty(&self, span: Span) -> Option<Ty> {
        self.prog.typed.get(&self.lex.owner).and_then(|t| t.bindings.get(&span)).cloned()
    }

    // ---- functions ----

    /// Calls a function by id with evaluated arguments.
    pub fn call_fn(&mut self, fid: FnId, args: Vec<Value>) -> R {
        self.call_fn_with(fid, args, TEnv::default())
    }

    pub fn call_fn_with(&mut self, fid: FnId, args: Vec<Value>, tenv: TEnv) -> R {
        let module = self.prog.fns[fid].module;
        let Some(fdecl) = self.prog.fn_decl(fid) else { return Err(panic("not a function")) };
        let Some(body) = fdecl.body else {
            return self.builtin(fid, args);
        };
        let env = new_env(None);
        let param_tys: Vec<Ty> = self.prog.fns[fid].scheme.params.iter().map(|(_, t)| t.clone()).collect();
        let frame = self.fresh_id();
        let saved = std::mem::replace(&mut self.lex, Lex { frame, loops: Vec::new(), owner: fid, module, tenv });
        for ((p, a), t) in fdecl.sig.params.iter().zip(args).zip(param_tys) {
            let t = self.frame_ty(&t);
            if super::drops::needs_drop(&self.prog, &t) {
                define_owned(&env, &p.name.name, a, t);
            } else {
                define(&env, &p.name.name, a);
            }
        }
        let r = self.block(&body, &env);
        // Parameters the body did not move are dropped as it returns (§5.6).
        let r = match (r, self.drop_scope(&env)) {
            (Ok(v), Err(e)) => {
                let _ = v;
                Err(e)
            }
            (r, _) => r,
        };
        self.lex = saved;
        match r {
            Err(Ctl::Return(f, v)) if f == frame => Ok(v),
            other => other,
        }
    }

    /// Calls a function value (closure, function, continuation).
    pub fn call_value(&mut self, f: &Value, args: Vec<Value>) -> R {
        match f.deref() {
            Value::Closure(c) => {
                let base = new_env(None);
                for (n, v) in &c.env {
                    base.vars.lock().expect("env").insert(n.clone(), v.clone());
                }
                // A `once` closure's call is its end: what it owns is dropped with it (§5.6).
                if c.once {
                    base.owned.lock().expect("env").extend(c.owned.iter().cloned());
                }
                let env = new_env(Some(base.clone()));
                for (p, a) in c.params.iter().zip(args) {
                    define(&env, p, a);
                }
                let frame = self.fresh_id();
                let saved = std::mem::replace(&mut self.lex, Lex { frame, loops: Vec::new(), owner: c.owner, module: c.module, tenv: c.tenv.clone() });
                let r = self.expr(&c.body, &env);
                let r = match (r, self.drop_scope(&base)) {
                    (Ok(_), Err(e)) => Err(e),
                    (r, _) => r,
                };
                self.lex = saved;
                match r {
                    Err(Ctl::Return(f, v)) if f == frame => Ok(v),
                    other => other,
                }
            }
            Value::Func(fid) => self.call_fn(fid, args),
            Value::Resume(id) => Err(Ctl::Resume(id, args.into_iter().next().unwrap_or(Value::Unit))),
            Value::Native("Cont", co) => {
                super::coroutine::drive(self, co, super::coroutine::Cmd::Resume(args.into_iter().next().unwrap_or(Value::Unit)))
            }
            other => Err(panic(format!("{} is not a function", other.show()))),
        }
    }

    // ---- effects ----

    /// `throw v`: unwinds to the innermost failure handler.
    pub fn raise(&mut self, v: Value) -> R {
        for h in self.handlers.iter().rev() {
            if let Handler::Fail { id } = h {
                return Err(Ctl::Unwind(*id, v));
            }
            if let Handler::GenYield { generator } = h {
                return super::generators::fail_out(self, *generator, v);
            }
            if let Handler::Coroutine { co, .. } = h {
                return super::coroutine::fail(self, *co, v);
            }
        }
        Err(panic(format!("uncaught failure: {}", v.show())))
    }

    /// `yield v`: runs the innermost loop body here, or hands the item to a generator's consumer.
    pub fn yield_value(&mut self, v: Value) -> R {
        // `yield` is an operation of `Yield`: a `handle` of it is a handler like the built-in ones.
        let yield_def = self.prog.known.get("Yield").copied();
        let user = |h: &Handler| matches!(h, Handler::User { effect, .. } if Some(*effect) == yield_def);
        let Some(pos) = self.handlers.iter().rposition(|h| matches!(h, Handler::Loop { .. } | Handler::GenYield { .. }) || user(h)) else {
            if let (Some(Handler::Coroutine { effect, .. }), Some(y)) = (self.handlers.first(), yield_def)
                && *effect == y
            {
                return self.perform(y, "yield", vec![v]);
            }
            if let Some(Handler::Coroutine { co, .. }) = self.handlers.first() {
                let co = *co;
                return super::coroutine::forward(self, co, super::coroutine::Evt::Yield(v));
            }
            return Err(panic("`yield` outside any generator"));
        };
        match self.handlers[pos].clone() {
            Handler::User { effect, .. } => self.perform(effect, "yield", vec![v]),
            Handler::GenYield { generator } => super::generators::hand_over(self, generator, v),
            Handler::Loop { pat, body, env, lex, .. } => {
                // The body is outside the generator: it sees the handlers outside the loop.
                let saved_handlers = self.handlers.split_off(pos);
                let saved_lex = std::mem::replace(&mut self.lex, lex.clone());
                let env = new_env(Some(env));
                let r = match self.bind(&pat, &v, None, &env) {
                    true => self.block(&body, &env),
                    false => Err(panic("loop pattern did not match")),
                };
                self.lex = saved_lex;
                self.handlers.extend(saved_handlers);
                match r {
                    Ok(_) => Ok(Value::Unit),
                    Err(Ctl::Continue(l)) if lex.loops.last() == Some(&l) => Ok(Value::Unit),
                    Err(e) => Err(e),
                }
            }
            _ => unreachable!(),
        }
    }

    /// Performs a user effect's operation.
    /// `Io`'s own operations, handled by the root handler against the simulated world (§6.4).
    /// Each is a scheduling point.
    fn root_io(&mut self, op: &str, args: Vec<Value>) -> R {
        self.sched.yield_now(self.task)?;
        let mut w = self.world.lock().expect("world");
        Ok(match op {
            "now" => Value::Int(w.clock as i128),
            "sleep" => {
                w.clock += args.first().map_or(0, |n| n.as_int() as u64);
                Value::Unit
            }
            "write" => {
                let bytes: Vec<u8> = match args.get(1).map(|b| b.deref()) {
                    Some(Value::List(vs)) => vs.iter().map(|b| b.as_int() as u8).collect(),
                    _ => Vec::new(),
                };
                let n = bytes.len();
                w.out.push(String::from_utf8_lossy(&bytes).into_owned());
                Value::tag("Ok", Value::Tuple(vec![Value::Int(n as i128)]))
            }
            "read" => Value::tag("Ok", Value::Tuple(vec![Value::Int(0)])),
            _ => Value::Unit,
        })
    }

    /// Performs `op` of `effect` as if from here (for a coroutine's driver).
    pub fn perform_op(&mut self, effect: usize, op: &str, args: Vec<Value>) -> R {
        self.perform(effect, op, args)
    }

    fn perform(&mut self, effect: usize, op: &str, args: Vec<Value>) -> R {
        let Some(pos) = self.handlers.iter().rposition(|h| matches!(h, Handler::User { effect: e, .. } if *e == effect)) else {
            // On a coroutine's thread, the effect is its handler's or its resumer's.
            if let Some(Handler::Coroutine { co, effect: handled }) = self.handlers.first() {
                let (co, handled) = (*co, *handled);
                return if handled == effect {
                    super::coroutine::op(self, co, op, args)
                } else {
                    super::coroutine::forward(self, co, super::coroutine::Evt::Perform(effect, op.to_string(), args))
                };
            }
            if self.prog.known.get("Io") == Some(&effect) {
                return self.root_io(op, args);
            }
            return Err(panic(format!("unhandled effect `{}`", self.prog.defs[effect].name)));
        };
        let Handler::User { id, arms, env, lex, .. } = self.handlers[pos].clone() else { unreachable!() };
        let Some(ai) = arms.iter().position(|a| a.op.name == op) else {
            return Err(panic(format!("no arm for `{op}`")));
        };
        let arm = &arms[ai];
        if arm.resumes.is_none() {
            // Abortive: unwind the body first, then run the arm at the handler (§5.2).
            return Err(Ctl::Abort(id, ai, args));
        }
        // Resumptive: run the arm here, with the handlers outside the `handle` (deep, §5.3).
        let saved_handlers = self.handlers.split_off(pos);
        let saved_lex = std::mem::replace(&mut self.lex, lex);
        let aenv = new_env(Some(env));
        for (p, a) in arm.params.iter().zip(args) {
            define(&aenv, &p.name, a);
        }
        if let Some(k) = &arm.resumes {
            define(&aenv, &k.name, Value::Resume(id));
        }
        let r = self.block(&arm.body.clone(), &aenv);
        self.lex = saved_lex;
        self.handlers.extend(saved_handlers);
        match r {
            Err(Ctl::Resume(h, v)) if h == id => Ok(v),
            // The arm finished without resuming: the `handle` evaluates to its value.
            Ok(v) => Err(Ctl::Unwind(id, v)),
            Err(e) => Err(e),
        }
    }

    // ---- blocks and statements ----

    pub fn block(&mut self, b: &ast::Block, env: &Env) -> R {
        let env = new_env(Some(env.clone()));
        let mut defers: Vec<Expr> = Vec::new();
        let mut result = Ok(Value::Unit);
        for st in &b.stmts {
            let r = match st {
                Stmt::Let { pat, init, .. } => match self.expr(init, &env) {
                    Ok(v) => {
                        let v = self.coerce_binding(pat, v);
                        if self.bind(pat, &v, None, &env) { Ok(Value::Unit) } else { Err(panic("pattern did not match")) }
                    }
                    Err(e) => Err(e),
                },
                Stmt::Defer(e) => {
                    defers.push(e.clone());
                    Ok(Value::Unit)
                }
                Stmt::Expr(e) => self.expr(e, &env),
            };
            if let Err(e) = r {
                result = Err(e);
                break;
            }
        }
        if result.is_ok() {
            result = match &b.tail {
                Some(e) => self.expr(e, &env),
                None => Ok(Value::Unit),
            };
        }
        // `defer`s run in reverse order however the block exits (§5.6).
        for d in defers.iter().rev() {
            if let Err(e) = self.expr(d, &env)
                && result.is_ok() {
                    result = Err(e);
                }
        }
        // Then the block's owned bindings that were not moved out, newest first.
        if let Err(e) = self.drop_scope(&env)
            && result.is_ok() {
                result = Err(e);
            }
        result
    }

    /// Drops the owned bindings of a scope, newest first, except what was moved out of them.
    fn drop_scope(&mut self, env: &Env) -> Result<(), Ctl> {
        let owned = std::mem::take(&mut *env.owned.lock().expect("env"));
        for (name, ty) in owned.into_iter().rev() {
            let moved = env.moved.lock().expect("env").get(&name).cloned().unwrap_or_default();
            let Some(cell) = env.vars.lock().expect("env").get(&name).cloned() else { continue };
            let v = cell.lock().expect("cell").clone();
            self.drop_value(v, &ty, &moved)?;
        }
        Ok(())
    }

    /// A value bound to an owned binding is read out of any borrow it arrived as.
    fn coerce_binding(&self, pat: &Pattern, v: Value) -> Value {
        match self.binding_ty(pat.span) {
            Some(Ty::Borrow(..)) | Some(Ty::Slice(_)) | Some(Ty::Prim(Prim::Str)) => v,
            _ if matches!(v, Value::Ptr(_)) && matches!(pat.kind, PatternKind::Bind(_)) => v.deref(),
            _ => v,
        }
    }

    // ---- patterns ----

    /// Matches `v` (found at `place`, if it is a place) against `pat`, binding into `env`.
    pub fn bind(&mut self, pat: &Pattern, v: &Value, place: Option<Place>, env: &Env) -> bool {
        // Matching through a borrow binds borrows of the parts.
        let (v, place) = match v {
            Value::Ptr(p) if !matches!(pat.kind, PatternKind::Bind(_) | PatternKind::Wild) => (get(p), Some(p.clone())),
            _ => (v.clone(), place),
        };
        let sub = |place: &Option<Place>, seg: Seg| place.clone().map(|mut p| {
            p.path.push(seg);
            p
        });
        let part = |place: &Option<Place>, seg: Seg, value: Value| match sub(place, seg) {
            Some(p) => Value::Ptr(p),
            None => value,
        };
        match &pat.kind {
            PatternKind::Wild => true,
            PatternKind::TagAt { .. } => false,
            PatternKind::Bind(name) => {
                match self.binding_ty(pat.span).map(|t| self.frame_ty(&t)) {
                    Some(t) if !matches!(v, Value::Ptr(_)) && super::drops::needs_drop(&self.prog, &t) => define_owned(env, name, v.clone(), t),
                    _ => define(env, name, v.clone()),
                }
                true
            }
            PatternKind::Lit(e) => match self.expr(e, env) {
                Ok(lit) => lit.equals(&v),
                Err(_) => false,
            },
            PatternKind::Tuple(ps) => {
                let items = match v.deref() {
                    Value::Tuple(vs) | Value::List(vs) => vs,
                    _ => return false,
                };
                items.len() == ps.len()
                    && ps.iter().enumerate().all(|(i, p)| {
                        let pv = part(&place, Seg::Index(i), items[i].clone());
                        self.bind(p, &pv, None, env)
                    })
            }
            PatternKind::Record { fields, .. } => {
                let Value::Record(fs) = v.deref() else { return false };
                fields.iter().all(|(name, p)| {
                    let fv = part(&place, Seg::Field(name.name.clone()), fs.get(&name.name).cloned().unwrap_or(Value::Unit));
                    match p {
                        Some(p) => self.bind(p, &fv, None, env),
                        None => {
                            define(env, &name.name, fv);
                            true
                        }
                    }
                })
            }
            PatternKind::Tag { name, args } => {
                let Value::Tag(tag, payload) = v.deref() else { return false };
                if &*tag != name {
                    return false;
                }
                match args {
                    TagPatArgs::None => true,
                    // `#A(x)` binds the whole of a larger payload (§3.2).
                    TagPatArgs::Tuple(ps) if ps.len() == 1 && (matches!(*payload, Value::Record(_)) || matches!(&*payload, Value::Tuple(items) if items.len() != 1)) => {
                        self.bind(&ps[0], &part(&place, Seg::Payload, (*payload).clone()), None, env)
                    }
                    TagPatArgs::Tuple(ps) => {
                        let Value::Tuple(items) = *payload else { return false };
                        ps.iter().enumerate().all(|(i, p)| {
                            let pv = part(&place, Seg::Index(i), items[i].clone());
                            self.bind(p, &pv, None, env)
                        })
                    }
                    TagPatArgs::Record(fields) => {
                        let Value::Record(fs) = *payload else { return false };
                        fields.iter().all(|(fname, p)| {
                            let fv = part(&place, Seg::Field(fname.name.clone()), fs.get(&fname.name).cloned().unwrap_or(Value::Unit));
                            match p {
                                Some(p) => self.bind(p, &fv, None, env),
                                None => {
                                    define(env, &fname.name, fv);
                                    true
                                }
                            }
                        })
                    }
                }
            }
            PatternKind::Or(alts) => alts.iter().any(|a| self.bind(a, &v, place.clone(), env)),
        }
    }

    // ---- places ----

    /// The place an expression denotes: a binding, a field or element of one, or a temporary.
    pub fn place(&mut self, e: &Expr, env: &Env) -> Result<Place, Ctl> {
        match &e.kind {
            ExprKind::Ident(name) => match lookup(env, name) {
                // A binding that holds a borrow denotes the borrowed place.
                Some(cell) => match &*cell.lock().expect("cell") {
                    Value::Ptr(p) => Ok(p.clone()),
                    Value::Ref(r) => Ok(Place { root: r.clone(), path: Vec::new() }),
                    _ => Ok(Place { root: cell.clone(), path: Vec::new() }),
                },
                None => Err(panic(format!("unknown name `{name}`"))),
            },
            ExprKind::Field { target, name } => {
                let mut p = self.place(target, env)?;
                p.path.push(Seg::Field(name.name.clone()));
                Ok(p)
            }
            ExprKind::Index { target, index } => {
                let mut p = self.place(target, env)?;
                if let ExprKind::Range { lo, hi } = &index.kind {
                    let lo = match lo { Some(x) => self.expr(x, env)?.as_int() as usize, None => 0 };
                    let hi = match hi {
                        Some(x) => self.expr(x, env)?.as_int() as usize,
                        None => match get(&p) {
                            Value::List(vs) => vs.len(),
                            Value::Text(s) => s.len(),
                            _ => 0,
                        },
                    };
                    p.path.push(Seg::Range(lo, hi));
                } else {
                    let i = self.expr(index, env)?.as_int() as usize;
                    p.path.push(Seg::Index(i));
                }
                Ok(p)
            }
            ExprKind::BorrowMut(inner) => self.place(inner, env),
            _ => {
                let v = self.expr(e, env)?;
                Ok(match v {
                    Value::Ptr(p) => p,
                    Value::Ref(r) => Place { root: r, path: Vec::new() },
                    v => Place { root: shared(v), path: Vec::new() },
                })
            }
        }
    }

    // ---- expressions ----

    pub fn expr(&mut self, e: &Expr, env: &Env) -> R {
        let r = self.expr_inner(e, env);
        // A value moved out of a binding is no longer the binding's to drop.
        if r.is_ok()
            && let Some(path) = self.prog.typed.get(&self.lex.owner).and_then(|t| t.moves.get(&e.span)).cloned()
                && let Some(name) = root_name(e) {
                    mark_moved(env, name, path);
                }
        r
    }

    fn expr_inner(&mut self, e: &Expr, env: &Env) -> R {
        match &e.kind {
            ExprKind::TypeRef(_) | ExprKind::FieldAt { .. } | ExprKind::TagAt { .. } => Err(panic("comptime syntax at run time")),
            ExprKind::Int(s) => Ok(match self.ty_of(e.span) {
                Some(Ty::Prim(p)) if p.is_float() => Value::Float(s.parse().unwrap_or(0.0)),
                _ => Value::Int(parse_int(s)),
            }),
            ExprKind::Float(s) => Ok(Value::Float(s.parse().unwrap_or(0.0))),
            ExprKind::Byte(b) => Ok(Value::Int(*b as i128)),
            ExprKind::Str(s) => Ok(Value::text(s)),
            ExprKind::Bool(b) => Ok(Value::Bool(*b)),
            ExprKind::Template(pieces) => {
                let mut out = String::new();
                for p in pieces {
                    match p {
                        ast::TemplatePiece::Lit(s) => out.push_str(s),
                        ast::TemplatePiece::Expr(x) => {
                            let v = self.expr(x, env)?;
                            // A string is written as it is, also where generic code has it as a `T`.
                            let string = self.ty_of(x.span).map(|t| self.frame_ty(&t)).is_some_and(|t| self.is_string(&t));
                            match self.op_target(x.span, true).filter(|_| !string) {
                                // `Show.show` writes it, into a string of its own.
                                Some((f, tenv)) => {
                                    let buf = Place { root: shared(Value::text("")), path: Vec::new() };
                                    self.call_fn_with(f, vec![v, Value::Ptr(buf.clone())], tenv)?;
                                    out.push_str(&get(&buf).as_text());
                                }
                                None => out.push_str(&v.show()),
                            }
                        }
                    }
                }
                Ok(Value::text(&out))
            }
            ExprKind::Ident(name) => match lookup(env, name) {
                Some(cell) => Ok(cell.lock().expect("cell").clone()),
                None => match self.prog.lookup(self.lex.module, name) {
                    Some(Binding::Fn(fid)) => Ok(Value::Func(fid)),
                    Some(Binding::Const(c)) => {
                        let value = self.prog.consts[c].value.clone();
                        self.expr(&value, &new_env(None))
                    }
                    _ => Err(panic(format!("unknown name `{name}`"))),
                },
            },
            ExprKind::Tag { name, args } => {
                let payload = match args {
                    TagArgs::None => Value::Unit,
                    TagArgs::Tuple(items) if self.prog.typed.get(&self.lex.owner).is_some_and(|t| t.whole.contains(&e.span)) => {
                        self.owned_all(items, env)?.into_iter().next().unwrap_or(Value::Unit)
                    }
                    TagArgs::Tuple(items) => Value::Tuple(self.owned_all(items, env)?),
                    TagArgs::Record(fields) => self.record(fields, env)?,
                };
                Ok(Value::tag(name, payload))
            }
            ExprKind::Record { fields, .. } => self.record(fields, env),
            ExprKind::List(items) => {
                let vs = self.owned_all(items, env)?;
                Ok(match self.ty_of(e.span) {
                    Some(Ty::Tuple(_)) => Value::Tuple(vs),
                    _ => Value::List(vs),
                })
            }
            ExprKind::Field { .. } | ExprKind::Index { .. } => {
                let p = self.place(e, env)?;
                Ok(get(&p))
            }
            ExprKind::Call { callee, args, .. } => self.call(e, callee, args, env),
            ExprKind::Unary { op, operand } => {
                let v = self.expr(operand, env)?.deref();
                Ok(match (*op, v) {
                    ("!", Value::Bool(b)) => Value::Bool(!b),
                    ("-", Value::Int(i)) => Value::Int(-i),
                    ("-", Value::Float(f)) => Value::Float(-f),
                    (_, v) => return Err(panic(format!("bad operand {}", v.show()))),
                })
            }
            ExprKind::BorrowMut(inner) => Ok(Value::Ptr(self.place(inner, env)?)),
            ExprKind::Binary { op, lhs, rhs } if self.op_target(e.span, false).is_some() => {
                let (f, tenv) = self.op_target(e.span, false).expect("an operator's method");
                let (l, r) = (self.expr(lhs, env)?, self.expr(rhs, env)?);
                let v = self.call_fn_with(f, vec![l, r], tenv)?;
                Ok(Value::Bool(match *op {
                    "==" => v.as_bool(),
                    "!=" => !v.as_bool(),
                    // `Ord.cmp` gave `#Less`, `#Equal` or `#Greater`.
                    _ => {
                        let Value::Tag(t, _) = v.deref() else { return Err(panic("`cmp` gave no ordering")) };
                        match *op {
                            "<" => &*t == "Less",
                            "<=" => &*t != "Greater",
                            ">" => &*t == "Greater",
                            _ => &*t != "Less",
                        }
                    }
                }))
            }
            ExprKind::Binary { op, lhs, rhs } => {
                if *op == "&&" {
                    return Ok(Value::Bool(self.expr(lhs, env)?.as_bool() && self.expr(rhs, env)?.as_bool()));
                }
                if *op == "||" {
                    return Ok(Value::Bool(self.expr(lhs, env)?.as_bool() || self.expr(rhs, env)?.as_bool()));
                }
                let a = self.expr(lhs, env)?.deref();
                let b = self.expr(rhs, env)?.deref();
                binary(op, &a, &b)
            }
            ExprKind::Assign { op, target, value } => {
                let v = self.expr(value, env)?;
                let p = self.place(target, env)?;
                let new = if *op == "=" {
                    if matches!(v, Value::Ptr(_)) && !self.ty_of(target.span).is_some_and(|t| matches!(t, Ty::Borrow(..))) { v.deref() } else { v }
                } else {
                    binary(&op[..op.len() - 1], &get(&p).deref(), &v.deref())?
                };
                // The value the place held is dropped before it is overwritten (§5.6).
                let fields = self.place_fields(target);
                if *op == "="
                    && let Some(t) = self.ty_of(target.span).map(|t| self.frame_ty(&t))
                    && super::drops::needs_drop(&self.prog, &t)
                {
                    let moved = fields.as_ref().map(|(name, prefix)| moved_under(env, name, prefix)).unwrap_or_default();
                    self.drop_value(get(&p), &t, &moved)?;
                }
                set(&p, new);
                if let Some((name, prefix)) = fields {
                    mark_assigned(env, name, &prefix);
                }
                Ok(Value::Unit)
            }
            ExprKind::Cast { expr, ty } => {
                let v = self.expr(expr, env)?.deref();
                Ok(cast(&v, ty))
            }
            ExprKind::Range { .. } => Err(panic("a range can only index")),
            ExprKind::Lambda { params, body } => {
                // What it moves in leaves its binding now, into a cell of the closure's own.
                let moved_in = self.prog.typed.get(&self.lex.owner).and_then(|t| t.captured_moves.get(&e.span)).cloned().unwrap_or_default();
                let mut captured: Vec<(String, Shared)> = Vec::new();
                let mut owned = Vec::new();
                for (name, ty) in moved_in {
                    if let Some(cell) = lookup(env, &name) {
                        let v = cell.lock().expect("cell").clone();
                        captured.push((name.clone(), shared(v)));
                        mark_moved(env, &name, Vec::new());
                        let ty = self.frame_ty(&ty);
                        if super::drops::needs_drop(&self.prog, &ty) {
                            owned.push((name, ty));
                        }
                    }
                }
                // The rest it captures by reference: borrows, as checked (§4.3).
                let mut scope = Some(env.clone());
                while let Some(s) = scope {
                    for (k, v) in s.vars.lock().expect("env").iter() {
                        if !captured.iter().any(|(n, _)| n == k) {
                            captured.push((k.clone(), v.clone()));
                        }
                    }
                    scope = s.parent.clone();
                }
                let once = matches!(self.ty_of(e.span), Some(Ty::Fn(f)) if f.mode == crate::check::types::FnMode::Once);
                Ok(Value::Closure(Arc::new(Closure {
                    params: params.iter().map(|p| p.name.name.clone()).collect(),
                    body: (**body).clone(),
                    env: captured,
                    module: self.lex.module,
                    owner: self.lex.owner,
                    tenv: self.lex.tenv.clone(),
                    owned,
                    once,
                })))
            }
            ExprKind::Block(b) => self.block(b, env),
            ExprKind::If { cond, then, otherwise } => {
                if self.expr(cond, env)?.as_bool() {
                    self.block(then, env)
                } else if let Some(o) = otherwise {
                    self.expr(o, env)
                } else {
                    Ok(Value::Unit)
                }
            }
            ExprKind::While { cond, body } => {
                let id = self.fresh_id();
                self.lex.loops.push(id);
                let r = loop {
                    match self.expr(cond, env) {
                        Ok(c) if !c.as_bool() => break Ok(Value::Unit),
                        Ok(_) => {}
                        Err(e) => break Err(e),
                    }
                    match self.block(body, env) {
                        Ok(_) => {}
                        Err(Ctl::Continue(l)) if l == id => {}
                        Err(Ctl::Break(l)) if l == id => break Ok(Value::Unit),
                        Err(e) => break Err(e),
                    }
                };
                self.lex.loops.pop();
                r
            }
            ExprKind::For { pat, iter, body, .. } => self.for_of(pat, iter, body, env),
            ExprKind::Match { scrutinee, arms } => {
                let v = self.expr(scrutinee, env)?;
                for arm in arms {
                    let aenv = new_env(Some(env.clone()));
                    if self.bind(&arm.pat, &v, None, &aenv) {
                        if let Some(g) = &arm.guard
                            && !self.expr(g, &aenv)?.as_bool() {
                                continue;
                            }
                        return self.expr(&arm.body, &aenv);
                    }
                }
                Err(panic(format!("no arm matched {}", v.show())))
            }
            ExprKind::Try { body, pat, handler } => {
                let id = self.fresh_id();
                self.handlers.push(Handler::Fail { id });
                let r = self.block(body, env);
                self.handlers.pop();
                match r {
                    Err(Ctl::Unwind(h, v)) if h == id => {
                        let henv = new_env(Some(env.clone()));
                        self.bind(pat, &v, None, &henv);
                        self.block(handler, &henv)
                    }
                    other => other,
                }
            }
            ExprKind::Throw(v) => {
                let v = self.expr(v, env)?.deref();
                self.raise(v)
            }
            ExprKind::Yield(v) => {
                let v = self.expr(v, env)?;
                self.yield_value(v)
            }
            ExprKind::Return(v) => {
                let v = match v {
                    Some(v) => self.expr(v, env)?,
                    None => Value::Unit,
                };
                Err(Ctl::Return(self.lex.frame, v))
            }
            ExprKind::Break => Err(Ctl::Break(*self.lex.loops.last().unwrap_or(&0))),
            ExprKind::Continue => Err(Ctl::Continue(*self.lex.loops.last().unwrap_or(&0))),
            // Region memory is released with the block's values; nothing to do at run time here.
            ExprKind::Region { body, .. } | ExprKind::Unsafe(body) => self.block(body, env),
            ExprKind::Handle { body, effect, arms } => self.handle(body, effect, arms, env),
            ExprKind::Comptime(inner) => self.expr(inner, env),
        }
    }

    fn record(&mut self, fields: &[ast::FieldInit], env: &Env) -> R {
        let mut out = std::collections::BTreeMap::new();
        for f in fields {
            let v = match &f.value {
                Some(x) => self.expr(x, env)?,
                None => lookup(env, &f.name.name).map(|c| c.lock().expect("cell").clone()).unwrap_or(Value::Unit),
            };
            out.insert(f.name.name.clone(), v);
        }
        Ok(Value::Record(out))
    }

    fn owned_all(&mut self, items: &[Expr], env: &Env) -> Result<Vec<Value>, Ctl> {
        items.iter().map(|it| self.expr(it, env)).collect()
    }

    fn handle(&mut self, body: &ast::Block, effect: &ast::Type, arms: &[ast::HandlerArm], env: &Env) -> R {
        let ast::TypeKind::Path { segments, .. } = &effect.kind else { return Err(panic("bad effect")) };
        let Some(Binding::Def(def)) = self.prog.lookup(self.lex.module, &segments[0].name) else {
            return Err(panic("unknown effect"));
        };
        // A continuation that is kept, or resumed before more work, needs a body suspended for
        // real (§5.3).
        if super::coroutine::needed(arms) {
            return super::coroutine::handle(self, body, def, arms, env);
        }
        let id = self.fresh_id();
        self.handlers.push(Handler::User { id, effect: def, arms: arms.to_vec(), env: env.clone(), lex: self.lex.clone() });
        let r = self.block(body, env);
        self.handlers.pop();
        match r {
            Err(Ctl::Unwind(h, v)) if h == id => Ok(v),
            Err(Ctl::Abort(h, ai, args)) if h == id => {
                let arm = &arms[ai];
                let aenv = new_env(Some(env.clone()));
                for (p, a) in arm.params.iter().zip(args) {
                    define(&aenv, &p.name, a);
                }
                self.block(&arm.body, &aenv)
            }
            other => other,
        }
    }

    fn for_of(&mut self, pat: &Pattern, iter: &Expr, body: &ast::Block, env: &Env) -> R {
        let id = self.fresh_id();
        self.lex.loops.push(id);
        let generator = matches!(self.ty_of(iter.span), Some(Ty::Prim(Prim::Void)));
        let r = if generator {
            // A generator: each `yield` runs the body where it is performed (tail-resumptive).
            self.handlers.push(Handler::Loop { id, pat: pat.clone(), body: body.clone(), env: env.clone(), lex: self.lex.clone() });
            let r = self.expr(iter, env);
            self.handlers.pop();
            r.map(|_| Value::Unit)
        } else {
            let v = self.expr(iter, env)?;
            let mut out = Ok(Value::Unit);
            let mut next = super::generators::items_of(self, &v)?;
            loop {
                let item = match next(self) {
                    Ok(Some(item)) => item,
                    Ok(None) => break,
                    Err(e) => {
                        out = Err(e);
                        break;
                    }
                };
                let benv = new_env(Some(env.clone()));
                self.bind(pat, &item, None, &benv);
                match self.block(body, &benv) {
                    Ok(_) => {}
                    Err(Ctl::Continue(l)) if l == id => {}
                    Err(Ctl::Break(l)) if l == id => break,
                    Err(e) => {
                        out = Err(e);
                        break;
                    }
                }
            }
            out
        };
        self.lex.loops.pop();
        match r {
            Err(Ctl::Break(l)) if l == id => Ok(Value::Unit),
            other => other,
        }
    }

    // ---- calls ----

    fn call(&mut self, e: &Expr, callee: &Expr, args: &[Expr], env: &Env) -> R {
        let fid = self.prog.typed.get(&self.lex.owner).and_then(|t| t.calls.get(&e.span)).copied();
        if let Some(fid) = fid {
            let params = self.prog.fns[fid].scheme.params.clone();
            let mut vals = Vec::new();
            let has_self = params.first().is_some_and(|(n, _)| n == "self");
            if has_self {
                let ExprKind::Field { target, .. } = &callee.kind else { return Err(panic("bad method call")) };
                vals.push(self.arg(target, &params[0].1, env)?);
            }
            let rest = if has_self { &params[1..] } else { &params[..] };
            for (a, (_, pt)) in args.iter().zip(rest) {
                vals.push(self.arg(a, pt, env)?);
            }
            return self.call_fn_at(fid, vals, e.span);
        }
        // An effect operation, `Eff.op(…)`.
        if let ExprKind::Field { target, name } = &callee.kind
            && let ExprKind::Ident(tname) = &target.kind
                && lookup(env, tname).is_none()
                    && let Some(Binding::Def(d)) = self.prog.lookup(self.lex.module, tname)
                        && matches!(self.prog.defs[d].kind, DefKind::Effect { .. }) {
                            let vals = self.owned_all(args, env)?;
                            if self.prog.defs[d].name == "Yield" {
                                return self.yield_value(vals.into_iter().next().unwrap_or(Value::Unit));
                            }
                            if self.prog.defs[d].name == "Fail" {
                                return self.raise(vals.into_iter().next().unwrap_or(Value::Unit));
                            }
                            return self.perform(d, &name.name, vals);
                        }
        let f = self.expr(callee, env)?;
        // Arguments go as the function's type says: a `mut` parameter gets a place.
        let mut ft = self.ty_of(callee.span);
        while let Some(Ty::Borrow(_, inner)) = ft {
            ft = Some(*inner);
        }
        let vals = match ft {
            Some(Ty::Fn(fty)) if fty.params.len() == args.len() => {
                let mut vals = Vec::new();
                for (a, pt) in args.iter().zip(&fty.params) {
                    vals.push(self.arg(a, pt, env)?);
                }
                vals
            }
            _ => self.owned_all(args, env)?,
        };
        self.call_value(&f, vals)
    }

    /// Calls `fid`, giving builtins the call's span (for its recorded result type).
    fn call_fn_at(&mut self, fid: FnId, vals: Vec<Value>, span: Span) -> R {
        let (fid, tenv) = self.dispatch(fid, self.callee_tenv(fid, span))?;
        let saved = self.call_span.replace(span);
        let r = self.call_fn_with(fid, vals, tenv);
        self.call_span = saved;
        r
    }

    /// The method an operator or interpolation at `span` calls, resolved for this frame.
    fn op_target(&self, span: Span, show: bool) -> Option<(FnId, TEnv)> {
        let typed = self.prog.typed.get(&self.lex.owner)?;
        let (f, args) = if show { typed.shows.get(&span)? } else { typed.ops.get(&span)? }.clone();
        let outer: SubstMap<'_> = self.lex.tenv.iter().map(|(k, v)| (*k, v)).collect();
        let params = &self.prog.fns[f].scheme.tparams;
        let tenv: TEnv = Arc::new(params.iter().zip(&args).map(|(g, a)| (g.sym.id, subst_arg(a, &outer))).collect());
        self.dispatch(f, tenv).ok()
    }

    /// The generic arguments `fid` is called with at `span`, in terms of the caller's.
    fn callee_tenv(&self, fid: FnId, span: Span) -> TEnv {
        let Some(args) = self.prog.typed.get(&self.lex.owner).and_then(|t| t.targs.get(&span)) else { return TEnv::default() };
        let outer: SubstMap<'_> = self.lex.tenv.iter().map(|(k, v)| (*k, v)).collect();
        let params = &self.prog.fns[fid].scheme.tparams;
        Arc::new(params.iter().zip(args).map(|(g, a)| (g.sym.id, subst_arg(a, &outer))).collect())
    }

    /// A call through a bound runs the method of the impl for the type `Self` stands for.
    fn dispatch(&self, fid: FnId, tenv: TEnv) -> Result<(FnId, TEnv), Ctl> {
        let info = &self.prog.fns[fid];
        let Some(iface) = info.iface else { return Ok((fid, tenv)) };
        let tps = &info.scheme.tparams;
        let Some(GArg::Ty(self_ty)) = tenv.get(&tps[0].sym.id) else { return Err(panic(format!("no type for `Self` in `{}`", info.name))) };
        let (imp, binds) = self.prog.resolve_impl(iface, self_ty).ok_or_else(|| {
            panic(format!("no impl of `{}` for `{}`", self.prog.defs[iface].name, Show(self_ty, &*self.prog)))
        })?;
        let m = self.prog.method_for(imp, &info.name, &binds).ok_or_else(|| panic(format!("no specialized `{}`", info.name)))?;
        let mut env: HashMap<u32, GArg> = binds;
        // The method's own parameters follow the impl's; the call gave them after `Self` and the
        // interface's.
        let skip = 1 + self.prog.defs[iface].params.len();
        // A specialization has lost the impl's `comptime` parameters.
        let impl_params = self.prog.impls[imp].params.iter().filter(|g| !g.comptime || !self.prog.spec_of.contains_key(&m)).count();
        let own = self.prog.fns[m].scheme.tparams.get(impl_params..).unwrap_or(&[]);
        for (g, v) in own.iter().zip(&tps[skip..]) {
            if let Some(a) = tenv.get(&v.sym.id) {
                env.insert(g.sym.id, a.clone());
            }
        }
        Ok((m, Arc::new(env)))
    }

    /// A type in this frame's terms: its generic parameters replaced by the frame's arguments,
    /// and associated types resolved (`C.View` with `C = f32[]` is `mut f32`).
    fn concrete(&self, t: &Ty) -> Ty {
        let map: SubstMap<'_> = self.lex.tenv.iter().map(|(k, v)| (*k, v)).collect();
        let t = subst(t, &map);
        match &t {
            Ty::Assoc(base, name) => self.prog.assoc_type(&self.concrete(base), name).map_or(t.clone(), |r| self.concrete(&r)),
            _ => t,
        }
    }

    /// Evaluates an argument for a parameter: a place for a `mut` borrow, a value otherwise.
    fn arg(&mut self, a: &Expr, param: &Ty, env: &Env) -> R {
        let mut param = self.concrete(param);
        // A parameter still generic here takes the argument the way the argument's type says.
        if matches!(param, Ty::Param(_) | Ty::Assoc(..))
            && let Some(at) = self.ty_of(a.span) {
                param = self.concrete(&at);
            }
        match &param {
            Ty::Borrow(true, _) => Ok(Value::Ptr(self.place(a, env)?)),
            Ty::Borrow(false, _) | Ty::Slice(_) | Ty::Prim(Prim::Str) => self.expr(a, env),
            _ => {
                let v = self.expr(a, env)?;
                Ok(if matches!(v, Value::Ptr(_)) { v.deref() } else { v })
            }
        }
    }

    /// The array length a call's result is expected to have (for `repeat`).
    pub fn expected_len(&self) -> Option<usize> {
        match self.call_span.and_then(|s| self.ty_of(s)) {
            Some(Ty::Array(_, Len::Known(n))) => Some(n as usize),
            _ => None,
        }
    }
}

fn parse_int(s: &str) -> i128 {
    if let Some(h) = s.strip_prefix("0x") {
        i128::from_str_radix(h, 16).unwrap_or(0)
    } else if let Some(b) = s.strip_prefix("0b") {
        i128::from_str_radix(b, 2).unwrap_or(0)
    } else {
        s.parse().unwrap_or(0)
    }
}

pub fn binary(op: &str, a: &Value, b: &Value) -> R {
    use Value::*;
    Ok(match (a, b) {
        (Int(x), Int(y)) => match op {
            "+" => Int(x + y),
            "-" => Int(x - y),
            "*" => Int(x * y),
            "/" => {
                if *y == 0 {
                    return Err(panic("division by zero"));
                }
                Int(x / y)
            }
            "%" => {
                if *y == 0 {
                    return Err(panic("division by zero"));
                }
                Int(x % y)
            }
            "&" => Int(x & y),
            "|" => Int(x | y),
            "^" => Int(x ^ y),
            "<<" => Int(x << y),
            ">>" => Int(x >> y),
            "==" => Bool(x == y),
            "!=" => Bool(x != y),
            "<" => Bool(x < y),
            ">" => Bool(x > y),
            "<=" => Bool(x <= y),
            ">=" => Bool(x >= y),
            _ => return Err(panic(format!("bad operator {op}"))),
        },
        (Float(_), _) | (_, Float(_)) => {
            let (x, y) = (a.as_float(), b.as_float());
            match op {
                "+" => Float(x + y),
                "-" => Float(x - y),
                "*" => Float(x * y),
                "/" => Float(x / y),
                "==" => Bool(x == y),
                "!=" => Bool(x != y),
                "<" => Bool(x < y),
                ">" => Bool(x > y),
                "<=" => Bool(x <= y),
                ">=" => Bool(x >= y),
                _ => return Err(panic(format!("bad operator {op}"))),
            }
        }
        (Text(x), Text(y)) if op == "+" => Value::text(&format!("{x}{y}")),
        // Strings order by their bytes, and `false` before `true`.
        (Text(x), Text(y)) if matches!(op, "<" | ">" | "<=" | ">=") => Bool(compare(op, x.as_bytes().cmp(y.as_bytes()))),
        (Bool(x), Bool(y)) if matches!(op, "<" | ">" | "<=" | ">=") => Bool(compare(op, x.cmp(y))),
        _ => match op {
            "==" => Bool(a.equals(b)),
            "!=" => Bool(!a.equals(b)),
            _ => return Err(panic(format!("bad operands for {op}: {} and {}", a.show(), b.show()))),
        },
    })
}

fn compare(op: &str, o: std::cmp::Ordering) -> bool {
    use std::cmp::Ordering::*;
    match op {
        "<" => o == Less,
        ">" => o == Greater,
        "<=" => o != Greater,
        _ => o != Less,
    }
}

fn cast(v: &Value, ty: &ast::Type) -> Value {
    let ast::TypeKind::Path { segments, .. } = &ty.kind else { return v.clone() };
    let name = segments[0].name.as_str();
    match name {
        "f32" | "f64" => Value::Float(v.as_float()),
        _ => {
            let i = match v {
                Value::Float(f) => *f as i128,
                other => other.as_int(),
            };
            Value::Int(match name {
                "u8" => i & 0xff,
                "u16" => i & 0xffff,
                "u32" => i & 0xffff_ffff,
                "u64" | "usize" => i & 0xffff_ffff_ffff_ffff,
                "i8" => i as i8 as i128,
                "i16" => i as i16 as i128,
                "i32" => i as i32 as i128,
                "i64" | "isize" => i as i64 as i128,
                _ => i,
            })
        }
    }
}

/// The binding an expression reads from: `x`, `x.f`, `x.f.g`.
impl Interp {
    /// A place as a binding and the field path below it, as the ownership pass names moves.
    fn place_fields<'e>(&self, e: &'e Expr) -> Option<(&'e str, Vec<String>)> {
        match &e.kind {
            ExprKind::Ident(n) => Some((n, Vec::new())),
            ExprKind::Field { target, name } => {
                let (n, mut path) = self.place_fields(target)?;
                path.push(name.name.clone());
                Some((n, path))
            }
            ExprKind::Index { target, index } => {
                let (n, mut path) = self.place_fields(target)?;
                let mut t = self.ty_of(target.span);
                while let Some(Ty::Borrow(_, inner)) = t {
                    t = Some(*inner);
                }
                // An element of anything but a tuple is not a place moves are tracked for.
                let (ExprKind::Int(i), Some(Ty::Tuple(_))) = (&index.kind, &t) else { return None };
                path.push(i.clone());
                Some((n, path))
            }
            _ => None,
        }
    }
}

impl Interp {
    fn is_string(&self, t: &Ty) -> bool {
        match t {
            Ty::Prim(Prim::Str) => true,
            Ty::Borrow(_, inner) => self.is_string(inner),
            Ty::Named(d, _) => self.prog.known.get("String") == Some(d),
            _ => false,
        }
    }
}

fn root_name(e: &Expr) -> Option<&str> {
    match &e.kind {
        ExprKind::Ident(n) => Some(n),
        ExprKind::Field { target, .. } | ExprKind::Index { target, .. } => root_name(target),
        _ => None,
    }
}
