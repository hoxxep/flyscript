//! A direct-style interpreter with effect handlers.
//!
//! Abortive handlers unwind (`Ctl::Unwind`); tail-resumptive ones run at the point the effect is
//! performed, so a `for…of` over a generator, or an `Ask` handler that answers and resumes, costs
//! no stack capture. Continuations that must be stored — a `Gen` pulled with `next()` — run the
//! generator on its own thread, handing control back and forth (see `gen`).

use std::collections::{BTreeMap, HashMap};
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
    /// The enclosing scope, and how many of its bindings this one sees: those made before it was.
    /// A closure keeps its scope, and must not see bindings made after it.
    parent: Option<(Env, usize)>,
    bindings: Mutex<Bindings>,
}

#[derive(Default)]
struct Bindings {
    /// In the order made: a binding may shadow another in the same scope.
    vars: Vec<(String, Shared)>,
    /// The bindings made here that may need dropping, in order, with their types (§5.6).
    owned: Vec<(String, Ty)>,
    /// Field paths moved out of this scope's bindings (a whole move is the empty path).
    moved: HashMap<String, Vec<Vec<String>>>,
}

impl Scope {
    fn lock(&self) -> std::sync::MutexGuard<'_, Bindings> {
        self.bindings.lock().expect("env")
    }
}

pub type Env = Arc<Scope>;

pub fn new_env(parent: Option<Env>) -> Env {
    let parent = parent.map(|p| {
        let n = p.lock().vars.len();
        (p, n)
    });
    scope_in(parent, Vec::new())
}

fn scope_in(parent: Option<(Env, usize)>, vars: Vec<(String, Shared)>) -> Env {
    Arc::new(Scope { parent, bindings: Mutex::new(Bindings { vars, ..Bindings::default() }) })
}

/// The scope that binds `name` as seen from `env`, and the binding.
fn find<'a>(env: &'a Env, name: &str) -> Option<(&'a Env, Shared)> {
    let mut e = env;
    let mut limit = usize::MAX;
    loop {
        {
            let b = e.lock();
            if let Some((_, v)) = b.vars[..limit.min(b.vars.len())].iter().rev().find(|(n, _)| n == name) {
                return Some((e, v.clone()));
            }
        }
        let (p, n) = e.parent.as_ref()?;
        e = p;
        limit = *n;
    }
}

fn lookup(env: &Env, name: &str) -> Option<Shared> {
    find(env, name).map(|(_, v)| v)
}

pub fn define(env: &Env, name: &str, v: Value) {
    env.lock().vars.push((name.to_string(), shared(v)));
}

/// Binds `name` to an owned value of type `ty`, to be dropped when its scope ends.
fn define_owned(env: &Env, name: &str, v: Value, ty: Ty) {
    env.lock().moved.remove(name);
    env.lock().owned.push((name.to_string(), ty));
    define(env, name, v);
}

/// Records that `path` of binding `name` was moved out, in the scope that has the binding.
fn mark_moved(env: &Env, name: &str, path: Vec<String>) {
    if let Some((s, _)) = find(env, name) {
        s.lock().moved.entry(name.to_string()).or_default().push(path);
    }
}

/// The parts of binding `name` under field path `prefix` that were moved out, relative to
/// `prefix`; the empty path if the whole of it was.
fn moved_under(env: &Env, name: &str, prefix: &[String]) -> Vec<Vec<String>> {
    let Some((s, _)) = find(env, name) else { return Vec::new() };
    let moved = s.lock().moved.get(name).cloned().unwrap_or_default();
    if moved.iter().any(|m| prefix.starts_with(m)) {
        return vec![Vec::new()];
    }
    moved.iter().filter(|m| m.starts_with(prefix)).map(|m| m[prefix.len()..].to_vec()).collect()
}

/// A place assigned anew owns a value again.
fn mark_assigned(env: &Env, name: &str, prefix: &[String]) {
    if let Some((s, _)) = find(env, name)
        && let Some(moved) = s.lock().moved.get_mut(name)
    {
        moved.retain(|m| !m.starts_with(prefix));
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
    pub memo: Arc<Memo>,
    /// The temporaries lent by each statement under way, and by each body of code that runs apart
    /// from the code around it, innermost last, with where each was made: each is dropped when its
    /// statement ends, or when the same code makes the next (§5.6).
    pub temps: Vec<Vec<(Value, Ty, Span)>>,
}

/// Facts about the program the interpreter derives once and keeps, rather than per call.
#[derive(Default)]
pub struct Memo {
    fns: Mutex<HashMap<FnId, Arc<FnFacts>>>,
    /// For each definition met, whether some arguments make it need dropping.
    pub drop_shapes: Mutex<HashMap<crate::check::types::DefId, bool>>,
    /// An interface method and its `Self` type: the implementing method, its impl and the impl's
    /// arguments.
    dispatches: Mutex<HashMap<(FnId, Ty), Dispatch>>,
}

type Dispatch = (FnId, usize, HashMap<u32, GArg>);

/// A function as the interpreter calls it: its declaration, and for each parameter whether a
/// value passed for it needs dropping — `None` where that depends on the frame's type arguments.
pub struct FnFacts {
    pub decl: Option<ast::FnDecl>,
    pub drops: Vec<Option<bool>>,
    /// How an argument is passed to each parameter — `None` where the frame's type arguments say.
    pub passes: Vec<Option<Pass>>,
}

/// How an argument is passed for a parameter.
#[derive(Clone, Copy)]
pub enum Pass {
    /// A `mut` borrow: the argument's place.
    Mut,
    /// A readonly borrow of a non-`Copy` value, or a slice: the argument's place if it has one.
    /// A copied argument would hold no loan (§4.4), so its source could change while it lives.
    Lend,
    /// A readonly borrow of a `Copy` value, or a `str`: the argument's value, borrow or not.
    View,
    /// An owned value.
    Owned,
}

/// What `exit` ends the program with: a panic, so nothing cleans up, that `run` reports as the end
/// of the program, its status in the world.
pub const EXITED: &str = "\u{2}exit";

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
            memo: Arc::default(),
            temps: Vec::new(),
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
            memo: self.memo.clone(),
            temps: Vec::new(),
        }
    }

    /// What the interpreter needs of `fid` to call it, computed once.
    pub fn facts(&self, fid: FnId) -> Arc<FnFacts> {
        if let Some(f) = self.memo.fns.lock().expect("fns").get(&fid) {
            return f.clone();
        }
        let decl = self.prog.fn_decl(fid);
        let params = &self.prog.fns[fid].scheme.params;
        let generic = |t: &Ty| super::super::check::impls::contains_params(t) || matches!(t, Ty::Assoc(..));
        let drops = params.iter().map(|(_, t)| if generic(t) { None } else { Some(self.needs_drop(t)) }).collect();
        let passes = params.iter().map(|(_, t)| if generic(t) { None } else { Some(self.pass(t)) }).collect();
        let f = Arc::new(FnFacts { decl, drops, passes });
        self.memo.fns.lock().expect("fns").insert(fid, f.clone());
        f
    }

    pub fn fresh_id(&self) -> u64 {
        self.ids.fetch_add(1, Ordering::Relaxed)
    }

    pub(crate) fn ty_of(&self, span: Span) -> Option<Ty> {
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
        let facts = self.facts(fid);
        let Some(fdecl) = &facts.decl else { return Err(panic("not a function")) };
        let Some(body) = &fdecl.body else {
            // A builtin sees its impl's type arguments: a channel's destructor drops messages of
            // its element type.
            let saved = std::mem::replace(&mut self.lex.tenv, tenv);
            let r = self.builtin(fid, args);
            self.lex.tenv = saved;
            return r;
        };
        let env = new_env(None);
        let frame = self.fresh_id();
        let saved = std::mem::replace(&mut self.lex, Lex { frame, loops: Vec::new(), owner: fid, module, tenv });
        for (i, (p, a)) in fdecl.sig.params.iter().zip(args).enumerate() {
            let needs = match facts.drops.get(i).copied().flatten() {
                Some(n) => n,
                None => {
                    let t = self.frame_ty(&self.prog.fns[fid].scheme.params[i].1);
                    self.needs_drop(&t)
                }
            };
            if needs {
                let t = self.frame_ty(&self.prog.fns[fid].scheme.params[i].1);
                define_owned(&env, &p.name.name, a, t);
            } else {
                define(&env, &p.name.name, a);
            }
        }
        // What the body's value lends of its temporaries lives until it is given back.
        let r = self.home(|o| o.block(body, &env));
        // Parameters the body did not move are dropped as it returns (§5.6).
        let c = self.cleanup(&r, &env);
        let r = match (r, c) {
            (Ok(v), Err(e)) => {
                let _ = v;
                Err(e)
            }
            (r, _) => r,
        };
        // An owned result is never a borrow: `clone` gives a `Copy` value back as `self`, which
        // here may be a pointer into its source.
        let owned = !matches!(self.frame_ty(&self.prog.fns[fid].scheme.ret), Ty::Borrow(..) | Ty::Param(_) | Ty::Assoc(..));
        self.lex = saved;
        let r = match r {
            Err(Ctl::Return(f, v)) if f == frame => Ok(v),
            other => other,
        };
        match r {
            Ok(v @ Value::Ptr(_)) if owned => Ok(v.deref()),
            other => other,
        }
    }

    /// Calls a function value (closure, function, continuation).
    pub fn call_value(&mut self, f: &Value, args: Vec<Value>) -> R {
        match f.deref() {
            Value::Closure(c) => {
                let base = scope_in(c.scope.clone(), c.env.clone());
                // A `once` closure's call is its end: what it owns is dropped with it (§5.6).
                if c.once {
                    base.lock().owned.extend(c.owned.iter().cloned());
                }
                let env = new_env(Some(base.clone()));
                for (p, a) in c.params.iter().zip(args) {
                    define(&env, p, a);
                }
                let frame = self.fresh_id();
                let saved = std::mem::replace(&mut self.lex, Lex { frame, loops: Vec::new(), owner: c.owner, module: c.module, tenv: c.tenv.clone() });
                let r = self.expr(&c.body, &env);
                let c = self.cleanup(&r, &base);
                let r = match (r, c) {
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
                    true => self.home(|o| o.block(&body, &env)),
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
        // `Instant` and `Duration` are structs of nanoseconds.
        let nanos = |v: Option<&Value>| match v.map(|v| v.deref()) {
            Some(Value::Record(fs)) => fs.get("nanos").map_or(0, |n| n.as_int() as u64),
            Some(other) => other.as_int() as u64,
            None => 0,
        };
        // Sleeping waits for the virtual clock, which is its scheduling point.
        if op == "sleep" {
            self.sched.sleep(self.task, nanos(args.first()))?;
            return Ok(Value::Unit);
        }
        self.sched.yield_now(self.task)?;
        let now = self.sched.now();
        let mut w = self.world.lock().expect("world");
        Ok(match op {
            "now" => Value::Record([("nanos".to_string(), Value::Int(now as i128))].into_iter().collect::<BTreeMap<_, _>>().into()),
            "write" => {
                let bytes: Vec<u8> = match args.get(1).map(|b| b.deref()) {
                    Some(Value::List(vs)) => vs.iter().map(|b| b.as_int() as u8).collect(),
                    _ => Vec::new(),
                };
                let n = bytes.len();
                w.out.push(String::from_utf8_lossy(&bytes).into_owned());
                Value::tag("Ok", Value::Tuple(vec![Value::Int(n as i128)].into()))
            }
            "read" => Value::tag("Ok", Value::Tuple(vec![Value::Int(0)].into())),
            "wall" => Value::Int(std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_nanos() as i128)),
            "cwd" => Value::text(&if w.real_fs { std::env::current_dir().map(|d| d.display().to_string()).unwrap_or_default() } else { "/".to_string() }),
            "env" => {
                let name = args.first().map(|a| a.as_text().to_string()).unwrap_or_default();
                let found = w.env.get(&name).cloned().or_else(|| if w.real_fs { std::env::var(&name).ok() } else { None });
                match found {
                    Some(v) => Value::tag("Some", Value::Tuple(vec![Value::text(&v)].into())),
                    None => Value::tag("None", Value::Unit),
                }
            }
            "stat" | "list" | "mkdir" | "remove" | "rename" => {
                let path = |i: usize| -> String {
                    let p = args.get(i).map(|a| a.as_text().to_string()).unwrap_or_default();
                    let p = p.trim_start_matches("./").trim_end_matches('/');
                    if p == "." { String::new() } else { p.to_string() }
                };
                let result: Result<Value, &str> = if w.real_fs { real_fs(op, &path(0), &path(1)) } else { sim_fs(&mut w, op, &path(0), &path(1)) };
                match result {
                    Ok(v) => Value::tag("Ok", Value::Tuple(vec![v].into())),
                    Err(e) => Value::tag("Err", Value::Tuple(vec![Value::tag(e, Value::Unit)].into())),
                }
            }
            "run" => {
                let program = args.first().map(|a| a.as_text().to_string()).unwrap_or_default();
                let list: Vec<String> = match args.get(1).map(|a| a.deref()) {
                    Some(Value::List(vs)) => vs.iter().map(|v| v.as_text().to_string()).collect(),
                    _ => Vec::new(),
                };
                let input = args.get(2).map(|a| a.as_text().to_string()).unwrap_or_default();
                // A simulated world has no programs of its own: the machine's run, as they would.
                match run_program(&program, &list, &input) {
                    Ok((status, out, err)) => Value::tag("Ok", Value::Tuple(vec![Value::Record([
                        ("status".to_string(), Value::Int(status as i128)),
                        ("out".to_string(), Value::text(&out)),
                        ("err".to_string(), Value::text(&err)),
                    ].into_iter().collect::<BTreeMap<_, _>>().into())].into())),
                    Err(e) => Value::tag("Err", Value::Tuple(vec![Value::tag(e, Value::Unit)].into())),
                }
            }
            _ => Value::Unit,
        })
    }

    /// Performs `op` of `effect` as if from here (for a coroutine's driver).
    pub fn perform_op(&mut self, effect: usize, op: &str, args: Vec<Value>) -> R {
        self.perform(effect, op, args)
    }

    fn perform(&mut self, effect: usize, op: &str, args: Vec<Value>) -> R {
        // The innermost handler with an arm for `op`: one without passes it on (§5.2).
        let Some(pos) = self.handlers.iter().rposition(|h| matches!(h, Handler::User { effect: e, arms, .. } if *e == effect && arms.iter().any(|a| a.op.name == op))) else {
            // On a coroutine's thread, the effect is its handler's or its resumer's.
            if let Some(Handler::Coroutine { co, effect: handled }) = self.handlers.first() {
                let (co, handled) = (*co, *handled);
                return if handled == effect && super::coroutine::has_arm(self, co, op) {
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
        let Some(ai) = arms.iter().position(|a| a.op.name == op) else { unreachable!() };
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
        let r = self.home(|o| o.block(&arm.body.clone(), &aenv));
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
            self.temps.push(Vec::new());
            let at = env.lock().owned.len();
            let r = match st {
                Stmt::Let { pat, init, .. } => match self.expr(init, &env) {
                    Ok(v) => {
                        // A value bound as a borrow is lent: a temporary.
                        if matches!(self.binding_ty(pat.span), Some(Ty::Borrow(..))) {
                            self.lend_temp(&v, init)?;
                        }
                        let v = self.coerce_binding(pat, v);
                        if self.bind(pat, &v, None, &env) { Ok(Value::Unit) } else { Err(panic("pattern did not match")) }
                    }
                    Err(e) => Err(e),
                },
                Stmt::Defer(e) => {
                    defers.push(e.clone());
                    Ok(Value::Unit)
                }
                // A value nothing takes is dropped where it is made.
                Stmt::Expr(e) => match self.expr(e, &env) {
                    Ok(v) if !matches!(v, Value::Ptr(_) | Value::Unit) && !is_place(e) => match self.ty_of(e.span).map(|t| self.concrete(&t)) {
                        Some(t) if self.needs_drop(&t) => self.drop_value(v, &t, &[]).map(|()| Value::Unit),
                        _ => Ok(v),
                    },
                    r => r,
                },
            };
            // The statement's temporaries end with it, unless what it binds may hold them: then
            // they are the block's, dropped just after the binding (§5.6).
            let keeps = match st {
                Stmt::Let { pat, init, .. } => {
                    let bound = match &pat.kind {
                        PatternKind::Bind(_) => self.binding_ty(pat.span),
                        _ => self.ty_of(init.span),
                    };
                    bound.is_some_and(|t| self.prog.class(&self.concrete(&t)) == 2)
                }
                _ => false,
            };
            let r = if keeps {
                let temps = self.temps.pop().unwrap_or_default();
                let mut scope = env.lock();
                for (k, (v, t, _)) in temps.into_iter().enumerate() {
                    let name = format!("\0temporary {}", scope.vars.len());
                    scope.vars.push((name.clone(), shared(v)));
                    scope.owned.insert(at + k, (name, t));
                }
                r
            } else {
                self.end_temps(r)
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
        // `defer`s run in reverse order however the block exits (§5.6), and to their end: a
        // cancellation meanwhile takes effect after them. A panic stops the task where it is, its
        // cleanup not run (§5.7).
        if is_panic(&result) {
            return result;
        }
        let cleans = !defers.is_empty() || !env.lock().owned.is_empty();
        if cleans {
            self.sched.cleaning(self.task, true);
        }
        for d in defers.iter().rev() {
            if let Err(e) = self.home(|o| o.expr(d, &env))
                && result.is_ok() {
                    result = Err(e);
                }
        }
        // Then the block's owned bindings that were not moved out, newest first, each just
        // before the temporaries it held borrows of.
        if let Err(e) = self.drop_scope(&env)
            && result.is_ok() {
                result = Err(e);
            }
        if cleans {
            self.sched.cleaning(self.task, false);
        }
        result
    }

    /// Runs code whose temporaries are its own: a body that runs apart from the code around it.
    pub(crate) fn home(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.temps.push(Vec::new());
        let r = f(self);
        self.end_temps(r)
    }

    /// `v`, the value of `e`, is lent: unless it is a place already, it is a temporary of the
    /// statement under way, which drops the one the same code made before, on an earlier pass
    /// through a loop.
    fn lend_temp(&mut self, v: &Value, e: &Expr) -> Result<(), Ctl> {
        if matches!(v, Value::Ptr(_)) {
            return Ok(());
        }
        let Some(t) = self.ty_of(e.span).map(|t| self.concrete(&t)) else { return Ok(()) };
        if !self.needs_drop(&t) {
            return Ok(());
        }
        let Some(frame) = self.temps.last_mut() else { return Ok(()) };
        let before = frame.iter().position(|(_, _, at)| *at == e.span).map(|i| frame.remove(i));
        frame.push((v.clone(), t, e.span));
        match before {
            Some((v, t, _)) => self.drop_value(v, &t, &[]),
            None => Ok(()),
        }
    }

    /// The statement, or the call's body, whose temporaries are the innermost has ended with `r`:
    /// they are dropped, the last made first, unless a panic is passing (§5.7).
    fn end_temps(&mut self, r: R) -> R {
        let temps = self.temps.pop().unwrap_or_default();
        if is_panic(&r) {
            return r;
        }
        let mut r = r;
        for (v, t, _) in temps.into_iter().rev() {
            if let Err(e) = self.drop_value(v, &t, &[])
                && r.is_ok() {
                    r = Err(e);
                }
        }
        r
    }

    /// The cleanup of a scope left with `r`: its owned bindings dropped, unless a panic is passing,
    /// which stops the task where it is (§5.7).
    fn cleanup(&mut self, r: &R, env: &Env) -> Result<(), Ctl> {
        if is_panic(r) {
            return Ok(());
        }
        self.drop_scope(env)
    }

    /// Drops the owned bindings of a scope, newest first, except what was moved out of them. A
    /// destructor that panics leaves the others to run; the first panic is the scope's.
    fn drop_scope(&mut self, env: &Env) -> Result<(), Ctl> {
        let owned = std::mem::take(&mut env.lock().owned);
        let mut result = Ok(());
        for (name, ty) in owned.into_iter().rev() {
            let moved = env.lock().moved.get(&name).cloned().unwrap_or_default();
            let Some(cell) = env.lock().vars.iter().rev().find(|(n, _)| *n == name).map(|(_, c)| c.clone()) else { continue };
            let v = cell.lock().expect("cell").clone();
            if let Err(e) = self.drop_value(v, &ty, &moved)
                && result.is_ok() {
                    result = Err(e);
                }
        }
        result
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
                    Some(t) if !matches!(v, Value::Ptr(_)) && self.needs_drop(&t) => define_owned(env, name, v.clone(), t),
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
                // A module's constant or function: a temporary.
                None => Ok(Place { root: shared(self.expr(e, env)?), path: Vec::new() }),
            },
            ExprKind::Field { target, name } => {
                let mut p = self.place(target, env)?;
                p.path.push(Seg::Field(name.name.clone()));
                // A field that holds a borrow, of a view, denotes the borrowed place, as a binding
                // that holds one does.
                if let Value::Ptr(q) = get(&p) {
                    return Ok(q);
                }
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
                    // An out-of-bounds range is a panic of the program's, as the compiled runtimes say.
                    let len = match get(&p) {
                        Value::List(vs) => Some(vs.len()),
                        Value::Text(t) => Some(t.len()),
                        _ => None,
                    };
                    if let Some(n) = len && (lo > hi || hi > n) {
                        return Err(panic(format!("range {lo}..{hi} out of bounds (length {n})")));
                    }
                    p.path.push(Seg::Range(lo, hi));
                } else {
                    let i = self.expr(index, env)?.as_int();
                    let len = match get(&p) {
                        Value::List(vs) => Some(vs.len()),
                        Value::Text(t) => Some(t.len()),
                        _ => None,
                    };
                    if let Some(n) = len && (i < 0 || i as usize >= n) {
                        return Err(panic(format!("index {i} out of bounds (length {n})")));
                    }
                    p.path.push(Seg::Index(i as usize));
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
        let moved = self.prog.typed.get(&self.lex.owner).and_then(|t| t.moves.get(&e.span)).cloned();
        let r = self.expr_inner(e, env);
        // A value moved out of a binding is no longer the binding's to drop.
        if r.is_ok()
            && let Some(path) = moved
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
                    TagArgs::Tuple(items) => Value::Tuple(self.owned_all(items, env)?.into()),
                    TagArgs::Record(fields) => self.record(fields, env)?,
                };
                Ok(Value::tag(name, payload))
            }
            ExprKind::Record { fields, .. } => self.record(fields, env),
            ExprKind::List(items) => {
                let vs = self.owned_all(items, env)?;
                Ok(match self.ty_of(e.span) {
                    Some(Ty::Tuple(_)) => Value::Tuple(vs.into()),
                    _ => Value::List(vs.into()),
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
                    ("-", Value::Int(i)) => self.checked(-i, e.span)?,
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
                match binary(op, &a, &b)? {
                    Value::Int(i) => self.checked(i, e.span),
                    v => Ok(v),
                }
            }
            ExprKind::Assign { op, target, value } => {
                let v = self.expr(value, env)?;
                let p = self.place(target, env)?;
                let new = if *op == "=" {
                    if matches!(v, Value::Ptr(_)) && !self.ty_of(target.span).is_some_and(|t| matches!(t, Ty::Borrow(..))) { v.deref() } else { v }
                } else {
                    match binary(&op[..op.len() - 1], &get(&p).deref(), &v.deref())? {
                        Value::Int(i) => self.checked(i, target.span)?,
                        v => v,
                    }
                };
                // The value the place held is dropped before it is overwritten (§5.6).
                let fields = self.place_fields(target);
                if *op == "="
                    && let Some(t) = self.ty_of(target.span).map(|t| self.frame_ty(&t))
                    && self.needs_drop(&t)
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
                        if self.needs_drop(&ty) {
                            owned.push((name, ty));
                        }
                    }
                }
                // The rest it captures by reference, borrows as checked (§4.3): the scope it is made
                // in, as it is now.
                let n = env.lock().vars.len();
                let once = matches!(self.ty_of(e.span), Some(Ty::Fn(f)) if f.mode == crate::check::types::FnMode::Once);
                Ok(Value::Closure(Arc::new(Closure {
                    params: params.iter().map(|p| p.name.name.clone()).collect(),
                    body: (**body).clone(),
                    env: captured,
                    scope: Some((env.clone(), n)),
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
                    // A pass's temporaries, the condition's and the body's, end with it (§5.6).
                    let pass = self.home(|o| match o.expr(cond, env) {
                        Ok(c) if !c.as_bool() => Ok(Value::Bool(false)),
                        Ok(_) => o.block(body, env).map(|_| Value::Bool(true)),
                        Err(e) => Err(e),
                    });
                    match pass {
                        Ok(Value::Bool(false)) => break Ok(Value::Unit),
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
                // A place is matched where it is: an arm that takes what it binds moves it out,
                // and any other borrows it, writing in place through a `mut` borrow (§4.1).
                let place = match self.place_fields(scrutinee) {
                    Some(_) => Some(self.place(scrutinee, env)?),
                    None => None,
                };
                let v = match &place {
                    Some(p) => get(p),
                    None => self.expr(scrutinee, env)?,
                };
                for arm in arms {
                    let aenv = new_env(Some(env.clone()));
                    let takes = self.prog.typed.get(&self.lex.owner).is_some_and(|t| t.moves.contains_key(&arm.pat.span));
                    let bv = match &place {
                        Some(p) if !takes => Value::Ptr(p.clone()),
                        _ => v.clone(),
                    };
                    if self.bind(&arm.pat, &bv, None, &aenv) {
                        if let Some(g) = &arm.guard
                            && !self.expr(g, &aenv)?.as_bool() {
                                continue;
                            }
                        // The arm that took an owned part of the scrutinee moved it (§5.6).
                        if let Some(path) = self.prog.typed.get(&self.lex.owner).and_then(|t| t.moves.get(&arm.pat.span)).cloned()
                            && let Some(name) = root_name(scrutinee) {
                                mark_moved(env, name, path);
                            }
                        // What the arm took and did not move on is dropped as it ends (§5.6).
                        let r = self.expr(&arm.body, &aenv);
                        let c = self.cleanup(&r, &aenv);
                        return match (r, c) {
                            (Ok(_), Err(e)) => Err(e),
                            (r, _) => r,
                        };
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
        Ok(Value::Record(out.into()))
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
        let r = self.home(|o| o.block(body, env));
        self.handlers.pop();
        match r {
            Err(Ctl::Unwind(h, v)) if h == id => Ok(v),
            Err(Ctl::Abort(h, ai, args)) if h == id => {
                let arm = &arms[ai];
                let aenv = new_env(Some(env.clone()));
                for (p, a) in arm.params.iter().zip(args) {
                    define(&aenv, &p.name, a);
                }
                self.home(|o| o.block(&arm.body, &aenv))
            }
            other => other,
        }
    }

    fn for_of(&mut self, pat: &Pattern, iter: &Expr, body: &ast::Block, env: &Env) -> R {
        let id = self.fresh_id();
        self.lex.loops.push(id);
        let generator = matches!(self.ty_of(iter.span), Some(Ty::Prim(Prim::Void)));
        let r = if let ExprKind::Range { lo: Some(lo), hi: Some(hi) } = &iter.kind {
            let (lo, hi) = (self.expr(lo, env)?.as_int(), self.expr(hi, env)?.as_int());
            let mut out = Ok(Value::Unit);
            for i in lo..hi {
                let benv = new_env(Some(env.clone()));
                self.bind(pat, &Value::Int(i), None, &benv);
                match self.home(|o| o.block(body, &benv)) {
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
        } else if generator {
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
                // An item the body did not move on is dropped as the iteration ends (§5.6), after
                // the temporaries the iteration made.
                let r = self.home(|o| o.block(body, &benv));
                let c = self.cleanup(&r, &benv);
                let r = match (r, c) {
                    (Ok(_), Err(e)) => Err(e),
                    (r, _) => r,
                };
                match r {
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
            let facts = self.facts(fid);
            let prog = self.prog.clone();
            let params = &prog.fns[fid].scheme.params;
            let mut vals = Vec::new();
            let has_self = params.first().is_some_and(|(n, _)| n == "self");
            let receiver = match (&callee.kind, has_self) {
                (ExprKind::Field { target, .. }, true) => Some(&**target),
                (_, true) => return Err(panic("bad method call")),
                _ => None,
            };
            for (i, a) in receiver.into_iter().chain(args).enumerate() {
                let Some((_, pt)) = params.get(i) else { break };
                let pass = match facts.passes[i] {
                    Some(pass) => pass,
                    None => self.pass_at(a, pt),
                };
                vals.push(self.arg(a, pass, env)?);
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
                    let pass = self.pass_at(a, pt);
                    vals.push(self.arg(a, pass, env)?);
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
        let key = (fid, self_ty.clone());
        let found = self.memo.dispatches.lock().expect("dispatches").get(&key).cloned();
        let (m, imp, binds) = match found {
            Some(d) => d,
            None => {
                let (imp, binds) = self.prog.resolve_impl(iface, self_ty).ok_or_else(|| {
                    panic(format!("no impl of `{}` for `{}`", self.prog.defs[iface].name, Show(self_ty, &*self.prog)))
                })?;
                let m = self.prog.method_for(imp, &info.name, &binds).ok_or_else(|| panic(format!("no specialized `{}`", info.name)))?;
                self.memo.dispatches.lock().expect("dispatches").insert(key, (m, imp, binds.clone()));
                (m, imp, binds)
            }
        };
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

    /// How `a` is passed for a parameter of type `param`, in this frame.
    fn pass_at(&self, a: &Expr, param: &Ty) -> Pass {
        let mut param = self.concrete(param);
        // A parameter still generic here takes the argument the way the argument's type says.
        if matches!(param, Ty::Param(_) | Ty::Assoc(..))
            && let Some(at) = self.ty_of(a.span) {
                param = self.concrete(&at);
            }
        self.pass(&param)
    }

    /// How an argument is passed for a parameter of the concrete type `param`.
    fn pass(&self, param: &Ty) -> Pass {
        match param {
            Ty::Borrow(true, _) => Pass::Mut,
            Ty::Borrow(false, inner) if matches!(**inner, Ty::Slice(_)) || !self.prog.is_copy(inner) => Pass::Lend,
            Ty::Slice(_) => Pass::Lend,
            Ty::Borrow(false, _) | Ty::Prim(Prim::Str) => Pass::View,
            _ => Pass::Owned,
        }
    }

    /// Evaluates an argument: a place for a `mut` borrow, a value otherwise.
    fn arg(&mut self, a: &Expr, pass: Pass, env: &Env) -> R {
        let place = match &a.kind {
            // A binding holding a handle (a region reference, a cell, a channel) is passed as the
            // handle: its place would be what the handle points at.
            ExprKind::Ident(n) => lookup(env, n).is_some_and(|c| !matches!(&*c.lock().expect("cell"), Value::Ref(_) | Value::Cell(_) | Value::Native(..))),
            ExprKind::Field { .. } | ExprKind::Index { .. } => !is_range_index(a),
            _ => false,
        };
        match pass {
            Pass::Mut => Ok(Value::Ptr(self.place(a, env)?)),
            Pass::Lend if place => Ok(Value::Ptr(self.place(a, env)?)),
            Pass::Lend | Pass::View => {
                let v = self.expr(a, env)?;
                // A value made to be lent is a temporary, its statement's to drop.
                if !matches!(a.kind, ExprKind::Ident(_)) {
                    self.lend_temp(&v, a)?;
                }
                Ok(v)
            }
            Pass::Owned => {
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
            // Overflowing `i128`, the widest type, is overflowing whatever the static type is.
            "+" => Int(x.checked_add(*y).ok_or_else(|| panic("arithmetic overflow"))?),
            "-" => Int(x.checked_sub(*y).ok_or_else(|| panic("arithmetic overflow"))?),
            "*" => Int(x.checked_mul(*y).ok_or_else(|| panic("arithmetic overflow"))?),
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

/// Whether `r` is a panic passing, which stops its task without cleanup (§5.7). A generator or
/// coroutine ended early unwinds by a panic of its own, marked with a NUL, and runs its cleanup.
fn is_panic(r: &R) -> bool {
    matches!(r, Err(Ctl::Panic(m)) if !m.starts_with('\u{0}'))
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

/// The values of an integer type.
pub fn int_range(p: Prim) -> Option<(i128, i128)> {
    Some(match p {
        Prim::I8 => (i8::MIN as i128, i8::MAX as i128),
        Prim::I16 => (i16::MIN as i128, i16::MAX as i128),
        Prim::I32 => (i32::MIN as i128, i32::MAX as i128),
        Prim::I64 | Prim::Isize => (i64::MIN as i128, i64::MAX as i128),
        Prim::I128 => (i128::MIN, i128::MAX),
        Prim::U8 => (0, u8::MAX as i128),
        Prim::U16 => (0, u16::MAX as i128),
        Prim::U32 => (0, u32::MAX as i128),
        Prim::U64 | Prim::Usize => (0, u64::MAX as i128),
        _ => return None,
    })
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
    /// An integer result checked against its static type: overflow panics (§5.7).
    fn checked(&self, i: i128, span: Span) -> R {
        let t = self.ty_of(span).map(|t| self.frame_ty(&t));
        if let Some(Ty::Prim(p)) = t
            && let Some((lo, hi)) = int_range(p)
            && (i < lo || i > hi)
        {
            return Err(panic(format!("arithmetic overflow: {i} does not fit in `{}`", p.name())));
        }
        Ok(Value::Int(i))
    }

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

fn is_range_index(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Index { index, .. } if matches!(index.kind, ExprKind::Range { .. }))
}

/// Whether an expression denotes a place, whose value a statement that only names it leaves where
/// it is.
fn is_place(e: &Expr) -> bool {
    matches!(e.kind, ExprKind::Ident(_) | ExprKind::Field { .. } | ExprKind::Index { .. })
}


/// What is at a path, as `Io.stat` gives it.
fn stat_value(size: u64, dir: bool, modified: i128) -> Value {
    Value::Record([
        ("size".to_string(), Value::Int(size as i128)),
        ("dir".to_string(), Value::Bool(dir)),
        ("modified".to_string(), Value::Int(modified)),
    ].into_iter().collect::<BTreeMap<_, _>>().into())
}

fn io_err(e: &std::io::Error) -> &'static str {
    use std::io::ErrorKind::*;
    match e.kind() {
        NotFound => "NotFound",
        AlreadyExists => "Exists",
        DirectoryNotEmpty => "NotEmpty",
        PermissionDenied => "PermissionDenied",
        _ => "PermissionDenied",
    }
}

/// The file system's operations, on the machine's.
fn real_fs(op: &str, a: &str, b: &str) -> Result<Value, &'static str> {
    let a = if a.is_empty() { "." } else { a };
    match op {
        "stat" => {
            let m = std::fs::metadata(a).map_err(|e| io_err(&e))?;
            let modified = m.modified().ok().and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok()).map_or(0, |d| d.as_nanos() as i128);
            Ok(stat_value(m.len(), m.is_dir(), modified))
        }
        "list" => {
            let mut names: Vec<String> = std::fs::read_dir(a).map_err(|e| io_err(&e))?.filter_map(|e| e.ok()).map(|e| e.file_name().to_string_lossy().to_string()).collect();
            names.sort();
            Ok(Value::List(names.iter().map(|n| Value::text(n)).collect::<Vec<_>>().into()))
        }
        "mkdir" => std::fs::create_dir(a).map(|_| Value::Unit).map_err(|e| io_err(&e)),
        "remove" => {
            let m = std::fs::symlink_metadata(a).map_err(|e| io_err(&e))?;
            if m.is_dir() { std::fs::remove_dir(a) } else { std::fs::remove_file(a) }.map(|_| Value::Unit).map_err(|e| io_err(&e))
        }
        _ => std::fs::rename(a, b).map(|_| Value::Unit).map_err(|e| io_err(&e)),
    }
}

/// The same, on a simulated world's, which tests keep deterministic: what is there changed nothing.
fn sim_fs(w: &mut crate::eval::World, op: &str, a: &str, b: &str) -> Result<Value, &'static str> {
    match op {
        "stat" => {
            if let Some(f) = w.files.get(a) {
                Ok(stat_value(f.len() as u64, false, 0))
            } else if w.is_dir(a) {
                Ok(stat_value(0, true, 0))
            } else {
                Err("NotFound")
            }
        }
        "list" => {
            if w.files.contains_key(a) || !w.is_dir(a) {
                return Err("NotFound");
            }
            Ok(Value::List(w.entries(a).iter().map(|n| Value::text(n)).collect::<Vec<_>>().into()))
        }
        "mkdir" => {
            if w.files.contains_key(a) || w.is_dir(a) {
                return Err("Exists");
            }
            let parent = a.rsplit_once('/').map_or("", |(p, _)| p);
            if !w.is_dir(parent) {
                return Err("NotFound");
            }
            w.dirs.insert(a.to_string());
            Ok(Value::Unit)
        }
        "remove" => {
            if w.files.remove(a).is_some() {
                return Ok(Value::Unit);
            }
            if !w.is_dir(a) || a.is_empty() {
                return Err("NotFound");
            }
            if !w.entries(a).is_empty() {
                return Err("NotEmpty");
            }
            w.dirs.remove(a);
            Ok(Value::Unit)
        }
        _ => {
            if let Some(content) = w.files.remove(a) {
                w.files.insert(b.to_string(), content);
                Ok(Value::Unit)
            } else if w.is_dir(a) && !a.is_empty() {
                let from = format!("{a}/");
                let moved: Vec<(String, String)> = w.files.iter().filter(|(k, _)| k.starts_with(&from)).map(|(k, v)| (k.clone(), v.clone())).collect();
                for (k, v) in moved {
                    w.files.remove(&k);
                    w.files.insert(format!("{b}/{}", &k[from.len()..]), v);
                }
                let dirs: Vec<String> = w.dirs.iter().filter(|d| *d == a || d.starts_with(&from)).cloned().collect();
                for d in dirs {
                    w.dirs.remove(&d);
                    w.dirs.insert(if d == a { b.to_string() } else { format!("{b}/{}", &d[from.len()..]) });
                }
                Ok(Value::Unit)
            } else {
                Err("NotFound")
            }
        }
    }
}

/// Runs a program of the machine's to its end, given what it reads.
fn run_program(program: &str, args: &[String], input: &str) -> Result<(i32, String, String), &'static str> {
    use std::io::Write;
    let mut child = std::process::Command::new(program)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| io_err(&e))?;
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(input.as_bytes());
    }
    let out = child.wait_with_output().map_err(|e| io_err(&e))?;
    Ok((out.status.code().unwrap_or(-1), String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned()))
}
