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
use crate::check::env::{Binding, DefKind, FnId, Program};
use crate::check::types::{Len, Prim, Ty};
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
}

pub type R = Result<Value, Ctl>;

/// A lexical scope of bindings.
pub struct Scope {
    vars: Mutex<HashMap<String, Shared>>,
    parent: Option<Env>,
}

pub type Env = Arc<Scope>;

pub fn new_env(parent: Option<Env>) -> Env {
    Arc::new(Scope { vars: Mutex::new(HashMap::new()), parent })
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

fn define(env: &Env, name: &str, v: Value) {
    env.vars.lock().expect("env").insert(name.to_string(), shared(v));
}

/// Where `break`, `continue` and `return` go, lexically.
#[derive(Clone)]
pub struct Lex {
    pub frame: u64,
    pub loops: Vec<u64>,
    /// The function whose recorded types apply.
    pub owner: FnId,
    pub module: usize,
}

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
}

pub struct Interp {
    pub prog: Arc<Program>,
    pub world: Arc<Mutex<World>>,
    pub handlers: Vec<Handler>,
    pub lex: Lex,
    pub ids: Arc<AtomicU64>,
    pub gens: Arc<super::generators::Gens>,
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
            lex: Lex { frame: 0, loops: Vec::new(), owner: 0, module: 0 },
            ids: Arc::new(AtomicU64::new(1)),
            gens: Arc::new(super::generators::Gens::default()),
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
        let info = &self.prog.fns[fid];
        let decl = info.decl;
        let item = &self.prog.modules[decl.module].ast.items[decl.item];
        let fdecl = match (&item.kind, decl.method) {
            (ast::ItemKind::Function(f), None) => f.clone(),
            (ast::ItemKind::Impl(imp), Some(k)) => imp.methods[k].decl.clone(),
            _ => return Err(panic("not a function")),
        };
        let Some(body) = fdecl.body else {
            return self.builtin(fid, args);
        };
        let env = new_env(None);
        for (p, a) in fdecl.sig.params.iter().zip(args) {
            define(&env, &p.name.name, a);
        }
        let frame = self.fresh_id();
        let saved = std::mem::replace(&mut self.lex, Lex { frame, loops: Vec::new(), owner: fid, module: decl.module });
        let r = self.block(&body, &env);
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
                let env = new_env(None);
                for (n, v) in &c.env {
                    env.vars.lock().expect("env").insert(n.clone(), v.clone());
                }
                let env = new_env(Some(env));
                for (p, a) in c.params.iter().zip(args) {
                    define(&env, p, a);
                }
                let frame = self.fresh_id();
                let saved = std::mem::replace(&mut self.lex, Lex { frame, loops: Vec::new(), owner: c.owner, module: c.module });
                let r = self.expr(&c.body, &env);
                self.lex = saved;
                match r {
                    Err(Ctl::Return(f, v)) if f == frame => Ok(v),
                    other => other,
                }
            }
            Value::Func(fid) => self.call_fn(fid, args),
            Value::Resume(id) => Err(Ctl::Resume(id, args.into_iter().next().unwrap_or(Value::Unit))),
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
        }
        Err(panic(format!("uncaught failure: {}", v.show())))
    }

    /// `yield v`: runs the innermost loop body here, or hands the item to a generator's consumer.
    pub fn yield_value(&mut self, v: Value) -> R {
        let Some(pos) = self.handlers.iter().rposition(|h| matches!(h, Handler::Loop { .. } | Handler::GenYield { .. })) else {
            return Err(panic("`yield` outside any generator"));
        };
        match self.handlers[pos].clone() {
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
    fn perform(&mut self, effect: usize, op: &str, args: Vec<Value>) -> R {
        let Some(pos) = self.handlers.iter().rposition(|h| matches!(h, Handler::User { effect: e, .. } if *e == effect)) else {
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
            PatternKind::Bind(name) => {
                define(env, name, v.clone());
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
        match &e.kind {
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
                        ast::TemplatePiece::Expr(x) => out.push_str(&self.expr(x, env)?.show()),
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
            ExprKind::StructType(_) => Err(panic("`comptime` types are not evaluated yet")),
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
                set(&p, new);
                Ok(Value::Unit)
            }
            ExprKind::Cast { expr, ty } => {
                let v = self.expr(expr, env)?.deref();
                Ok(cast(&v, ty))
            }
            ExprKind::Range { .. } => Err(panic("a range can only index")),
            ExprKind::Lambda { params, body } => {
                // Capture the environment's cells: borrows by reference, as checked (§4.3).
                let mut captured = Vec::new();
                let mut e = Some(env.clone());
                while let Some(s) = e {
                    for (k, v) in s.vars.lock().expect("env").iter() {
                        if !captured.iter().any(|(n, _): &(String, Shared)| n == k) {
                            captured.push((k.clone(), v.clone()));
                        }
                    }
                    e = s.parent.clone();
                }
                Ok(Value::Closure(Arc::new(Closure {
                    params: params.iter().map(|p| p.name.name.clone()).collect(),
                    body: (**body).clone(),
                    env: captured,
                    module: self.lex.module,
                    owner: self.lex.owner,
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
        let vals = self.owned_all(args, env)?;
        self.call_value(&f, vals)
    }

    /// Calls `fid`, giving builtins the call's span (for its recorded result type).
    fn call_fn_at(&mut self, fid: FnId, vals: Vec<Value>, span: Span) -> R {
        let saved = self.call_span.replace(span);
        let r = self.call_fn(fid, vals);
        self.call_span = saved;
        r
    }

    /// Evaluates an argument for a parameter: a place for a `mut` borrow, a value otherwise.
    fn arg(&mut self, a: &Expr, param: &Ty, env: &Env) -> R {
        match param {
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
        _ => match op {
            "==" => Bool(a.equals(b)),
            "!=" => Bool(!a.equals(b)),
            _ => return Err(panic(format!("bad operands for {op}: {} and {}", a.show(), b.show()))),
        },
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
