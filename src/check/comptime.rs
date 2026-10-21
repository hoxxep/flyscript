//! `comptime` (§7): the interpreter the compiler runs, reflection over types, and expansion of
//! `comptime` constructs into ordinary syntax.
//!
//! A body containing `comptime` code — a template's, or any function's — is *expanded* before
//! it is checked: `comptime if`/`match` keep one branch, `comptime for` repeats its body, computed
//! names (`v.[e]`, `#[e]`, `[e]:`) become plain names, and references to `comptime` values become
//! literals or spliced types. The expanded body is ordinary syntax with fresh positions, in source
//! order, so the later passes treat each repeated copy as distinct code; `Program::synth` maps
//! the positions back to the source for diagnostics.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::env::{Binding, DefKind, Program, TyScope};
use super::types::*;
use crate::diag::Span;
use crate::syntax::ast::*;

/// The methods `comptime` values have; any other method of one is a run-time call on its value
/// (`f.name.toString()`).
const COMPTIME_METHODS: &[&str] = &["len", "isEmpty", "enumerate", "map", "filter", "any"];

/// Positions at or above this belong to expanded code.
pub const SYNTH_BASE: usize = 1 << 40;

/// A value computed by the compiler.
#[derive(Clone, Debug, PartialEq)]
pub enum CV {
    Unit,
    Bool(bool),
    Int(i128),
    Str(String),
    List(Vec<CV>),
    Record(BTreeMap<String, CV>),
    Tag(String, Option<Box<CV>>),
    Type(Ty),
    /// A `comptime function`, by its declaration.
    Fn(usize),
    Closure(Vec<String>, Box<Expr>, Vec<(String, Option<CV>)>),
}

impl CV {
    fn show(&self, p: &Program) -> String {
        match self {
            CV::Unit => "void".into(),
            CV::Bool(b) => b.to_string(),
            CV::Int(i) => i.to_string(),
            CV::Str(s) => s.clone(),
            CV::Type(t) => format!("{}", Show(t, p)),
            CV::List(xs) => format!("[{}]", xs.iter().map(|x| x.show(p)).collect::<Vec<_>>().join(", ")),
            CV::Record(fs) => format!("{{ {} }}", fs.iter().map(|(k, v)| format!("{k}: {}", v.show(p))).collect::<Vec<_>>().join(", ")),
            CV::Tag(n, None) => format!("#{n}"),
            CV::Tag(n, Some(v)) => format!("#{n}({})", v.show(p)),
            CV::Fn(_) | CV::Closure(..) => "function".into(),
        }
    }

    fn kind(&self) -> &'static str {
        match self {
            CV::Unit => "void",
            CV::Bool(_) => "a `bool`",
            CV::Int(_) => "an integer",
            CV::Str(_) => "a string",
            CV::List(_) => "a list",
            CV::Record(_) => "a record",
            CV::Tag(..) => "a tag",
            CV::Type(_) => "a type",
            CV::Fn(_) | CV::Closure(..) => "a function",
        }
    }
}

enum Stop {
    Error(Span, String),
    Return(CV),
}

type R<T> = Result<T, Stop>;

fn fail<T>(span: Span, msg: impl Into<String>) -> R<T> {
    Err(Stop::Error(span, msg.into()))
}

/// Expands `comptime` constructs in one function body.
pub struct Expand<'p> {
    pub p: &'p mut Program,
    module: usize,
    /// The nominal type a derivation was requested for (`impl Json for User;`): its private
    /// fields are visible to the reflection the derivation does (§7.3).
    requested: Option<DefId>,
    /// `comptime` bindings; `None` where a run-time binding shadows one.
    env: Vec<(String, Option<CV>)>,
    steps: u64,
}

const STEP_BUDGET: u64 = 1_000_000;

impl<'p> Expand<'p> {
    pub fn new(p: &'p mut Program, module: usize, requested: Option<DefId>, env: Vec<(String, CV)>) -> Expand<'p> {
        Expand { p, module, requested, env: env.into_iter().map(|(k, v)| (k, Some(v))).collect(), steps: 0 }
    }

    /// Expands a body; on error, reports it at its source position and returns `None`.
    pub fn body(&mut self, b: &Block) -> Option<Block> {
        match self.block(b) {
            Ok(b) => Some(b),
            Err(Stop::Error(span, msg)) => {
                let m = self.module;
                self.p.error(m, span, msg);
                None
            }
            Err(Stop::Return(_)) => None,
        }
    }

    // ---- positions ----

    /// A fresh position for expanded code that came from `orig`.
    fn sp(&mut self, orig: Span) -> Span {
        let orig = self.p.source_span(orig);
        let s = self.p.next_synth;
        self.p.next_synth += 1;
        self.p.synth.insert(s, orig);
        Span::new(s, s + 1)
    }

    fn ident(&mut self, i: &Ident) -> Ident {
        Ident { name: i.name.clone(), span: self.sp(i.span) }
    }

    // ---- scopes ----

    fn lookup(&self, name: &str) -> Option<&Option<CV>> {
        self.env.iter().rev().find(|(n, _)| n == name).map(|(_, v)| v)
    }

    fn ct_value(&self, name: &str) -> Option<CV> {
        self.lookup(name).cloned().flatten()
    }

    fn shadow(&mut self, name: &str) {
        if self.lookup(name).is_some() {
            self.env.push((name.to_string(), None));
        }
    }

    /// Whether `e` is computed from `comptime` values alone, as far as its root.
    fn is_ct(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Ident(n) => self.ct_value(n).is_some() || (n == "Type" && self.lookup(n).is_none()),
            ExprKind::Field { target, .. } => self.is_ct(target),
            ExprKind::Call { callee, args, .. } => match &callee.kind {
                ExprKind::Field { target, .. } => self.is_ct(target),
                // A `comptime function` applied to `comptime` values: `payloadOf(t)`.
                ExprKind::Ident(n) => {
                    self.lookup(n).is_none()
                        && matches!(self.p.lookup(self.module, n), Some(Binding::Fn(f)) if self.p.fn_decl(f).is_some_and(|d| d.sig.comptime))
                        && args.iter().all(|a| self.is_ct(a))
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// A type with `comptime` code in it, expanded (a template impl's associated type).
    pub fn expand_type(&mut self, t: &Type) -> Option<Type> {
        match self.ty(t) {
            Ok(t) => Some(t),
            Err(Stop::Error(span, msg)) => {
                let m = self.module;
                self.p.error(m, span, msg);
                None
            }
            Err(Stop::Return(_)) => None,
        }
    }

    /// A template struct's fields for one instance (§7.1); reports an error and returns `None`
    /// if its `comptime` code fails.
    pub fn struct_fields(&mut self, fields: &[Field]) -> Option<Vec<Field>> {
        match self.fields(fields) {
            Ok(f) => Some(f),
            Err(Stop::Error(span, msg)) => {
                let m = self.module;
                self.p.error(m, span, msg);
                None
            }
            Err(Stop::Return(_)) => None,
        }
    }

    // ---- expansion ----

    fn block(&mut self, b: &Block) -> R<Block> {
        let depth = self.env.len();
        let span = self.sp(b.span);
        let mut stmts = Vec::new();
        for st in &b.stmts {
            stmts.push(match st {
                Stmt::Let { mutable, pat, ty, init, span } => {
                    let span = self.sp(*span);
                    let init = self.expr(init)?;
                    let ty = ty.as_ref().map(|t| self.ty(t)).transpose()?;
                    let pat = self.pattern(pat)?;
                    Stmt::Let { mutable: *mutable, pat, ty, init, span }
                }
                Stmt::Defer(e) => Stmt::Defer(self.expr(e)?),
                Stmt::Expr(e) => Stmt::Expr(self.expr(e)?),
            });
        }
        let tail = b.tail.as_ref().map(|t| self.expr(t).map(Box::new)).transpose()?;
        self.env.truncate(depth);
        Ok(Block { stmts, tail, span })
    }

    fn scoped_block(&mut self, b: &Block) -> R<Block> {
        let depth = self.env.len();
        let r = self.block(b);
        self.env.truncate(depth);
        r
    }

    fn exprs(&mut self, es: &[Expr]) -> R<Vec<Expr>> {
        es.iter().map(|e| self.expr(e)).collect()
    }

    fn expr(&mut self, e: &Expr) -> R<Expr> {
        let span = self.sp(e.span);
        let kind = match &e.kind {
            ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Byte(_) | ExprKind::Str(_) | ExprKind::Bool(_) | ExprKind::Break | ExprKind::Continue | ExprKind::TypeRef(_) => {
                e.kind.clone()
            }
            ExprKind::Template(pieces) => ExprKind::Template(
                pieces
                    .iter()
                    .map(|p| match p {
                        TemplatePiece::Lit(s) => Ok(TemplatePiece::Lit(s.clone())),
                        TemplatePiece::Expr(e) => Ok(TemplatePiece::Expr(self.expr(e)?)),
                    })
                    .collect::<R<_>>()?,
            ),
            ExprKind::Ident(n) => match self.ct_value(n) {
                Some(v) => return self.splice(&v, e.span),
                None => ExprKind::Ident(n.clone()),
            },
            ExprKind::Tag { name, args } => ExprKind::Tag { name: name.clone(), args: self.tag_args(args)? },
            ExprKind::TagAt { name, args } => {
                let name = self.ct_name(name)?;
                ExprKind::Tag { name, args: self.tag_args(args)? }
            }
            ExprKind::Record { name, fields } => {
                let name = name.as_ref().map(|path| path.iter().map(|i| self.ident(i)).collect());
                ExprKind::Record { name, fields: self.inits(fields)? }
            }
            ExprKind::List(items) => ExprKind::List(self.list(items)?),
            ExprKind::Field { target, name } if self.is_ct(target) => {
                let v = self.eval(target)?;
                if let CV::Type(t) = v {
                    let i = self.splice_ty(t);
                    let target = Expr { kind: ExprKind::TypeRef(i), span: self.sp(target.span) };
                    ExprKind::Field { target: Box::new(target), name: self.ident(name) }
                } else {
                    let v = self.field_of(v, &name.name, name.span)?;
                    return self.splice(&v, e.span);
                }
            }
            ExprKind::Field { target, name } => ExprKind::Field { target: Box::new(self.expr(target)?), name: self.ident(name) },
            ExprKind::FieldAt { target, name } => {
                let n = self.ct_name(name)?;
                let name = Ident { name: n, span: self.sp(name.span) };
                ExprKind::Field { target: Box::new(self.expr(target)?), name }
            }
            ExprKind::Index { target, index } => ExprKind::Index { target: Box::new(self.expr(target)?), index: Box::new(self.expr(index)?) },
            ExprKind::Call { callee, type_args, args } => {
                if let ExprKind::Field { target, name } = &callee.kind
                    && self.is_ct(target)
                    && COMPTIME_METHODS.contains(&name.name.as_str())
                    && !matches!(self.eval(target)?, CV::Type(_))
                {
                    // A method of a `comptime` value: computed now (`fields.len()`).
                    let v = self.eval(e)?;
                    return self.splice(&v, e.span);
                }
                let type_args = type_args.iter().map(|t| self.ty(t)).collect::<R<_>>()?;
                // A run-time method of a `comptime` value: called on the value, spliced in.
                let callee = match &callee.kind {
                    ExprKind::Field { target, name } if self.is_ct(target) && !matches!(self.eval(target)?, CV::Type(_)) => {
                        let v = self.eval(target)?;
                        let span = self.sp(callee.span);
                        Expr { kind: ExprKind::Field { target: Box::new(self.splice(&v, target.span)?), name: self.ident(name) }, span }
                    }
                    _ => self.expr(callee)?,
                };
                ExprKind::Call { callee: Box::new(callee), type_args, args: self.exprs(args)? }
            }
            ExprKind::Unary { op, operand } => ExprKind::Unary { op, operand: Box::new(self.expr(operand)?) },
            ExprKind::BorrowMut(x) => ExprKind::BorrowMut(Box::new(self.expr(x)?)),
            ExprKind::Binary { op, lhs, rhs } => ExprKind::Binary { op, lhs: Box::new(self.expr(lhs)?), rhs: Box::new(self.expr(rhs)?) },
            ExprKind::Assign { op, target, value } => ExprKind::Assign { op, target: Box::new(self.expr(target)?), value: Box::new(self.expr(value)?) },
            ExprKind::Cast { expr, ty } => ExprKind::Cast { expr: Box::new(self.expr(expr)?), ty: self.ty(ty)? },
            ExprKind::Range { lo, hi } => ExprKind::Range {
                lo: lo.as_ref().map(|x| self.expr(x).map(Box::new)).transpose()?,
                hi: hi.as_ref().map(|x| self.expr(x).map(Box::new)).transpose()?,
            },
            ExprKind::Lambda { params, body } => {
                let depth = self.env.len();
                let params = self.params(params)?;
                let body = self.expr(body)?;
                self.env.truncate(depth);
                ExprKind::Lambda { params, body: Box::new(body) }
            }
            ExprKind::Block(b) => ExprKind::Block(self.scoped_block(b)?),
            ExprKind::If { cond, then, otherwise } => ExprKind::If {
                cond: Box::new(self.expr(cond)?),
                then: self.scoped_block(then)?,
                otherwise: otherwise.as_ref().map(|x| self.expr(x).map(Box::new)).transpose()?,
            },
            ExprKind::While { cond, body } => ExprKind::While { cond: Box::new(self.expr(cond)?), body: self.scoped_block(body)? },
            ExprKind::For { mutable, pat, iter, body } => {
                let iter = self.expr(iter)?;
                let depth = self.env.len();
                let pat = self.pattern(pat)?;
                let body = self.block(body)?;
                self.env.truncate(depth);
                ExprKind::For { mutable: *mutable, pat, iter: Box::new(iter), body }
            }
            ExprKind::Match { scrutinee, arms } => ExprKind::Match { scrutinee: Box::new(self.expr(scrutinee)?), arms: self.arms(arms)? },
            ExprKind::Try { body, pat, handler } => {
                let body = self.scoped_block(body)?;
                let depth = self.env.len();
                let pat = self.pattern(pat)?;
                let handler = self.block(handler)?;
                self.env.truncate(depth);
                ExprKind::Try { body, pat, handler }
            }
            ExprKind::Throw(x) => ExprKind::Throw(Box::new(self.expr(x)?)),
            ExprKind::Yield(x) => ExprKind::Yield(Box::new(self.expr(x)?)),
            ExprKind::Return(x) => ExprKind::Return(x.as_ref().map(|x| self.expr(x).map(Box::new)).transpose()?),
            ExprKind::Region { name, body } => ExprKind::Region { name: self.ident(name), body: self.scoped_block(body)? },
            ExprKind::Handle { body, effect, arms } => {
                let body = self.scoped_block(body)?;
                let effect = self.ty(effect)?;
                let mut out = Vec::new();
                for a in arms {
                    let depth = self.env.len();
                    for p in &a.params {
                        self.shadow(&p.name);
                    }
                    if let Some(k) = &a.resumes {
                        self.shadow(&k.name);
                    }
                    let params = a.params.iter().map(|i| self.ident(i)).collect();
                    let resumes = a.resumes.as_ref().map(|i| self.ident(i));
                    let op = self.ident(&a.op);
                    let body = self.block(&a.body)?;
                    self.env.truncate(depth);
                    out.push(HandlerArm { op, params, resumes, body });
                }
                ExprKind::Handle { body, effect, arms: out }
            }
            ExprKind::Unsafe(b) => ExprKind::Unsafe(self.scoped_block(b)?),
            ExprKind::Comptime(inner) => return self.comptime(inner, e.span),
        };
        Ok(Expr { kind, span })
    }

    /// `comptime e`: `if`, `match` and `for` choose or repeat code; anything else is computed
    /// and its value spliced in.
    fn comptime(&mut self, inner: &Expr, at: Span) -> R<Expr> {
        match &inner.kind {
            ExprKind::If { cond, then, otherwise } => {
                if self.eval_bool(cond)? {
                    let b = self.scoped_block(then)?;
                    let span = b.span;
                    Ok(Expr { kind: ExprKind::Block(b), span })
                } else {
                    match otherwise {
                        // `else if` continues the `comptime` choice.
                        Some(o) if matches!(o.kind, ExprKind::If { .. }) => self.comptime(o, at),
                        Some(o) => self.expr(o),
                        None => Ok(self.unit(at)),
                    }
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                let v = self.eval(scrutinee)?;
                for arm in arms {
                    let depth = self.env.len();
                    let mut binds = Vec::new();
                    if self.ct_match(&arm.pat, &v, &mut binds)? {
                        self.env.extend(binds.into_iter().map(|(k, v)| (k, Some(v))));
                        let guard = match &arm.guard {
                            Some(g) => self.eval_bool(g)?,
                            None => true,
                        };
                        if guard {
                            let r = self.expr(&arm.body);
                            self.env.truncate(depth);
                            return r;
                        }
                    }
                    self.env.truncate(depth);
                }
                fail(scrutinee.span, format!("no arm matches `{}`", v.show(self.p)))
            }
            ExprKind::For { pat, iter, body, .. } => {
                let items = self.eval_list(iter)?;
                let span = self.sp(at);
                let mut stmts = Vec::new();
                for item in items {
                    let depth = self.env.len();
                    let mut binds = Vec::new();
                    if !self.ct_match(pat, &item, &mut binds)? {
                        return fail(pat.span, format!("`{}` does not match this pattern", item.show(self.p)));
                    }
                    self.env.extend(binds.into_iter().map(|(k, v)| (k, Some(v))));
                    let b = self.block(body)?;
                    self.env.truncate(depth);
                    let bspan = b.span;
                    stmts.push(Stmt::Expr(Expr { kind: ExprKind::Block(b), span: bspan }));
                }
                Ok(Expr { kind: ExprKind::Block(Block { stmts, tail: None, span }), span })
            }
            _ => {
                let v = self.eval(inner)?;
                self.splice(&v, at)
            }
        }
    }

    fn unit(&mut self, at: Span) -> Expr {
        let span = self.sp(at);
        Expr { kind: ExprKind::Block(Block { stmts: Vec::new(), tail: None, span }), span }
    }

    /// A `comptime` value as syntax.
    fn splice(&mut self, v: &CV, at: Span) -> R<Expr> {
        let span = self.sp(at);
        let kind = match v {
            CV::Unit => return Ok(self.unit(at)),
            CV::Bool(b) => ExprKind::Bool(*b),
            CV::Int(i) if *i < 0 => ExprKind::Unary { op: "-", operand: Box::new(Expr { kind: ExprKind::Int((-i).to_string()), span }) },
            CV::Int(i) => ExprKind::Int(i.to_string()),
            CV::Str(s) => ExprKind::Str(s.clone()),
            CV::Type(t) => ExprKind::TypeRef(self.splice_ty(t.clone())),
            CV::List(xs) => ExprKind::List(xs.iter().map(|x| self.splice(x, at)).collect::<R<_>>()?),
            CV::Record(fs) => {
                let mut fields = Vec::new();
                for (k, x) in fs {
                    let name = Ident { name: k.clone(), span: self.sp(at) };
                    fields.push(FieldInit::new(name, Some(self.splice(x, at)?)));
                }
                ExprKind::Record { name: None, fields }
            }
            CV::Tag(n, None) => ExprKind::Tag { name: n.clone(), args: TagArgs::None },
            CV::Tag(n, Some(x)) => ExprKind::Tag { name: n.clone(), args: TagArgs::Tuple(vec![self.splice(x, at)?]) },
            CV::Fn(_) | CV::Closure(..) => return fail(at, "a `comptime` function cannot be used at run time"),
        };
        Ok(Expr { kind, span })
    }

    fn splice_ty(&mut self, t: Ty) -> usize {
        self.p.spliced.push(t);
        self.p.spliced.len() - 1
    }

    fn ct_name(&mut self, e: &Expr) -> R<String> {
        match self.eval(e)? {
            CV::Str(s) => Ok(s),
            v => fail(e.span, format!("a computed name must be a string, not {}", v.kind())),
        }
    }

    /// A list literal's items: in a list, `comptime for` contributes one item per iteration, its
    /// body, and `comptime if` the body it chooses (§7.2).
    fn list(&mut self, items: &[Expr]) -> R<Vec<Expr>> {
        let mut out = Vec::new();
        for it in items {
            let ExprKind::Comptime(inner) = &it.kind else {
                out.push(self.expr(it)?);
                continue;
            };
            match &inner.kind {
                ExprKind::For { pat, iter, body, .. } => {
                    for v in self.eval_list(iter)? {
                        let depth = self.env.len();
                        let mut binds = Vec::new();
                        if !self.ct_match(pat, &v, &mut binds)? {
                            return fail(pat.span, format!("`{}` does not match this pattern", v.show(self.p)));
                        }
                        self.env.extend(binds.into_iter().map(|(k, v)| (k, Some(v))));
                        let b = self.block(body);
                        self.env.truncate(depth);
                        let b = b?;
                        let span = b.span;
                        out.push(Expr { kind: ExprKind::Block(b), span });
                    }
                }
                ExprKind::If { cond, then, otherwise } => {
                    if self.eval_bool(cond)? {
                        let b = self.scoped_block(then)?;
                        let span = b.span;
                        out.push(Expr { kind: ExprKind::Block(b), span });
                    } else if let Some(o) = otherwise {
                        out.push(self.expr(o)?);
                    }
                }
                _ => out.push(self.expr(it)?),
            }
        }
        Ok(out)
    }

    fn tag_args(&mut self, a: &TagArgs) -> R<TagArgs> {
        Ok(match a {
            TagArgs::None => TagArgs::None,
            TagArgs::Tuple(es) => TagArgs::Tuple(self.exprs(es)?),
            TagArgs::Record(fs) => TagArgs::Record(self.inits(fs)?),
        })
    }

    fn params(&mut self, ps: &[Param]) -> R<Vec<Param>> {
        let mut out = Vec::new();
        for p in ps {
            let ty = p.ty.as_ref().map(|t| self.ty(t)).transpose()?;
            self.shadow(&p.name.name);
            out.push(Param { comptime: p.comptime, name: self.ident(&p.name), ty });
        }
        Ok(out)
    }

    // ---- sequences: what `comptime for` and `comptime if` generate ----

    fn seq<T>(&mut self, items: &[T], generated: fn(&T) -> Option<&Generate<T>>, one: fn(&mut Self, &T) -> R<T>) -> R<Vec<T>> {
        let mut out = Vec::new();
        for item in items {
            match generated(item) {
                None => out.push(one(self, item)?),
                Some(Generate::If { cond, then, otherwise }) => {
                    let chosen = if self.eval_bool(cond)? { then } else { otherwise };
                    out.extend(self.seq(chosen, generated, one)?);
                }
                Some(Generate::Do(e)) => {
                    self.eval(e)?;
                }
                Some(Generate::Match { scrutinee, arms }) => {
                    let v = self.eval(scrutinee)?;
                    let mut matched = false;
                    for (pat, items) in arms {
                        let depth = self.env.len();
                        let mut binds = Vec::new();
                        if self.ct_match(pat, &v, &mut binds)? {
                            self.env.extend(binds.into_iter().map(|(k, v)| (k, Some(v))));
                            let r = self.seq(items, generated, one);
                            self.env.truncate(depth);
                            out.extend(r?);
                            matched = true;
                            break;
                        }
                        self.env.truncate(depth);
                    }
                    if !matched {
                        return fail(scrutinee.span, format!("no arm matches `{}`", v.show(self.p)));
                    }
                }
                Some(Generate::For { pat, iter, body }) => {
                    for v in self.eval_list(iter)? {
                        let depth = self.env.len();
                        let mut binds = Vec::new();
                        if !self.ct_match(pat, &v, &mut binds)? {
                            return fail(pat.span, format!("`{}` does not match this pattern", v.show(self.p)));
                        }
                        self.env.extend(binds.into_iter().map(|(k, v)| (k, Some(v))));
                        let r = self.seq(body, generated, one);
                        self.env.truncate(depth);
                        out.extend(r?);
                    }
                }
            }
        }
        Ok(out)
    }

    fn inits(&mut self, fs: &[FieldInit]) -> R<Vec<FieldInit>> {
        self.seq(fs, |f| f.generate.as_deref(), |x, f| {
            let name = match &f.computed {
                Some(e) => Ident { name: x.ct_name(e)?, span: x.sp(f.name.span) },
                None => x.ident(&f.name),
            };
            let value = match &f.value {
                Some(v) => Some(x.expr(v)?),
                // A punned `comptime` binding is spliced: `{ n }` where `n` is `comptime`.
                None => match x.ct_value(&f.name.name) {
                    Some(v) => Some(x.splice(&v, f.name.span)?),
                    None => None,
                },
            };
            Ok(FieldInit::new(name, value))
        })
    }

    fn fields(&mut self, fs: &[Field]) -> R<Vec<Field>> {
        self.seq(fs, |f| f.generate.as_deref(), |x, f| {
            let name = match &f.computed {
                Some(e) => Ident { name: x.ct_name(e)?, span: x.sp(f.name.span) },
                None => x.ident(&f.name),
            };
            Ok(Field::new(name, x.ty(&f.ty)?, f.private))
        })
    }

    fn arms(&mut self, arms: &[MatchArm]) -> R<Vec<MatchArm>> {
        self.seq(arms, |a| a.generate.as_deref(), |x, a| {
            let depth = x.env.len();
            let pat = x.pattern(&a.pat)?;
            let guard = a.guard.as_ref().map(|g| x.expr(g)).transpose()?;
            let body = x.expr(&a.body)?;
            x.env.truncate(depth);
            Ok(MatchArm::new(pat, guard, body))
        })
    }

    // ---- types and patterns ----

    fn ty(&mut self, t: &Type) -> R<Type> {
        let span = self.sp(t.span);
        let kind = match &t.kind {
            TypeKind::Path { segments, args } if self.lookup(&segments[0].name).is_some_and(|v| v.is_some()) => {
                let mut e = Expr { kind: ExprKind::Ident(segments[0].name.clone()), span: segments[0].span };
                for s in &segments[1..] {
                    e = Expr { kind: ExprKind::Field { target: Box::new(e), name: s.clone() }, span: s.span };
                }
                if !args.is_empty() {
                    return fail(t.span, "a `comptime` type takes no type arguments");
                }
                match self.eval(&e)? {
                    CV::Type(ty) => TypeKind::Spliced(self.splice_ty(ty)),
                    v => return fail(t.span, format!("expected a type, found {}", v.kind())),
                }
            }
            TypeKind::Path { segments, args } => TypeKind::Path {
                segments: segments.iter().map(|i| self.ident(i)).collect(),
                args: args.iter().map(|a| self.ty(a)).collect::<R<_>>()?,
            },
            TypeKind::Record { fields, rest } => TypeKind::Record { fields: self.fields(fields)?, rest: rest.as_ref().map(|r| self.ident(r)) },
            TypeKind::Union { tags, rest } => TypeKind::Union {
                tags: tags
                    .iter()
                    .map(|t| {
                        Ok(TagDecl {
                            name: self.ident(&t.name),
                            payload: match &t.payload {
                                TagPayload::None => TagPayload::None,
                                TagPayload::Tuple(ts) => TagPayload::Tuple(ts.iter().map(|x| self.ty(x)).collect::<R<_>>()?),
                                TagPayload::Record(fs) => TagPayload::Record(self.fields(fs)?),
                            },
                        })
                    })
                    .collect::<R<_>>()?,
                rest: rest.as_ref().map(|r| self.ident(r)),
            },
            TypeKind::Tuple(ts) => TypeKind::Tuple(ts.iter().map(|x| self.ty(x)).collect::<R<_>>()?),
            TypeKind::EmptyRow => TypeKind::EmptyRow,
            TypeKind::Fn { mode, params, ret, uses } => {
                let depth = self.env.len();
                let params = self.params(params)?;
                let ret = Return { ty: self.ty(&ret.ty)?, from: ret.from.iter().map(|i| self.ident(i)).collect() };
                self.env.truncate(depth);
                TypeKind::Fn { mode: mode.clone(), params, ret: Box::new(ret), uses: self.uses(uses)? }
            }
            TypeKind::Array { elem, len } => TypeKind::Array {
                elem: Box::new(self.ty(elem)?),
                len: len.as_ref().map(|l| self.expr(l).map(Box::new)).transpose()?,
            },
            TypeKind::Mut(x) => TypeKind::Mut(Box::new(self.ty(x)?)),
            TypeKind::Readonly(x) => TypeKind::Readonly(Box::new(self.ty(x)?)),
            TypeKind::Ptr(x) => TypeKind::Ptr(Box::new(self.ty(x)?)),
            TypeKind::Dyn(path) => TypeKind::Dyn(path.iter().map(|i| self.ident(i)).collect()),
            TypeKind::Expr(e) => TypeKind::Expr(Box::new(self.expr(e)?)),
            TypeKind::Spliced(i) => TypeKind::Spliced(*i),
        };
        Ok(Type { kind, span })
    }

    fn uses(&mut self, u: &Option<Vec<RowItem>>) -> R<Option<Vec<RowItem>>> {
        let Some(items) = u else { return Ok(None) };
        let mut out = Vec::new();
        for it in items {
            out.push(match it {
                RowItem::Effect(t) => RowItem::Effect(self.ty(t)?),
                RowItem::Spread(i) => RowItem::Spread(self.ident(i)),
            });
        }
        Ok(Some(out))
    }

    /// A run-time pattern: its bindings shadow `comptime` ones for the rest of the scope.
    fn pattern(&mut self, p: &Pattern) -> R<Pattern> {
        let span = self.sp(p.span);
        let kind = match &p.kind {
            PatternKind::Wild => PatternKind::Wild,
            PatternKind::Bind(n) => {
                self.shadow(n);
                PatternKind::Bind(n.clone())
            }
            PatternKind::Lit(e) => match &e.kind {
                ExprKind::Comptime(inner) => {
                    let v = self.eval(inner)?;
                    PatternKind::Lit(Box::new(self.splice(&v, e.span)?))
                }
                _ => PatternKind::Lit(Box::new(self.expr(e)?)),
            },
            PatternKind::Tag { name, args } => PatternKind::Tag { name: name.clone(), args: self.tag_pats(args)? },
            PatternKind::TagAt { name, args } => {
                let name = self.ct_name(name)?;
                PatternKind::Tag { name, args: self.tag_pats(args)? }
            }
            PatternKind::Tuple(ps) => PatternKind::Tuple(ps.iter().map(|x| self.pattern(x)).collect::<R<_>>()?),
            PatternKind::Record { name, fields } => PatternKind::Record {
                name: name.as_ref().map(|path| path.iter().map(|i| self.ident(i)).collect()),
                fields: self.field_pats(fields)?,
            },
            PatternKind::Or(ps) => PatternKind::Or(ps.iter().map(|x| self.pattern(x)).collect::<R<_>>()?),
        };
        Ok(Pattern { kind, span })
    }

    fn field_pats(&mut self, fs: &[(Ident, Option<Pattern>)]) -> R<Vec<(Ident, Option<Pattern>)>> {
        let mut out = Vec::new();
        for (n, p) in fs {
            let p = match p {
                Some(p) => Some(self.pattern(p)?),
                None => {
                    self.shadow(&n.name);
                    None
                }
            };
            out.push((self.ident(n), p));
        }
        Ok(out)
    }

    fn tag_pats(&mut self, a: &TagPatArgs) -> R<TagPatArgs> {
        Ok(match a {
            TagPatArgs::None => TagPatArgs::None,
            TagPatArgs::Tuple(ps) => TagPatArgs::Tuple(ps.iter().map(|x| self.pattern(x)).collect::<R<_>>()?),
            TagPatArgs::Record(fs) => TagPatArgs::Record(self.field_pats(fs)?),
        })
    }

    // ---- the interpreter ----

    fn tick(&mut self, span: Span) -> R<()> {
        self.steps += 1;
        if self.steps > STEP_BUDGET {
            return fail(span, "`comptime` evaluation ran out of steps");
        }
        Ok(())
    }

    fn eval_bool(&mut self, e: &Expr) -> R<bool> {
        match self.eval(e)? {
            CV::Bool(b) => Ok(b),
            v => fail(e.span, format!("expected a `bool`, found {}", v.kind())),
        }
    }

    fn eval_list(&mut self, e: &Expr) -> R<Vec<CV>> {
        match self.eval(e)? {
            CV::List(xs) => Ok(xs),
            v => fail(e.span, format!("`comptime for` needs a list, found {}", v.kind())),
        }
    }

    fn eval(&mut self, e: &Expr) -> R<CV> {
        self.tick(e.span)?;
        Ok(match &e.kind {
            ExprKind::Int(s) => CV::Int(s.replace('_', "").parse().map_err(|_| Stop::Error(e.span, "bad integer".into()))?),
            ExprKind::Str(s) => CV::Str(s.clone()),
            ExprKind::Bool(b) => CV::Bool(*b),
            ExprKind::Template(pieces) => {
                let mut s = String::new();
                for p in pieces {
                    match p {
                        TemplatePiece::Lit(l) => s.push_str(l),
                        TemplatePiece::Expr(x) => {
                            let v = self.eval(x)?;
                            let _ = write!(s, "{}", v.show(self.p));
                        }
                    }
                }
                CV::Str(s)
            }
            ExprKind::Ident(n) => self.ident_value(n, e.span)?,
            ExprKind::Tag { name, args } => match args {
                TagArgs::None => CV::Tag(name.clone(), None),
                TagArgs::Tuple(xs) if xs.len() == 1 => CV::Tag(name.clone(), Some(Box::new(self.eval(&xs[0])?))),
                TagArgs::Tuple(xs) => CV::Tag(name.clone(), Some(Box::new(CV::List(xs.iter().map(|x| self.eval(x)).collect::<R<_>>()?)))),
                TagArgs::Record(fs) => CV::Tag(name.clone(), Some(Box::new(self.eval_record(fs)?))),
            },
            ExprKind::Record { fields, .. } => self.eval_record(fields)?,
            ExprKind::List(xs) => CV::List(xs.iter().map(|x| self.eval(x)).collect::<R<_>>()?),
            ExprKind::Field { target, name } => {
                let v = self.eval(target)?;
                self.field_of(v, &name.name, name.span)?
            }
            ExprKind::Index { target, index } => {
                let (v, i) = (self.eval(target)?, self.eval(index)?);
                match (v, i) {
                    (CV::List(xs), CV::Int(i)) => xs.get(i as usize).cloned().ok_or_else(|| Stop::Error(e.span, "index out of range".into()))?,
                    _ => return fail(e.span, "cannot index this `comptime` value"),
                }
            }
            ExprKind::Call { callee, args, .. } => self.eval_call(callee, args, e.span)?,
            ExprKind::Unary { op, operand } => match (*op, self.eval(operand)?) {
                ("!", CV::Bool(b)) => CV::Bool(!b),
                ("-", CV::Int(i)) => CV::Int(-i),
                (op, v) => return fail(e.span, format!("cannot apply `{op}` to {}", v.kind())),
            },
            ExprKind::Binary { op, lhs, rhs } => {
                if *op == "&&" || *op == "||" {
                    let l = self.eval_bool(lhs)?;
                    if (*op == "&&") != l {
                        return Ok(CV::Bool(l));
                    }
                    return Ok(CV::Bool(self.eval_bool(rhs)?));
                }
                let (l, r) = (self.eval(lhs)?, self.eval(rhs)?);
                binary(op, l, r).ok_or_else(|| Stop::Error(e.span, format!("cannot apply `{op}` to these `comptime` values")))?
            }
            ExprKind::Lambda { params, body } => {
                CV::Closure(params.iter().map(|p| p.name.name.clone()).collect(), body.clone(), self.env.clone())
            }
            ExprKind::Block(b) => {
                let depth = self.env.len();
                let r = self.eval_block(b);
                self.env.truncate(depth);
                r?
            }
            ExprKind::If { cond, then, otherwise } => {
                if self.eval_bool(cond)? {
                    let depth = self.env.len();
                    let r = self.eval_block(then);
                    self.env.truncate(depth);
                    r?
                } else {
                    match otherwise {
                        Some(o) => self.eval(o)?,
                        None => CV::Unit,
                    }
                }
            }
            ExprKind::Match { scrutinee, arms } => {
                let v = self.eval(scrutinee)?;
                for arm in arms {
                    let depth = self.env.len();
                    let mut binds = Vec::new();
                    if self.ct_match(&arm.pat, &v, &mut binds)? {
                        self.env.extend(binds.into_iter().map(|(k, v)| (k, Some(v))));
                        let ok = match &arm.guard {
                            Some(g) => self.eval_bool(g)?,
                            None => true,
                        };
                        if ok {
                            let r = self.eval(&arm.body);
                            self.env.truncate(depth);
                            return r;
                        }
                    }
                    self.env.truncate(depth);
                }
                return fail(scrutinee.span, format!("no arm matches `{}`", v.show(self.p)));
            }
            ExprKind::Return(v) => {
                let v = match v {
                    Some(v) => self.eval(v)?,
                    None => CV::Unit,
                };
                return Err(Stop::Return(v));
            }
            ExprKind::Comptime(x) => self.eval(x)?,
            ExprKind::TypeRef(i) => CV::Type(self.p.spliced[*i].clone()),
            _ => return fail(e.span, "this cannot be computed at compile time"),
        })
    }

    fn eval_record(&mut self, fs: &[FieldInit]) -> R<CV> {
        let mut out = BTreeMap::new();
        for f in fs {
            let v = match &f.value {
                Some(v) => self.eval(v)?,
                None => self.ident_value(&f.name.name, f.name.span)?,
            };
            out.insert(f.name.name.clone(), v);
        }
        Ok(CV::Record(out))
    }

    fn eval_block(&mut self, b: &Block) -> R<CV> {
        for st in &b.stmts {
            match st {
                Stmt::Let { pat, init, .. } => {
                    let v = self.eval(init)?;
                    let mut binds = Vec::new();
                    if !self.ct_match(pat, &v, &mut binds)? {
                        return fail(pat.span, "pattern does not match");
                    }
                    self.env.extend(binds.into_iter().map(|(k, v)| (k, Some(v))));
                }
                Stmt::Expr(e) | Stmt::Defer(e) => {
                    self.eval(e)?;
                }
            }
        }
        match &b.tail {
            Some(t) => self.eval(t),
            None => Ok(CV::Unit),
        }
    }

    fn ident_value(&mut self, n: &str, span: Span) -> R<CV> {
        if let Some(v) = self.lookup(n) {
            return match v {
                Some(v) => Ok(v.clone()),
                None => fail(span, format!("`{n}` is a run-time value; `comptime` code cannot use it")),
            };
        }
        if let Some(p) = Prim::from_name(n) {
            return Ok(CV::Type(Ty::Prim(p)));
        }
        match self.p.lookup(self.module, n) {
            Some(Binding::Const(c)) => {
                let (value, m) = (self.p.consts[c].value.clone(), self.p.consts[c].module);
                let saved = std::mem::replace(&mut self.module, m);
                let r = self.eval(&value);
                self.module = saved;
                r
            }
            Some(Binding::Fn(f)) => Ok(CV::Fn(f)),
            Some(Binding::Def(_)) => {
                let scope = TyScope { module: self.module, ..Default::default() };
                let t = Type { kind: TypeKind::Path { segments: vec![Ident { name: n.to_string(), span }], args: Vec::new() }, span };
                Ok(CV::Type(self.p.elab_ty(&t, &scope)))
            }
            None => fail(span, format!("unknown name `{n}` in `comptime` code")),
        }
    }

    fn field_of(&mut self, v: CV, name: &str, span: Span) -> R<CV> {
        match &v {
            CV::Record(fs) => fs.get(name).cloned().ok_or_else(|| Stop::Error(span, format!("no field `{name}` in `{}`", v.show(self.p)))),
            _ => fail(span, format!("{} has no field `{name}`", v.kind())),
        }
    }

    fn eval_call(&mut self, callee: &Expr, args: &[Expr], span: Span) -> R<CV> {
        if let ExprKind::Field { target, name } = &callee.kind {
            if matches!(&target.kind, ExprKind::Ident(t) if t == "Type" && self.lookup(t).is_none()) {
                let vals = args.iter().map(|a| self.eval(a)).collect::<R<Vec<_>>>()?;
                return self.reflect(&name.name, vals, span);
            }
            let recv = self.eval(target)?;
            let vals = args.iter().map(|a| self.eval(a)).collect::<R<Vec<_>>>()?;
            return self.method(recv, &name.name, vals, span);
        }
        if let ExprKind::Ident(n) = &callee.kind
            && self.lookup(n).is_none()
        {
            match n.as_str() {
                "panic" => {
                    let msg = match args.first() {
                        Some(a) => self.eval(a)?.show(self.p),
                        None => "panic".into(),
                    };
                    return fail(span, msg);
                }
                "assert" => {
                    if !self.eval_bool(&args[0])? {
                        let msg = match args.get(1) {
                            Some(a) => self.eval(a)?.show(self.p),
                            None => "assertion failed".into(),
                        };
                        return fail(span, msg);
                    }
                    return Ok(CV::Unit);
                }
                _ => {}
            }
        }
        let f = self.eval(callee)?;
        let vals = args.iter().map(|a| self.eval(a)).collect::<R<Vec<_>>>()?;
        self.apply(f, vals, span)
    }

    fn apply(&mut self, f: CV, args: Vec<CV>, span: Span) -> R<CV> {
        match f {
            CV::Closure(params, body, env) => {
                let saved = std::mem::replace(&mut self.env, env);
                self.env.extend(params.into_iter().zip(args).map(|(k, v)| (k, Some(v))));
                let r = self.eval(&body);
                self.env = saved;
                match r {
                    Err(Stop::Return(v)) => Ok(v),
                    other => other,
                }
            }
            CV::Fn(fid) => {
                let info = &self.p.fns[fid];
                let decl = info.decl;
                let module = info.module;
                let item = &self.p.modules[decl.module].ast.items[decl.item];
                let ItemKind::Function(fd) = &item.kind else { return fail(span, "not a `comptime` function") };
                if !fd.sig.comptime {
                    return fail(span, format!("`{}` is not a `comptime function`", fd.sig.name.name));
                }
                let (params, body) = (fd.sig.params.clone(), fd.body.clone());
                let Some(body) = body else { return fail(span, "this function has no body") };
                let env = params.iter().map(|p| p.name.name.clone()).zip(args).map(|(k, v)| (k, Some(v))).collect();
                let saved_env = std::mem::replace(&mut self.env, env);
                let saved_module = std::mem::replace(&mut self.module, module);
                let r = self.eval_block(&body);
                self.env = saved_env;
                self.module = saved_module;
                match r {
                    Err(Stop::Return(v)) => Ok(v),
                    other => other,
                }
            }
            v => fail(span, format!("{} is not a function", v.kind())),
        }
    }

    fn method(&mut self, recv: CV, name: &str, args: Vec<CV>, span: Span) -> R<CV> {
        match (recv, name) {
            (CV::List(xs), "len") => Ok(CV::Int(xs.len() as i128)),
            (CV::List(xs), "isEmpty") => Ok(CV::Bool(xs.is_empty())),
            (CV::List(xs), "enumerate") => Ok(CV::List(xs.into_iter().enumerate().map(|(i, x)| CV::List(vec![CV::Int(i as i128), x])).collect())),
            (CV::List(xs), "map") => {
                let f = args.into_iter().next().unwrap_or(CV::Unit);
                Ok(CV::List(xs.into_iter().map(|x| self.apply(f.clone(), vec![x], span)).collect::<R<_>>()?))
            }
            (CV::List(xs), "filter") => {
                let f = args.into_iter().next().unwrap_or(CV::Unit);
                let mut out = Vec::new();
                for x in xs {
                    if self.apply(f.clone(), vec![x.clone()], span)? == CV::Bool(true) {
                        out.push(x);
                    }
                }
                Ok(CV::List(out))
            }
            (CV::List(xs), "any") => {
                let f = args.into_iter().next().unwrap_or(CV::Unit);
                for x in xs {
                    if self.apply(f.clone(), vec![x], span)? == CV::Bool(true) {
                        return Ok(CV::Bool(true));
                    }
                }
                Ok(CV::Bool(false))
            }
            (CV::Str(s), "len") => Ok(CV::Int(s.len() as i128)),
            (v, _) => fail(span, format!("{} has no `comptime` method `{name}`", v.kind())),
        }
    }

    // ---- reflection ----

    fn reflect(&mut self, name: &str, args: Vec<CV>, span: Span) -> R<CV> {
        let Some(CV::Type(t)) = args.into_iter().next() else { return fail(span, format!("`Type.{name}` takes a type")) };
        match name {
            "info" => self.info(&t, span),
            "name" => Ok(CV::Str(format!("{}", Show(&t, &*self.p)))),
            _ => fail(span, format!("`Type` has no function `{name}`")),
        }
    }

    /// Whether reflection may see `d`'s private fields: from its own module, or for a
    /// derivation it requested.
    fn privileged(&self, d: DefId) -> bool {
        self.p.defs[d].module == self.module || self.requested == Some(d)
    }

    fn info(&mut self, t: &Ty, span: Span) -> R<CV> {
        let tag = |n: &str, v: CV| CV::Tag(n.into(), Some(Box::new(v)));
        let rec = |fs: Vec<(&str, CV)>| CV::Record(fs.into_iter().map(|(k, v)| (k.to_string(), v)).collect());
        let field = |(k, t): (&String, &Ty)| rec(vec![("name", CV::Str(k.clone())), ("type", CV::Type(t.clone()))]);
        Ok(match t {
            Ty::Prim(p) if p.is_int() => {
                let signed = matches!(p, Prim::I8 | Prim::I16 | Prim::I32 | Prim::I64 | Prim::Isize);
                let bits = match p {
                    Prim::I8 | Prim::U8 => 8,
                    Prim::I16 | Prim::U16 => 16,
                    Prim::I32 | Prim::U32 => 32,
                    _ => 64,
                };
                tag("Int", rec(vec![("signed", CV::Bool(signed)), ("bits", CV::Int(bits))]))
            }
            Ty::Prim(Prim::F32) => tag("Float", CV::Int(32)),
            Ty::Prim(Prim::F64) => tag("Float", CV::Int(64)),
            Ty::Prim(Prim::Bool) => CV::Tag("Bool".into(), None),
            Ty::Prim(Prim::Str) => CV::Tag("Str".into(), None),
            Ty::Prim(Prim::Void) => CV::Tag("Void".into(), None),
            Ty::Record(r) => tag("Record", CV::List(r.labels.iter().map(field).collect())),
            Ty::Tuple(ts) => tag("Tuple", CV::List(ts.iter().map(|t| CV::Type(t.clone())).collect())),
            Ty::Union(r) => tag("Union", CV::List(r.labels.iter().map(|(k, p)| self.tag_info(k, p)).collect())),
            Ty::Array(e, Len::Known(n)) => tag("Array", rec(vec![("item", CV::Type((**e).clone())), ("len", CV::Int(*n as i128))])),
            Ty::Slice(e) => tag("Slice", CV::Type((**e).clone())),
            Ty::Borrow(m, inner) => tag("Borrow", rec(vec![("mutable", CV::Bool(*m)), ("type", CV::Type((**inner).clone()))])),
            Ty::Named(d, args) => {
                let def = &self.p.defs[*d];
                let name = CV::Str(def.name.clone());
                let targs: Vec<CV> = args.iter().filter_map(|a| if let GArg::Ty(t) = a { Some(CV::Type(t.clone())) } else { None }).collect();
                let opaque = || tag("Opaque", rec(vec![("name", name.clone()), ("args", CV::List(targs.clone()))]));
                match &def.kind {
                    DefKind::Struct { fields: Some(_) } if def.private.is_empty() || self.privileged(*d) => {
                        let (d, args) = (*d, args.clone());
                        self.p.ensure_instance(d, &args);
                        let name = CV::Str(self.p.defs[d].name.clone());
                        let fs = self.p.struct_fields(d, &args).unwrap_or_default();
                        tag("Struct", rec(vec![("name", name.clone()), ("fields", CV::List(fs.iter().map(|(k, t)| field((k, t))).collect()))]))
                    }
                    DefKind::Enum { tags } => {
                        let tags: Vec<(String, Ty)> = def
                            .tag_order
                            .iter()
                            .filter_map(|k| tags.get(k).map(|t| (k.clone(), super::env::subst_params(t, &def.params, args))))
                            .collect();
                        let infos = tags.iter().map(|(k, p)| self.tag_info(k, p)).collect();
                        tag("Enum", rec(vec![("name", name.clone()), ("tags", CV::List(infos))]))
                    }
                    _ => opaque(),
                }
            }
            Ty::Fn(_) => CV::Tag("Fn".into(), None),
            _ => return fail(span, format!("`{}` cannot be reflected on", Show(t, &*self.p))),
        })
    }

    /// A tag's name and payload: none, the one type of `#A(T)`, or the tuple or record of a
    /// larger payload, which `#A(x)` binds whole (§3.2).
    fn tag_info(&self, name: &str, payload: &Ty) -> CV {
        let p = match payload {
            Ty::Prim(Prim::Void) => CV::Tag("None".into(), None),
            Ty::Tuple(ts) if ts.len() == 1 => CV::Tag("Some".into(), Some(Box::new(CV::Type(ts[0].clone())))),
            t => CV::Tag("Some".into(), Some(Box::new(CV::Type(t.clone())))),
        };
        CV::Record([("name".to_string(), CV::Str(name.into())), ("payload".to_string(), p)].into_iter().collect())
    }

    // ---- `comptime` patterns ----

    fn ct_match(&mut self, p: &Pattern, v: &CV, out: &mut Vec<(String, CV)>) -> R<bool> {
        Ok(match (&p.kind, v) {
            (PatternKind::Wild, _) => true,
            (PatternKind::Bind(n), v) => {
                out.push((n.clone(), v.clone()));
                true
            }
            (PatternKind::Lit(e), v) => {
                let lit = self.eval(e)?;
                &lit == v
            }
            (PatternKind::Tag { name, args }, CV::Tag(n, payload)) => {
                if name != n {
                    return Ok(false);
                }
                match (args, payload) {
                    (TagPatArgs::None, _) => true,
                    (TagPatArgs::Tuple(ps), Some(x)) if ps.len() == 1 => self.ct_match(&ps[0], x, out)?,
                    (TagPatArgs::Tuple(ps), Some(x)) => match &**x {
                        CV::List(xs) if xs.len() == ps.len() => {
                            for (p, x) in ps.iter().zip(xs) {
                                if !self.ct_match(p, x, out)? {
                                    return Ok(false);
                                }
                            }
                            true
                        }
                        _ => false,
                    },
                    (TagPatArgs::Record(fs), Some(x)) => self.ct_record(fs, x, out)?,
                    _ => false,
                }
            }
            (PatternKind::Tuple(ps), CV::List(xs)) if ps.len() == xs.len() => {
                for (p, x) in ps.iter().zip(xs) {
                    if !self.ct_match(p, x, out)? {
                        return Ok(false);
                    }
                }
                true
            }
            (PatternKind::Record { fields, .. }, v) => self.ct_record(fields, v, out)?,
            (PatternKind::Or(ps), v) => {
                for p in ps {
                    let mut binds = Vec::new();
                    if self.ct_match(p, v, &mut binds)? {
                        out.extend(binds);
                        return Ok(true);
                    }
                }
                false
            }
            _ => false,
        })
    }

    fn ct_record(&mut self, fs: &[(Ident, Option<Pattern>)], v: &CV, out: &mut Vec<(String, CV)>) -> R<bool> {
        let CV::Record(r) = v else { return Ok(false) };
        for (n, p) in fs {
            let Some(x) = r.get(&n.name) else { return Ok(false) };
            match p {
                Some(p) => {
                    if !self.ct_match(p, x, out)? {
                        return Ok(false);
                    }
                }
                None => out.push((n.name.clone(), x.clone())),
            }
        }
        Ok(true)
    }
}

fn binary(op: &str, l: CV, r: CV) -> Option<CV> {
    Some(match (op, l, r) {
        ("==", l, r) => CV::Bool(l == r),
        ("!=", l, r) => CV::Bool(l != r),
        ("+", CV::Int(a), CV::Int(b)) => CV::Int(a + b),
        ("-", CV::Int(a), CV::Int(b)) => CV::Int(a - b),
        ("*", CV::Int(a), CV::Int(b)) => CV::Int(a * b),
        ("/", CV::Int(a), CV::Int(b)) if b != 0 => CV::Int(a / b),
        ("%", CV::Int(a), CV::Int(b)) if b != 0 => CV::Int(a % b),
        ("&", CV::Int(a), CV::Int(b)) => CV::Int(a & b),
        ("|", CV::Int(a), CV::Int(b)) => CV::Int(a | b),
        ("<<", CV::Int(a), CV::Int(b)) if (0..127).contains(&b) => CV::Int(a << b),
        (">>", CV::Int(a), CV::Int(b)) if (0..127).contains(&b) => CV::Int(a >> b),
        ("<", CV::Int(a), CV::Int(b)) => CV::Bool(a < b),
        ("<=", CV::Int(a), CV::Int(b)) => CV::Bool(a <= b),
        (">", CV::Int(a), CV::Int(b)) => CV::Bool(a > b),
        (">=", CV::Int(a), CV::Int(b)) => CV::Bool(a >= b),
        ("+", CV::Str(a), CV::Str(b)) => CV::Str(a + &b),
        ("+", CV::List(mut a), CV::List(b)) => {
            a.extend(b);
            CV::List(a)
        }
        _ => return None,
    })
}

/// Whether a body uses `comptime` code, and so must be expanded before checking.
pub fn block_has_comptime(b: &Block) -> bool {
    b.stmts.iter().any(|s| match s {
        Stmt::Let { init, ty, .. } => expr_has(init) || ty.as_ref().is_some_and(ty_has),
        Stmt::Defer(e) | Stmt::Expr(e) => expr_has(e),
    }) || b.tail.as_deref().is_some_and(expr_has)
}

fn ty_has(t: &Type) -> bool {
    match &t.kind {
        TypeKind::Record { fields, .. } => fields.iter().any(|f| f.generate.is_some() || f.computed.is_some() || ty_has(&f.ty)),
        TypeKind::Path { args, .. } => args.iter().any(ty_has),
        TypeKind::Tuple(ts) => ts.iter().any(ty_has),
        TypeKind::Mut(x) | TypeKind::Readonly(x) | TypeKind::Ptr(x) => ty_has(x),
        TypeKind::Array { elem, .. } => ty_has(elem),
        _ => false,
    }
}

fn expr_has(e: &Expr) -> bool {
    let has_inits = |fs: &[FieldInit]| fs.iter().any(|f| f.generate.is_some() || f.computed.is_some() || f.value.as_ref().is_some_and(expr_has));
    match &e.kind {
        ExprKind::Comptime(_) | ExprKind::FieldAt { .. } | ExprKind::TagAt { .. } => true,
        ExprKind::Template(ps) => ps.iter().any(|p| matches!(p, TemplatePiece::Expr(e) if expr_has(e))),
        ExprKind::Tag { args, .. } => match args {
            TagArgs::None => false,
            TagArgs::Tuple(es) => es.iter().any(expr_has),
            TagArgs::Record(fs) => has_inits(fs),
        },
        ExprKind::Record { fields, .. } => has_inits(fields),
        ExprKind::List(es) => es.iter().any(expr_has),
        ExprKind::Field { target, .. } => expr_has(target),
        ExprKind::Index { target, index } => expr_has(target) || expr_has(index),
        ExprKind::Call { callee, args, type_args } => expr_has(callee) || args.iter().any(expr_has) || type_args.iter().any(ty_has),
        ExprKind::Unary { operand, .. } => expr_has(operand),
        ExprKind::BorrowMut(x) | ExprKind::Throw(x) | ExprKind::Yield(x) => expr_has(x),
        ExprKind::Binary { lhs, rhs, .. } => expr_has(lhs) || expr_has(rhs),
        ExprKind::Assign { target, value, .. } => expr_has(target) || expr_has(value),
        ExprKind::Cast { expr, ty } => expr_has(expr) || ty_has(ty),
        ExprKind::Range { lo, hi } => lo.as_deref().is_some_and(expr_has) || hi.as_deref().is_some_and(expr_has),
        ExprKind::Lambda { body, .. } => expr_has(body),
        ExprKind::Block(b) | ExprKind::Unsafe(b) | ExprKind::Region { body: b, .. } => block_has_comptime(b),
        ExprKind::If { cond, then, otherwise } => expr_has(cond) || block_has_comptime(then) || otherwise.as_deref().is_some_and(expr_has),
        ExprKind::While { cond, body } => expr_has(cond) || block_has_comptime(body),
        ExprKind::For { iter, body, .. } => expr_has(iter) || block_has_comptime(body),
        ExprKind::Match { scrutinee, arms } => {
            expr_has(scrutinee)
                || arms.iter().any(|a| a.generate.is_some() || matches!(&a.pat.kind, PatternKind::TagAt { .. } | PatternKind::Lit(_)) && pat_has(&a.pat) || expr_has(&a.body) || a.guard.as_ref().is_some_and(expr_has))
        }
        ExprKind::Try { body, handler, .. } => block_has_comptime(body) || block_has_comptime(handler),
        ExprKind::Return(x) => x.as_deref().is_some_and(expr_has),
        ExprKind::Handle { body, arms, .. } => block_has_comptime(body) || arms.iter().any(|a| block_has_comptime(&a.body)),
        _ => false,
    }
}

fn pat_has(p: &Pattern) -> bool {
    match &p.kind {
        PatternKind::TagAt { .. } => true,
        PatternKind::Lit(e) => matches!(e.kind, ExprKind::Comptime(_)),
        _ => false,
    }
}
