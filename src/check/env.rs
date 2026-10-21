//! The program: loaded modules, their declarations, and elaboration of syntax into types.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

use super::types::*;
use crate::diag::{Diagnostic, Span};
use crate::syntax::ast::{self, ItemKind, TypeKind};
use crate::syntax::{parse_declarations, parse_module};

/// The standard library, compiled into the checker.
const STD: &[(&str, &str)] = &[
    ("std/prelude", include_str!("../../std/prelude.d.fly")),
    ("std/region", include_str!("../../std/region.d.fly")),
    ("std/net", include_str!("../../std/net.d.fly")),
    ("std/io", include_str!("../../std/io.d.fly")),
    ("std/collections", include_str!("../../std/collections.d.fly")),
    ("std/iter", include_str!("../../std/iter.d.fly")),
    ("std/par", include_str!("../../std/par.d.fly")),
    ("std/layout", include_str!("../../std/layout.d.fly")),
    ("std/sync", include_str!("../../std/sync.d.fly")),
];

pub struct Module {
    pub name: String,
    pub file: String,
    pub source: String,
    pub ast: ast::Module,
    pub is_std: bool,
    pub scope: HashMap<String, Binding>,
    pub exports: HashMap<String, Binding>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Binding {
    Def(DefId),
    Fn(FnId),
}

pub type FnId = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PKind {
    Type,
    Region,
    Row,
    Len,
}

#[derive(Clone, Debug)]
pub struct GParam {
    pub sym: Sym,
    pub kind: PKind,
    pub bounds: Vec<Ty>,
    pub default: Option<GArg>,
}

#[derive(Clone, Debug)]
pub struct Scheme {
    pub tparams: Vec<GParam>,
    pub params: Vec<(String, Ty)>,
    pub ret: Ty,
    /// `None`: not declared, to be inferred from the body (non-exported functions only).
    pub effects: Option<EffRow>,
}

#[derive(Debug)]
pub enum DefKind {
    Struct { fields: Option<Vec<(String, Ty)>> },
    Enum { tags: BTreeMap<String, Ty> },
    Alias { ty: Ty },
    Interface { methods: Vec<(String, Scheme)>, assoc: Vec<String> },
    Effect { ops: Vec<(String, Scheme)> },
}

#[derive(Debug)]
pub struct Def {
    pub name: String,
    pub module: usize,
    pub params: Vec<GParam>,
    pub kind: DefKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub struct DeclRef {
    pub module: usize,
    pub item: usize,
    pub method: Option<usize>,
}

#[derive(Debug)]
pub struct FnInfo {
    pub name: String,
    pub module: usize,
    pub scheme: Scheme,
    pub decl: DeclRef,
    pub exported: bool,
    pub impl_id: Option<usize>,
    pub has_body: bool,
}

#[derive(Debug)]
pub struct Impl {
    pub module: usize,
    pub params: Vec<GParam>,
    pub target: Ty,
    pub interface: Option<(DefId, Vec<GArg>)>,
    pub methods: Vec<FnId>,
}

pub struct Program {
    pub modules: Vec<Module>,
    pub defs: Vec<Def>,
    pub fns: Vec<FnInfo>,
    pub impls: Vec<Impl>,
    pub diags: Vec<(usize, Diagnostic)>,
    next_sym: u32,
    /// Well-known declarations the checker needs by identity.
    pub known: HashMap<&'static str, DefId>,
    /// Effects inferred for functions declared without `uses`; `None` while being inferred.
    pub inferred: HashMap<FnId, Option<EffRow>>,
    /// Functions whose bodies have been checked.
    pub checked: std::collections::HashSet<FnId>,
}

impl Names for Program {
    fn def_name(&self, def: DefId) -> String {
        self.defs.get(def).map_or_else(|| "?".to_string(), |d| d.name.clone())
    }
}

/// Elaboration scope: generic parameters in scope, `Self`, and the region used for elision.
#[derive(Clone, Default)]
pub struct TyScope {
    pub module: usize,
    pub params: HashMap<String, (Sym, PKind)>,
    pub self_ty: Option<Ty>,
    pub elided_region: Option<Region>,
}

impl TyScope {
    pub fn with_params(&self, params: &[GParam]) -> TyScope {
        let mut s = self.clone();
        for p in params {
            s.params.insert(p.sym.name.clone(), (p.sym.clone(), p.kind));
        }
        let regions: Vec<&GParam> = params.iter().filter(|p| p.kind == PKind::Region).collect();
        if regions.len() == 1 {
            s.elided_region = Some(Region::Param(regions[0].sym.clone()));
        }
        s
    }
}

impl Program {
    /// Loads the given entry files, everything they import, and the standard library.
    pub fn load(entries: &[PathBuf]) -> Program {
        let mut p = Program {
            modules: Vec::new(),
            defs: Vec::new(),
            fns: Vec::new(),
            impls: Vec::new(),
            diags: Vec::new(),
            next_sym: 0,
            known: HashMap::new(),
            inferred: HashMap::new(),
            checked: Default::default(),
        };
        for (name, source) in STD {
            p.add_module(name.to_string(), format!("<{name}.d.fly>"), source.to_string(), true);
        }
        let mut queue: Vec<PathBuf> = entries.to_vec();
        while let Some(path) = queue.pop() {
            let name = path.with_extension("").to_string_lossy().to_string();
            if p.modules.iter().any(|m| m.name == name) {
                continue;
            }
            let source = match std::fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => {
                    p.diags.push((usize::MAX, Diagnostic::new(Span::default(), format!("{}: {e}", path.display()))));
                    continue;
                }
            };
            let idx = p.add_module(name, path.display().to_string(), source, false);
            for item in &p.modules[idx].ast.items {
                if let ItemKind::Import { from, .. } = &item.kind
                    && let Some(rel) = from.strip_prefix("./") {
                        queue.push(path.parent().unwrap_or(Path::new(".")).join(format!("{rel}.fly")));
                    }
            }
        }
        p.declare();
        p
    }

    fn add_module(&mut self, name: String, file: String, source: String, is_std: bool) -> usize {
        let parsed = if is_std { parse_declarations(&source) } else { parse_module(&source) };
        let idx = self.modules.len();
        let ast = parsed.unwrap_or_else(|d| {
            self.diags.push((idx, d));
            ast::Module { items: Vec::new() }
        });
        self.modules.push(Module { name, file, source, ast, is_std, scope: HashMap::new(), exports: HashMap::new() });
        idx
    }

    pub fn error(&mut self, module: usize, span: Span, msg: impl Into<String>) {
        self.diags.push((module, Diagnostic::new(span, msg)));
    }

    pub fn fresh_sym(&mut self, name: &str) -> Sym {
        self.next_sym += 1;
        Sym { id: self.next_sym, name: name.to_string() }
    }

    pub fn module_named(&self, name: &str) -> Option<usize> {
        self.modules.iter().position(|m| m.name == name)
    }

    // ---- declaration ----

    fn declare(&mut self) {
        // Pass 1: names.
        for m in 0..self.modules.len() {
            let items = std::mem::take(&mut self.modules[m].ast.items);
            for (i, item) in items.iter().enumerate() {
                let (name, binding) = match &item.kind {
                    ItemKind::Struct(s) => (s.name.name.clone(), Binding::Def(self.placeholder(&s.name, m))),
                    ItemKind::Enum(e) => (e.name.name.clone(), Binding::Def(self.placeholder(&e.name, m))),
                    ItemKind::TypeAlias(a) => (a.name.name.clone(), Binding::Def(self.placeholder(&a.name, m))),
                    ItemKind::Interface(x) => {
                        let id = self.placeholder(&x.name, m);
                        // Kinds are known before elaboration, so declarations may refer to
                        // themselves (`effect Io { start(task: () => void uses Io) … }`).
                        self.defs[id].kind = DefKind::Interface { methods: Vec::new(), assoc: Vec::new() };
                        (x.name.name.clone(), Binding::Def(id))
                    }
                    ItemKind::Effect(e) => {
                        let id = self.placeholder(&e.name, m);
                        self.defs[id].kind = DefKind::Effect { ops: Vec::new() };
                        (e.name.name.clone(), Binding::Def(id))
                    }
                    ItemKind::Function(f) => {
                        let id = self.fns.len();
                        self.fns.push(FnInfo {
                            name: f.sig.name.name.clone(),
                            module: m,
                            scheme: Scheme { tparams: Vec::new(), params: Vec::new(), ret: Ty::Error, effects: None },
                            decl: DeclRef { module: m, item: i, method: None },
                            exported: item.exported,
                            impl_id: None,
                            has_body: f.body.is_some(),
                        });
                        (f.sig.name.name.clone(), Binding::Fn(id))
                    }
                    _ => continue,
                };
                if self.modules[m].scope.insert(name.clone(), binding).is_some() {
                    self.error(m, item.span, format!("`{name}` is declared twice"));
                }
                if item.exported || self.modules[m].is_std {
                    self.modules[m].exports.insert(name, binding);
                }
            }
            self.modules[m].ast.items = items;
        }
        for name in ["Fail", "Yield", "Region", "Io", "String", "Ref", "Vec", "Soa", "Iterable", "LentBy", "Copy", "Send"] {
            let prelude = self.module_named("std/prelude").expect("prelude");
            let layout = self.module_named("std/layout").expect("layout");
            let found = self.modules[prelude].exports.get(name).or_else(|| self.modules[layout].exports.get(name));
            if let Some(Binding::Def(d)) = found {
                self.known.insert(name, *d);
            }
        }
        // Pass 2: imports and the prelude.
        let prelude = self.module_named("std/prelude").expect("prelude");
        let prelude_exports = self.modules[prelude].exports.clone();
        for m in 0..self.modules.len() {
            if m != prelude {
                for (k, v) in &prelude_exports {
                    self.modules[m].scope.entry(k.clone()).or_insert(*v);
                }
            }
            let items = std::mem::take(&mut self.modules[m].ast.items);
            for item in &items {
                let ItemKind::Import { names, from } = &item.kind else { continue };
                let target = if let Some(rel) = from.strip_prefix("./") {
                    let dir = Path::new(&self.modules[m].name).parent().unwrap_or(Path::new("")).to_path_buf();
                    self.module_named(&dir.join(rel).to_string_lossy())
                } else {
                    self.module_named(from)
                };
                let Some(target) = target else {
                    self.error(m, item.span, format!("no module `{from}`"));
                    continue;
                };
                for n in names {
                    match self.modules[target].exports.get(&n.name).copied() {
                        Some(b) => {
                            self.modules[m].scope.insert(n.name.clone(), b);
                        }
                        None => self.error(m, n.span, format!("module `{from}` does not export `{}`", n.name)),
                    }
                }
            }
            self.modules[m].ast.items = items;
        }
        // Pass 3: elaborate declarations, then impls, then function signatures.
        for m in 0..self.modules.len() {
            let items = std::mem::take(&mut self.modules[m].ast.items);
            for item in &items {
                self.elaborate_def(m, item);
            }
            self.modules[m].ast.items = items;
        }
        for m in 0..self.modules.len() {
            let items = std::mem::take(&mut self.modules[m].ast.items);
            for (i, item) in items.iter().enumerate() {
                match &item.kind {
                    ItemKind::Impl(imp) => self.elaborate_impl(m, i, imp),
                    ItemKind::Function(f) => {
                        let scope = TyScope { module: m, ..Default::default() };
                        let scheme = self.elaborate_sig(&f.sig, &scope, None);
                        let Some(Binding::Fn(id)) = self.modules[m].scope.get(&f.sig.name.name).copied() else { continue };
                        if item.exported && scheme.effects.is_none() {
                            self.fns[id].scheme = Scheme { effects: Some(EffRow::pure()), ..scheme };
                        } else {
                            self.fns[id].scheme = scheme;
                        }
                    }
                    _ => {}
                }
            }
            self.modules[m].ast.items = items;
        }
    }

    fn placeholder(&mut self, name: &ast::Ident, module: usize) -> DefId {
        self.defs.push(Def {
            name: name.name.clone(),
            module,
            params: Vec::new(),
            kind: DefKind::Struct { fields: None },
            span: name.span,
        });
        self.defs.len() - 1
    }

    pub fn type_params(&mut self, params: &[ast::TypeParam], scope: &TyScope) -> Vec<GParam> {
        let mut out = Vec::new();
        for p in params {
            let (name, kind) = match p {
                ast::TypeParam::Region { name, .. } => (name, PKind::Region),
                ast::TypeParam::Row { name, .. } => (name, PKind::Row),
                ast::TypeParam::Comptime { name, .. } => (name, PKind::Len),
                ast::TypeParam::Type { name, .. } => (name, PKind::Type),
            };
            let sym = self.fresh_sym(&name.name);
            out.push(GParam { sym, kind, bounds: Vec::new(), default: None });
        }
        // Bounds and defaults may mention earlier parameters.
        let inner = scope.with_params(&out);
        for (gp, p) in out.iter_mut().zip(params) {
            match p {
                ast::TypeParam::Type { bounds, default, .. } => {
                    gp.bounds = bounds.iter().map(|b| self.elab_ty(b, &inner)).collect();
                    gp.default = default.as_ref().map(|d| GArg::Ty(self.elab_ty(d, &inner)));
                }
                ast::TypeParam::Row { default: Some(d), .. } => gp.default = Some(GArg::Row(self.elab_row_type(d, &inner))),
                ast::TypeParam::Region { default: Some(d), .. } => gp.default = Some(GArg::Region(self.elab_region(d, &inner))),
                _ => {}
            }
        }
        out
    }

    fn elaborate_def(&mut self, m: usize, item: &ast::Item) {
        let scope = TyScope { module: m, ..Default::default() };
        let (name, params) = match &item.kind {
            ItemKind::Struct(s) => (&s.name, &s.params),
            ItemKind::Enum(e) => (&e.name, &e.params),
            ItemKind::TypeAlias(a) => (&a.name, &a.params),
            ItemKind::Interface(x) => (&x.name, &x.params),
            ItemKind::Effect(e) => (&e.name, &e.params),
            _ => return,
        };
        let Some(Binding::Def(id)) = self.modules[m].scope.get(&name.name).copied() else { return };
        let gparams = self.type_params(params, &scope);
        self.defs[id].params = gparams.clone();
        let inner = scope.with_params(&gparams);
        let kind = match &item.kind {
            ItemKind::Struct(s) => DefKind::Struct {
                fields: s.fields.as_ref().map(|fs| fs.iter().map(|f| (f.name.name.clone(), self.elab_ty(&f.ty, &inner))).collect()),
            },
            ItemKind::Enum(e) => DefKind::Enum {
                tags: e.tags.iter().map(|t| (t.name.name.clone(), self.elab_payload(&t.payload, &inner))).collect(),
            },
            ItemKind::TypeAlias(a) => DefKind::Alias { ty: self.elab_ty(&a.ty, &inner) },
            ItemKind::Interface(x) => {
                let self_scope = TyScope { self_ty: Some(Ty::Param(self.fresh_sym("Self"))), ..inner.clone() };
                let mut methods = Vec::new();
                let mut assoc = Vec::new();
                for member in &x.members {
                    match member {
                        ast::InterfaceMember::Method(sig) => {
                            methods.push((sig.name.name.clone(), self.elaborate_sig(sig, &self_scope, None)))
                        }
                        ast::InterfaceMember::AssocType { name, .. } => assoc.push(name.name.clone()),
                    }
                }
                DefKind::Interface { methods, assoc }
            }
            ItemKind::Effect(e) => {
                let ops = e.ops.iter().map(|sig| (sig.name.name.clone(), self.elaborate_sig(sig, &inner, None))).collect();
                DefKind::Effect { ops }
            }
            _ => return,
        };
        self.defs[id].kind = kind;
    }

    fn elaborate_impl(&mut self, m: usize, item: usize, imp: &ast::ImplDecl) {
        let scope = TyScope { module: m, ..Default::default() };
        let params = self.type_params(&imp.params, &scope);
        let inner = scope.with_params(&params);
        let target = self.elab_ty(&imp.target, &inner);
        let interface = imp.interface.as_ref().and_then(|t| match &t.kind {
            TypeKind::Path { segments, args } if segments.len() == 1 => match self.lookup(m, &segments[0].name) {
                Some(Binding::Def(d)) if matches!(self.defs[d].kind, DefKind::Interface { .. }) => {
                    let args = self.elab_args(d, args, &inner, t.span);
                    Some((d, args))
                }
                _ => {
                    self.error(m, t.span, format!("`{}` is not an interface", segments[0].name));
                    None
                }
            },
            _ => None,
        });
        let id = self.impls.len();
        self.impls.push(Impl { module: m, params: params.clone(), target: target.clone(), interface, methods: Vec::new() });
        let method_scope = TyScope { self_ty: Some(target), ..inner };
        for (k, method) in imp.methods.iter().enumerate() {
            let scheme = self.elaborate_sig(&method.decl.sig, &method_scope, Some(&params));
            let fid = self.fns.len();
            let exported = method.exported || self.modules[m].is_std || imp.interface.is_some();
            let scheme = if exported && scheme.effects.is_none() { Scheme { effects: Some(EffRow::pure()), ..scheme } } else { scheme };
            self.fns.push(FnInfo {
                name: method.decl.sig.name.name.clone(),
                module: m,
                scheme,
                decl: DeclRef { module: m, item, method: Some(k) },
                exported,
                impl_id: Some(id),
                has_body: method.decl.body.is_some(),
            });
            self.impls[id].methods.push(fid);
        }
    }

    /// A function signature. `outer` are the enclosing impl's parameters, which become the
    /// leading generic parameters of the scheme.
    pub fn elaborate_sig(&mut self, sig: &ast::FnSig, scope: &TyScope, outer: Option<&[GParam]>) -> Scheme {
        let own = self.type_params(&sig.type_params, scope);
        let mut inner = scope.with_params(&own);
        // Region elision: exactly one region parameter across the impl and the function.
        let mut all: Vec<GParam> = outer.map(|o| o.to_vec()).unwrap_or_default();
        all.extend(own.iter().cloned());
        let regions: Vec<&GParam> = all.iter().filter(|p| p.kind == PKind::Region).collect();
        if regions.len() == 1 {
            inner.elided_region = Some(Region::Param(regions[0].sym.clone()));
        }
        let params = sig
            .params
            .iter()
            .map(|p| {
                let ty = p.ty.as_ref().map_or(Ty::Error, |t| self.elab_ty(t, &inner));
                (p.name.name.clone(), ty)
            })
            .collect();
        let ret = self.elab_ty(&sig.ret.ty, &inner);
        let effects = sig.uses.as_ref().map(|row| self.elab_effects(row, &inner));
        Scheme { tparams: all, params, ret, effects }
    }

    // ---- elaboration of types ----

    pub fn lookup(&self, module: usize, name: &str) -> Option<Binding> {
        self.modules[module].scope.get(name).copied()
    }

    pub fn elab_payload(&mut self, p: &ast::TagPayload, scope: &TyScope) -> Ty {
        match p {
            ast::TagPayload::None => Ty::void(),
            ast::TagPayload::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| self.elab_ty(t, scope)).collect()),
            ast::TagPayload::Record(fs) => {
                Ty::Record(Row::closed(fs.iter().map(|f| (f.name.name.clone(), self.elab_ty(&f.ty, scope))).collect()))
            }
        }
    }

    pub fn elab_ty(&mut self, t: &ast::Type, scope: &TyScope) -> Ty {
        let m = scope.module;
        match &t.kind {
            TypeKind::Path { segments, args } if segments.len() == 2 => {
                let base = ast::Type {
                    kind: TypeKind::Path { segments: vec![segments[0].clone()], args: Vec::new() },
                    span: segments[0].span,
                };
                let base = self.elab_ty(&base, scope);
                if !args.is_empty() {
                    self.error(m, t.span, "an associated type takes no arguments");
                }
                Ty::Assoc(Box::new(base), segments[1].name.clone())
            }
            TypeKind::Path { segments, args } => {
                let name = &segments[0].name;
                if let Some(p) = Prim::from_name(name) {
                    return Ty::Prim(p);
                }
                if name == "Self" {
                    return scope.self_ty.clone().unwrap_or_else(|| {
                        self.error(m, t.span, "`Self` is only meaningful in an `impl` or `interface`");
                        Ty::Error
                    });
                }
                if let Some((sym, kind)) = scope.params.get(name) {
                    if *kind != PKind::Type {
                        self.error(m, t.span, format!("`{name}` is not a type"));
                        return Ty::Error;
                    }
                    return Ty::Param(sym.clone());
                }
                match self.lookup(m, name) {
                    Some(Binding::Def(d)) => {
                        let gargs = self.elab_args(d, args, scope, t.span);
                        match &self.defs[d].kind {
                            DefKind::Alias { ty } => {
                                let ty = ty.clone();
                                let params = self.defs[d].params.clone();
                                subst_params(&ty, &params, &gargs)
                            }
                            DefKind::Struct { .. } | DefKind::Enum { .. } => Ty::Named(d, gargs),
                            DefKind::Interface { .. } | DefKind::Effect { .. } => {
                                // Effects and interfaces are namespaces in expressions, not types.
                                Ty::Named(d, gargs)
                            }
                        }
                    }
                    Some(Binding::Fn(_)) => {
                        self.error(m, t.span, format!("`{name}` is a function, not a type"));
                        Ty::Error
                    }
                    None => {
                        self.error(m, t.span, format!("unknown type `{name}`"));
                        Ty::Error
                    }
                }
            }
            TypeKind::Call { path, .. } => {
                self.error(m, t.span, format!("`comptime` type functions such as `{}` are not supported yet", path[0].name));
                Ty::Error
            }
            TypeKind::Record { fields, rest } => {
                let labels = fields.iter().map(|f| (f.name.name.clone(), self.elab_ty(&f.ty, scope))).collect();
                let tail = rest.as_ref().map_or(Tail::Closed, |r| self.row_tail(r, scope));
                Ty::Record(Row { labels, tail })
            }
            TypeKind::Union { tags, rest } => {
                let labels = tags.iter().map(|tg| (tg.name.name.clone(), self.elab_payload(&tg.payload, scope))).collect();
                let tail = rest.as_ref().map_or(Tail::Closed, |r| self.row_tail(r, scope));
                Ty::Union(Row { labels, tail })
            }
            TypeKind::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| self.elab_ty(t, scope)).collect()),
            TypeKind::EmptyRow => {
                self.error(m, t.span, "`[]` is an empty effect row, not a type");
                Ty::Error
            }
            TypeKind::Fn { mode, params, ret, uses } => {
                let mode = match mode {
                    ast::FnMode::Shared => FnMode::Shared,
                    ast::FnMode::Mut => FnMode::Mut,
                    ast::FnMode::Once => FnMode::Once,
                };
                let params = params.iter().map(|p| p.ty.as_ref().map_or(Ty::Error, |t| self.elab_ty(t, scope))).collect();
                let ret = self.elab_ty(&ret.ty, scope);
                let effects = uses.as_ref().map_or_else(EffRow::pure, |u| self.elab_effects(u, scope));
                Ty::Fn(Box::new(FnTy { mode, params, ret, effects }))
            }
            TypeKind::Array { elem, len } => {
                let elem = Box::new(self.elab_ty(elem, scope));
                match len {
                    None => Ty::Slice(elem),
                    Some(e) => Ty::Array(elem, self.elab_len(e, scope)),
                }
            }
            TypeKind::Mut(inner) => Ty::Borrow(true, Box::new(self.elab_ty(inner, scope))),
            TypeKind::Readonly(inner) => Ty::Borrow(false, Box::new(self.elab_ty(inner, scope))),
            TypeKind::Ptr(_) | TypeKind::Dyn(_) => {
                self.error(m, t.span, "raw pointers and `dyn` are not supported yet");
                Ty::Error
            }
            TypeKind::Expr(_) => {
                self.error(m, t.span, "expected a type");
                Ty::Error
            }
        }
    }

    fn elab_len(&mut self, e: &ast::Expr, scope: &TyScope) -> Len {
        match &e.kind {
            ast::ExprKind::Int(s) => Len::Known(s.parse().unwrap_or(0)),
            ast::ExprKind::Ident(n) => match scope.params.get(n) {
                Some((sym, PKind::Len)) => Len::Param(sym.clone()),
                _ => {
                    self.error(scope.module, e.span, format!("`{n}` is not a `comptime` length"));
                    Len::Known(0)
                }
            },
            _ => {
                self.error(scope.module, e.span, "array lengths must be literals or `comptime` parameters for now");
                Len::Known(0)
            }
        }
    }

    fn row_tail(&mut self, name: &ast::Ident, scope: &TyScope) -> Tail {
        match scope.params.get(&name.name) {
            Some((sym, PKind::Row)) => Tail::Param(sym.clone()),
            _ => {
                self.error(scope.module, name.span, format!("`{}` is not a row parameter", name.name));
                Tail::Closed
            }
        }
    }

    pub fn elab_region(&mut self, t: &ast::Type, scope: &TyScope) -> Region {
        if let TypeKind::Path { segments, args } = &t.kind
            && segments.len() == 1 && args.is_empty() {
                let name = &segments[0].name;
                if name == "Heap" {
                    return Region::Heap;
                }
                if let Some((sym, PKind::Region)) = scope.params.get(name) {
                    return Region::Param(sym.clone());
                }
            }
        self.error(scope.module, t.span, "expected a region");
        Region::Heap
    }

    /// A row given as a generic argument: `[]`, `[Io, Fail<E>]`, or a row parameter `E`.
    fn elab_row_type(&mut self, t: &ast::Type, scope: &TyScope) -> EffRow {
        match &t.kind {
            TypeKind::EmptyRow => EffRow::pure(),
            TypeKind::Tuple(items) => {
                let row: Vec<ast::RowItem> = items.iter().map(|i| ast::RowItem::Effect(i.clone())).collect();
                self.elab_effects(&row, scope)
            }
            TypeKind::Path { segments, args } if segments.len() == 1 && args.is_empty() => {
                match scope.params.get(&segments[0].name) {
                    Some((sym, PKind::Row)) => EffRow { effs: Vec::new(), tail: Tail::Param(sym.clone()) },
                    _ => {
                        let row = vec![ast::RowItem::Effect(t.clone())];
                        self.elab_effects(&row, scope)
                    }
                }
            }
            _ => {
                self.error(scope.module, t.span, "expected a row");
                EffRow::pure()
            }
        }
    }

    pub fn elab_effects(&mut self, row: &[ast::RowItem], scope: &TyScope) -> EffRow {
        let mut effs = Vec::new();
        let mut tail = Tail::Closed;
        for item in row {
            match item {
                ast::RowItem::Spread(name) => tail = self.row_tail(name, scope),
                ast::RowItem::Effect(t) => {
                    let TypeKind::Path { segments, args } = &t.kind else { continue };
                    let name = &segments[0].name;
                    match self.lookup(scope.module, name) {
                        Some(Binding::Def(d)) if matches!(self.defs[d].kind, DefKind::Effect { .. }) => {
                            let gargs = self.elab_args(d, args, scope, t.span);
                            let mut regions = Vec::new();
                            let mut targs = Vec::new();
                            for a in gargs {
                                match a {
                                    GArg::Region(r) => regions.push(r),
                                    GArg::Ty(t) => targs.push(t),
                                    _ => {}
                                }
                            }
                            effs.push(Eff { def: d, regions, args: targs });
                        }
                        _ => self.error(scope.module, t.span, format!("`{name}` is not an effect")),
                    }
                }
            }
        }
        EffRow { effs, tail }
    }

    /// Generic arguments for `def`, by parameter kind, with region elision and defaults.
    pub fn elab_args(&mut self, def: DefId, args: &[ast::Type], scope: &TyScope, span: Span) -> Vec<GArg> {
        let params = self.defs[def].params.clone();
        let regions = params.iter().filter(|p| p.kind == PKind::Region).count();
        let elide = args.len() < params.len() && regions > 0 && args.len() + regions <= params.len() && scope.elided_region.is_some();
        let mut given = args.iter();
        let mut out = Vec::new();
        for p in &params {
            if p.kind == PKind::Region && elide {
                out.push(GArg::Region(scope.elided_region.clone().expect("checked")));
                continue;
            }
            let arg = match given.next() {
                Some(a) => match p.kind {
                    PKind::Type => GArg::Ty(self.elab_ty(a, scope)),
                    PKind::Region => GArg::Region(self.elab_region(a, scope)),
                    PKind::Row => GArg::Row(self.elab_row_type(a, scope)),
                    PKind::Len => match &a.kind {
                        TypeKind::Expr(e) => GArg::Len(self.elab_len(e, scope)),
                        TypeKind::Path { segments, .. } => {
                            let e = ast::Expr { kind: ast::ExprKind::Ident(segments[0].name.clone()), span: a.span };
                            GArg::Len(self.elab_len(&e, scope))
                        }
                        _ => GArg::Len(Len::Known(0)),
                    },
                },
                None => match &p.default {
                    Some(d) => d.clone(),
                    None => {
                        // Missing arguments are inferred where the type is used in a body; in a
                        // signature they are an error.
                        if scope.params.is_empty() && !args.is_empty() || !args.is_empty() {
                            self.error(scope.module, span, format!("`{}` takes {} arguments", self.defs[def].name, params.len()));
                        }
                        match p.kind {
                            PKind::Type => GArg::Ty(Ty::Error),
                            PKind::Region => GArg::Region(Region::Heap),
                            PKind::Row => GArg::Row(EffRow::pure()),
                            PKind::Len => GArg::Len(Len::Known(0)),
                        }
                    }
                },
            };
            out.push(arg);
        }
        if given.next().is_some() {
            self.error(scope.module, span, format!("`{}` takes {} arguments", self.defs[def].name, params.len()));
        }
        out
    }
}

/// Substitutes generic parameters by arguments.
pub fn subst_params(t: &Ty, params: &[GParam], args: &[GArg]) -> Ty {
    let map: HashMap<&Sym, &GArg> = params.iter().map(|p| &p.sym).zip(args).collect();
    subst(t, &map)
}

pub fn subst(t: &Ty, map: &HashMap<&Sym, &GArg>) -> Ty {
    match t {
        Ty::Param(s) => match map.get(s) {
            Some(GArg::Ty(t)) => t.clone(),
            _ => t.clone(),
        },
        Ty::Named(d, args) => Ty::Named(*d, args.iter().map(|a| subst_arg(a, map)).collect()),
        Ty::Record(r) => Ty::Record(subst_row(r, map)),
        Ty::Union(r) => Ty::Union(subst_row(r, map)),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(|t| subst(t, map)).collect()),
        Ty::Array(t, l) => Ty::Array(Box::new(subst(t, map)), subst_len(l, map)),
        Ty::Slice(t) => Ty::Slice(Box::new(subst(t, map))),
        Ty::Borrow(m, t) => Ty::Borrow(*m, Box::new(subst(t, map))),
        Ty::Fn(f) => Ty::Fn(Box::new(FnTy {
            mode: f.mode,
            params: f.params.iter().map(|t| subst(t, map)).collect(),
            ret: subst(&f.ret, map),
            effects: subst_effs(&f.effects, map),
        })),
        Ty::Assoc(t, n) => Ty::Assoc(Box::new(subst(t, map)), n.clone()),
        _ => t.clone(),
    }
}

pub fn subst_arg(a: &GArg, map: &HashMap<&Sym, &GArg>) -> GArg {
    match a {
        GArg::Ty(t) => GArg::Ty(subst(t, map)),
        GArg::Region(r) => GArg::Region(subst_region(r, map)),
        GArg::Row(r) => GArg::Row(subst_effs(r, map)),
        GArg::Len(l) => GArg::Len(subst_len(l, map)),
    }
}

pub fn subst_region(r: &Region, map: &HashMap<&Sym, &GArg>) -> Region {
    match r {
        Region::Param(s) => match map.get(s) {
            Some(GArg::Region(r)) => r.clone(),
            _ => r.clone(),
        },
        _ => r.clone(),
    }
}

fn subst_len(l: &Len, map: &HashMap<&Sym, &GArg>) -> Len {
    match l {
        Len::Param(s) => match map.get(s) {
            Some(GArg::Len(l)) => l.clone(),
            _ => l.clone(),
        },
        _ => l.clone(),
    }
}

fn subst_row(r: &Row, map: &HashMap<&Sym, &GArg>) -> Row {
    Row { labels: r.labels.iter().map(|(k, t)| (k.clone(), subst(t, map))).collect(), tail: r.tail.clone() }
}

pub fn subst_effs(r: &EffRow, map: &HashMap<&Sym, &GArg>) -> EffRow {
    let mut effs: Vec<Eff> = r
        .effs
        .iter()
        .map(|e| Eff {
            def: e.def,
            regions: e.regions.iter().map(|x| subst_region(x, map)).collect(),
            args: e.args.iter().map(|t| subst(t, map)).collect(),
        })
        .collect();
    let mut tail = r.tail.clone();
    if let Tail::Param(s) = &r.tail
        && let Some(GArg::Row(row)) = map.get(s) {
            effs.extend(row.effs.iter().cloned());
            tail = row.tail.clone();
        }
    EffRow { effs, tail }
}
