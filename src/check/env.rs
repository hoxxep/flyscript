//! The program: loaded modules, their declarations, and elaboration of syntax into types.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

use super::types::*;
use crate::diag::{Diagnostic, FastMap, Span, SpanMap, SpanSet};
use crate::syntax::ast::{self, ItemKind, TypeKind};
use crate::syntax::{parse_declarations, parse_module};

/// The standard library, compiled into the checker: declaration files, and modules written in
/// Flyscript. Either may leave out a function's body, which the runtime then provides.
const STD: &[(&str, &str)] = &[
    ("std/prelude.fly", include_str!("../../std/prelude.fly")),
    ("std/region.d.fly", include_str!("../../std/region.d.fly")),
    ("std/net.d.fly", include_str!("../../std/net.d.fly")),
    ("std/io.d.fly", include_str!("../../std/io.d.fly")),
    ("std/collections.d.fly", include_str!("../../std/collections.d.fly")),
    ("std/par.fly", include_str!("../../std/par.fly")),
    ("std/layout.fly", include_str!("../../std/layout.fly")),
    ("std/sync.d.fly", include_str!("../../std/sync.d.fly")),
    ("std/json.fly", include_str!("../../std/json.fly")),
    ("std/world.d.fly", include_str!("../../std/world.d.fly")),
    ("std/fs.fly", include_str!("../../std/fs.fly")),
    ("std/process.fly", include_str!("../../std/process.fly")),
    ("std/time.fly", include_str!("../../std/time.fly")),
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
    Const(usize),
}

/// A module-level constant (§8.1).
#[derive(Debug)]
pub struct ConstInfo {
    pub name: String,
    pub module: usize,
    pub ty: Ty,
    pub value: ast::Expr,
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
    /// `comptime T: Type`: a template parameter, whose functions are specialized for each type
    /// they are used at (§7.1).
    pub comptime: bool,
}

#[derive(Clone, Debug)]
pub struct Scheme {
    pub tparams: Vec<GParam>,
    pub params: Vec<(String, Ty)>,
    pub ret: Ty,
    /// `None`: not declared, to be inferred from the body (non-exported functions only).
    pub effects: Option<EffRow>,
    /// The parameters a returned borrow may come from (`from a, b`); empty if not written.
    pub ret_from: Vec<String>,
}

#[derive(Debug)]
pub enum DefKind {
    Struct { fields: Option<Vec<(String, Ty)>> },
    Enum { tags: BTreeMap<String, Ty> },
    Alias { ty: Ty },
    /// `self_sym` is the parameter standing for `Self` in the methods' schemes.
    Interface { methods: Vec<(String, Scheme)>, assoc: Vec<String>, self_sym: Sym, extends: Vec<Ty> },
    Effect { ops: Vec<(String, Scheme)> },
}

#[derive(Debug)]
pub struct Def {
    pub name: String,
    pub module: usize,
    pub params: Vec<GParam>,
    pub kind: DefKind,
    pub span: Span,
    /// Fields visible only in the declaring module.
    pub private: Vec<String>,
    /// Declared `view` (§3.3).
    pub view: bool,
    /// An enum's tags in declaration order, which derivations follow (`Ord`, §3.5).
    pub tag_order: Vec<String>,
    /// A template struct's fields as written, computed per instance (§7.1).
    pub template_fields: Option<Vec<ast::Field>>,
    /// `@layout(c)`: laid out as C lays it out, so C may take it (§8.2); and the alignment asked.
    pub c_layout: bool,
    pub align: Option<u64>,
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
    /// `extern "C"`: a function of C's, or one C calls (§8.2).
    pub foreign: bool,
    /// For an interface's method called through a bound (`x.encode()` with `T extends Json`):
    /// the interface. Its first generic parameter is `Self`, resolved to an impl when called.
    pub iface: Option<DefId>,
}

#[derive(Debug)]
pub struct Impl {
    /// `impl I for T;`: `T` asks for `I`'s derivation, the template impl of `I` (§7.3).
    pub derived: bool,
    /// Associated types as written, and elaborated (for an impl that is not a template).
    pub assoc: Vec<(String, ast::Type)>,
    pub assoc_tys: HashMap<String, Ty>,
    pub module: usize,
    pub params: Vec<GParam>,
    pub target: Ty,
    pub interface: Option<(DefId, Vec<GArg>)>,
    pub methods: Vec<FnId>,
    /// The `impl` item, in its module.
    pub item: usize,
}

pub struct Program {
    pub modules: Vec<Module>,
    pub defs: Vec<Def>,
    pub consts: Vec<ConstInfo>,
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
    /// Per checked function: final types of its expressions and bindings, for later passes.
    pub typed: FastMap<FnId, Typed>,
    /// Each interface method, as a function called through a bound.
    pub iface_fns: HashMap<(DefId, String), FnId>,
    /// Types computed by `comptime` code, referred to from expanded syntax (`TypeKind::Spliced`).
    pub spliced: Vec<Ty>,
    /// Bodies after `comptime` expansion, for templates' specializations and for functions that
    /// use `comptime` code.
    pub bodies: HashMap<FnId, ast::FnDecl>,
    /// The source position each position in expanded code came from.
    pub synth: HashMap<usize, Span>,
    pub next_synth: usize,
    /// Specializations of templates, by template and `comptime` arguments.
    pub specs: HashMap<(FnId, String), FnId>,
    /// Template impls' associated types, by impl, arguments and name.
    pub assoc_instances: HashMap<(usize, String, String), Ty>,
    /// Template structs' fields, by struct and arguments.
    pub instances: HashMap<(DefId, String), Vec<(String, Ty)>>,
    /// For a specialization: its template, and how diagnostics name it ("in `describe` for
    /// `Point`").
    pub spec_of: HashMap<FnId, FnId>,
    pub spec_notes: HashMap<FnId, String>,
    /// For a derivation's specialization: the type that asked for it, whose private fields it
    /// may use (§7.3).
    pub spec_requested: HashMap<FnId, DefId>,
    /// Functions called while their effects were being inferred, so assumed pure there.
    pub assumed_pure: HashMap<FnId, (usize, Span)>,
    /// Type aliases not yet elaborated, so one may use another written after it, and those being
    /// elaborated, so one that refers to itself is caught.
    pending_aliases: HashMap<DefId, (usize, ast::Item)>,
    aliasing: Vec<DefId>,
    /// While a specialization is checked: which one, for its diagnostics.
    pub note: Option<String>,
}

/// The type checker's results for one function body, keyed by source span.
#[derive(Clone, Debug, Default)]
pub struct Typed {
    pub exprs: SpanMap<Ty>,
    /// Types of `Bind` patterns (by the pattern's span), including parameters' bindings.
    pub bindings: SpanMap<Ty>,
    pub params: Vec<(String, Ty)>,
    /// `==`, `!=` and `${e}` that call an interface's method (`Eq.eq`, `Show.show`), by the
    /// operator's or the interpolated expression's span, with `Self`'s type (§3.5).
    pub ops: SpanMap<(FnId, Vec<GArg>)>,
    /// Likewise for `${e}`, by the interpolated expression's span (which an operator inside it
    /// may share).
    pub shows: SpanMap<(FnId, Vec<GArg>)>,
    /// Moves out of bindings, by the moving expression's span, with the field path moved: the
    /// evaluator's drop flags (§5.6).
    pub moves: SpanMap<Vec<String>>,
    /// The bindings each closure moves in, by the closure's span: they leave their scope's
    /// ownership when it is made.
    pub captured_moves: SpanMap<Vec<(String, Ty)>>,
    /// The effects each call, operation, `yield` or `throw` may perform, by its span; `None` in
    /// the list stands for effects a row variable leaves open.
    pub performs: SpanMap<Vec<Option<DefId>>>,
    /// The effect each `handle` expression handles, by its span.
    pub handled: SpanMap<DefId>,
    /// `match` scrutinees that are places nothing may be moved out of — behind a borrow, or an
    /// element of a collection — matched through a borrow (`true` if `mut`), by their span.
    pub lent_scrutinees: SpanMap<bool>,
    /// Match arms on an owned place that borrow it `mut`, changing what they bind in place.
    pub lent_arms: SpanSet,
    /// Tag constructions `#A(x)` whose one argument is the whole of a larger payload (§3.2).
    pub whole: SpanSet,
    /// The type each part of a tag, record or list literal was checked against, by the part's
    /// span: a part put where a borrow is wanted is lent, not moved.
    pub slots: SpanMap<Ty>,
    /// The function each call or method call resolved to, by the call's span.
    pub calls: SpanMap<FnId>,
    /// Each call's generic arguments, in its scheme's parameter order (for dispatch through
    /// bounds at run time).
    pub targs: SpanMap<Vec<GArg>>,
    /// The parameters of each effect operation performed, as instantiated there: an argument
    /// given where a borrow is declared is lent to the arm, not moved (§5.3).
    pub op_params: SpanMap<Vec<Ty>>,
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
            consts: Vec::new(),
            fns: Vec::new(),
            impls: Vec::new(),
            diags: Vec::new(),
            next_sym: 0,
            known: HashMap::new(),
            inferred: HashMap::new(),
            checked: Default::default(),
            typed: FastMap::default(),
            iface_fns: HashMap::new(),
            spliced: Vec::new(),
            bodies: HashMap::new(),
            synth: HashMap::new(),
            next_synth: super::comptime::SYNTH_BASE,
            specs: HashMap::new(),
            spec_of: HashMap::new(),
            spec_notes: HashMap::new(),
            instances: HashMap::new(),
            assoc_instances: HashMap::new(),
            spec_requested: HashMap::new(),
            note: None,
            assumed_pure: HashMap::new(),
            pending_aliases: HashMap::new(),
            aliasing: Vec::new(),
        };
        for (file, source) in STD {
            let name = file.trim_end_matches(".fly").trim_end_matches(".d");
            p.add_module(name.to_string(), format!("<{file}>"), source.to_string(), true, true);
        }
        let mut queue: Vec<PathBuf> = entries.iter().map(|e| normalize(e)).collect();
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
            let idx = p.add_module(name, path.display().to_string(), source, false, false);
            for item in &p.modules[idx].ast.items {
                if let ItemKind::Import { from, .. } = &item.kind {
                    if is_relative(from) {
                        queue.push(normalize(&path.parent().unwrap_or(Path::new(".")).join(format!("{from}.fly"))));
                    } else if !from.starts_with("std/") {
                        queue.push(normalize(&package_root().join(format!("{from}.fly"))));
                    }
                }
            }
        }
        p.declare();
        p
    }

    fn add_module(&mut self, name: String, file: String, source: String, is_std: bool, declarations: bool) -> usize {
        let parsed = if declarations { parse_declarations(&source) } else { parse_module(&source) };
        let idx = self.modules.len();
        let ast = parsed.unwrap_or_else(|d| {
            self.diags.push((idx, d));
            ast::Module { items: Vec::new() }
        });
        self.modules.push(Module { name, file, source, ast, is_std, scope: HashMap::new(), exports: HashMap::new() });
        idx
    }

    pub fn error(&mut self, module: usize, span: Span, msg: impl Into<String>) {
        let span = self.source_span(span);
        let mut msg = msg.into();
        if let Some(n) = &self.note {
            msg = format!("{msg} ({n})");
        }
        let d = (module, Diagnostic::new(span, msg));
        // Repeated copies of generated code report a problem once.
        if !self.diags.contains(&d) {
            self.diags.push(d);
        }
    }

    /// The source position of a position, which may be in expanded code.
    pub fn source_span(&self, span: Span) -> Span {
        if span.start < super::comptime::SYNTH_BASE {
            return span;
        }
        self.synth.get(&span.start).copied().unwrap_or_default()
    }

    /// A struct's fields with its arguments substituted: for a template, those of the instance,
    /// once it has been computed (`ensure_instance`).
    /// A template struct's instance whose `comptime` code failed, already reported.
    pub fn failed_instance(&self, d: DefId, args: &[GArg]) -> bool {
        self.defs[d].template_fields.is_some() && args.iter().all(concrete_arg) && !self.instances.contains_key(&(d, format!("{args:?}")))
    }

    pub fn struct_fields(&self, d: DefId, args: &[GArg]) -> Option<Vec<(String, Ty)>> {
        let def = &self.defs[d];
        if def.template_fields.is_some() {
            return self.instances.get(&(d, format!("{args:?}"))).cloned();
        }
        match &def.kind {
            DefKind::Struct { fields: Some(fs) } => Some(fs.iter().map(|(k, t)| (k.clone(), subst_params(t, &def.params, args))).collect()),
            _ => None,
        }
    }

    /// Computes a template struct's fields for these arguments, if they are known (§7.1).
    pub fn ensure_instance(&mut self, d: DefId, args: &[GArg]) {
        let Some(fields) = self.defs[d].template_fields.clone() else { return };
        let key = (d, format!("{args:?}"));
        if self.instances.contains_key(&key) || args.iter().any(|a| !concrete_arg(a)) {
            return;
        }
        // Registered first, so a field of the same instance's type does not recurse forever.
        self.instances.insert(key.clone(), Vec::new());
        let params = self.defs[d].params.clone();
        let module = self.defs[d].module;
        let mut env = Vec::new();
        for (g, a) in params.iter().zip(args) {
            match (g.comptime, a) {
                (true, GArg::Ty(t)) => env.push((g.sym.name.clone(), super::comptime::CV::Type(t.clone()))),
                (_, GArg::Len(Len::Known(n))) => env.push((g.sym.name.clone(), super::comptime::CV::Int(*n as i128))),
                _ => {}
            }
        }
        let Some(expanded) = super::comptime::Expand::new(self, module, None, env).struct_fields(&fields) else {
            // Its `comptime` code failed and said why; the instance has no fields to report on.
            self.instances.remove(&key);
            return;
        };
        let scope = TyScope { module, ..Default::default() }.with_params(&params);
        let fs: Vec<(String, Ty)> = expanded
            .iter()
            .map(|f| {
                let t = self.elab_ty(&f.ty, &scope);
                (f.name.name.clone(), subst_params(&t, &params, args))
            })
            .collect();
        // Each instance is checked as the struct it is: unless declared `view`, it holds no
        // borrow (§3.3).
        if !self.defs[d].view
            && let Some((name, t)) = fs.iter().find(|(_, t)| self.class(t) == 2) {
                let shown = format!("{}", Show(&Ty::Named(d, args.to_vec()), self));
                let ft = format!("{}", Show(t, self));
                let span = self.defs[d].span;
                self.error(module, span, format!("`{shown}` holds a borrow in `{name}` (`{ft}`): declare it `view struct` if it is a temporary view"));
            }
        self.instances.insert(key, fs);
    }

    /// A function's declaration: its expanded body if it has one.
    pub fn fn_decl(&self, fid: FnId) -> Option<ast::FnDecl> {
        if let Some(d) = self.bodies.get(&fid) {
            return Some(d.clone());
        }
        let decl = self.fns[fid].decl;
        let item = self.modules.get(decl.module)?.ast.items.get(decl.item)?;
        match (&item.kind, decl.method) {
            (ast::ItemKind::Function(f), None) => Some(f.clone()),
            (ast::ItemKind::Impl(imp), Some(k)) => Some(imp.methods[k].decl.clone()),
            _ => None,
        }
    }

    pub fn fresh_sym(&mut self, name: &str) -> Sym {
        self.next_sym += 1;
        Sym { id: self.next_sym, name: name.to_string() }
    }

    /// `name`, with where to import it from if a standard module exports it.
    pub fn unknown(&self, what: &str, name: &str) -> String {
        let home = self.modules.iter().find(|m| m.is_std && m.name != "std/prelude" && m.exports.contains_key(name));
        match home {
            Some(m) => format!("unknown {what} `{name}`: import it with `import {{ {name} }} from \"{}\";`", m.name),
            None => match ts_hint(what, name) {
                Some(hint) => format!("unknown {what} `{name}`: {hint}"),
                None => format!("unknown {what} `{name}`"),
            },
        }
    }

    pub fn module_named(&self, name: &str) -> Option<usize> {
        self.modules.iter().position(|m| m.name == name)
    }

    // ---- declaration ----

    fn declare(&mut self) {
        // Pass 1: names.
        for m in 0..self.modules.len() {
            let items = self.modules[m].ast.items.clone();
            for (i, item) in items.iter().enumerate() {
                let (name, binding) = match &item.kind {
                    ItemKind::Struct(s) => (s.name.name.clone(), Binding::Def(self.placeholder(&s.name, m))),
                    ItemKind::Enum(e) => (e.name.name.clone(), Binding::Def(self.placeholder(&e.name, m))),
                    ItemKind::TypeAlias(a) => (a.name.name.clone(), Binding::Def(self.placeholder(&a.name, m))),
                    ItemKind::Interface(x) => {
                        let id = self.placeholder(&x.name, m);
                        // Kinds are known before elaboration, so declarations may refer to
                        // themselves (`effect Io { start(task: () => void uses Io) … }`).
                        let self_sym = self.fresh_sym("Self");
                        self.defs[id].kind = DefKind::Interface { methods: Vec::new(), assoc: Vec::new(), self_sym, extends: Vec::new() };
                        (x.name.name.clone(), Binding::Def(id))
                    }
                    ItemKind::Effect(e) => {
                        let id = self.placeholder(&e.name, m);
                        self.defs[id].kind = DefKind::Effect { ops: Vec::new() };
                        (e.name.name.clone(), Binding::Def(id))
                    }
                    ItemKind::Const { name, value, .. } => {
                        self.consts.push(ConstInfo { name: name.name.clone(), module: m, ty: Ty::Error, value: value.clone() });
                        (name.name.clone(), Binding::Const(self.consts.len() - 1))
                    }
                    ItemKind::Function(f) => {
                        let id = self.fns.len();
                        self.fns.push(FnInfo {
                            name: f.sig.name.name.clone(),
                            module: m,
                            scheme: Scheme { tparams: Vec::new(), params: Vec::new(), ret: Ty::Error, effects: None, ret_from: Vec::new() },
                            decl: DeclRef { module: m, item: i, method: None },
                            exported: item.exported,
                            impl_id: None,
                            has_body: f.body.is_some(),
                            foreign: f.sig.foreign,
                            iface: None,
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
        }
        for name in ["Fail", "Yield", "Region", "Io", "String", "Ref", "Vec", "Iterable", "LentBy", "Copy", "Send", "Eq", "Show", "Ord", "Cont", "Box", "Arc", "Ptr", "Unsafe"] {
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
            let items = self.modules[m].ast.items.clone();
            for item in &items {
                let ItemKind::Import { names, from } = &item.kind else { continue };
                let target = if is_relative(from) {
                    let dir = Path::new(&self.modules[m].name).parent().unwrap_or(Path::new("")).to_path_buf();
                    self.module_named(&normalize(&dir.join(from)).to_string_lossy())
                } else if from.starts_with("std/") {
                    self.module_named(from)
                } else {
                    // A package's module is known by its file, however it was reached.
                    self.module_named(&normalize(&package_root().join(from)).to_string_lossy())
                };
                let Some(target) = target else {
                    self.error(m, item.span, format!("no module `{from}`"));
                    continue;
                };
                for (n, local) in names {
                    match self.modules[target].exports.get(&n.name).copied() {
                        Some(b) => {
                            self.modules[m].scope.insert(local.name.clone(), b);
                        }
                        None => {
                            let name = &n.name;
                            let in_prelude = self.module_named("std/prelude").is_some_and(|p| self.modules[p].exports.contains_key(name));
                            let home = self.modules.iter().find(|x| x.is_std && x.name != "std/prelude" && x.exports.contains_key(name)).map(|x| x.name.clone());
                            let hint = match (in_prelude, home) {
                                (true, _) => format!(": `{name}` is in the prelude, so it needs no import"),
                                (false, Some(h)) => format!(": it is in `{h}`"),
                                _ => String::new(),
                            };
                            self.error(m, n.span, format!("module `{from}` does not export `{name}`{hint}"))
                        }
                    }
                }
            }
        }
        // Pass 3: elaborate declarations, then impls, then function signatures. Aliases come
        // first, so a declaration may use one written after it (`interface Ord` returning
        // `Ordering`).
        for m in 0..self.modules.len() {
            let items = self.modules[m].ast.items.clone();
            for item in &items {
                self.elaborate_params(m, item);
            }
        }
        for m in 0..self.modules.len() {
            for item in &self.modules[m].ast.items {
                if let ItemKind::TypeAlias(a) = &item.kind
                    && let Some(Binding::Def(id)) = self.modules[m].scope.get(&a.name.name).copied()
                {
                    self.pending_aliases.insert(id, (m, item.clone()));
                }
            }
        }
        for aliases in [true, false] {
            for m in 0..self.modules.len() {
                let items = self.modules[m].ast.items.clone();
                for item in items.iter().filter(|i| matches!(i.kind, ItemKind::TypeAlias(_)) == aliases) {
                    self.elaborate_def(m, item);
                }
            }
        }
        self.check_views();
        self.elaborate_consts();
        for m in 0..self.modules.len() {
            let items = self.modules[m].ast.items.clone();
            for (i, item) in items.iter().enumerate() {
                match &item.kind {
                    ItemKind::Impl(imp) => self.elaborate_impl(m, i, imp),
                    ItemKind::Function(f) => {
                        let scope = TyScope { module: m, ..Default::default() };
                        let mut scheme = self.elaborate_sig(&f.sig, &scope, None);
                        let Some(Binding::Fn(id)) = self.modules[m].scope.get(&f.sig.name.name).copied() else { continue };
                        if f.sig.foreign {
                            scheme = self.foreign_scheme(m, f, scheme);
                        }
                        // A template is checked only per specialization, so it states its effects (§7.1).
                        if (item.exported || scheme.tparams.iter().any(|g| g.comptime)) && scheme.effects.is_none() {
                            self.fns[id].scheme = Scheme { effects: Some(EffRow::pure()), ..scheme };
                        } else {
                            self.fns[id].scheme = scheme;
                        }
                    }
                    _ => {}
                }
            }
        }
        self.check_impls();
    }

    /// An impl of an interface has exactly the interface's methods, each taking what the
    /// interface's takes, giving what it gives, and performing nothing it does not declare: code
    /// that calls it through the interface knows only the interface's (§3.4).
    fn check_impls(&mut self) {
        for i in 0..self.impls.len() {
            let Some((iface, iargs)) = self.impls[i].interface.clone() else { continue };
            if self.impls[i].derived || self.impls[i].params.iter().any(|g| g.comptime) {
                continue;
            }
            let DefKind::Interface { methods, self_sym, .. } = &self.defs[iface].kind else { continue };
            let (methods, self_sym) = (methods.clone(), self_sym.clone());
            let (m, item, target, fids, nouter) =
                (self.impls[i].module, self.impls[i].item, self.impls[i].target.clone(), self.impls[i].methods.clone(), self.impls[i].params.len());
            let iname = self.defs[iface].name.clone();
            let shown_target = format!("{}", Show(&target, self));
            let impl_span = self.modules[m].ast.items[item].span;
            for (name, want) in &methods {
                let Some(&fid) = fids.iter().find(|&&f| self.fns[f].name == *name) else {
                    let span = Span { start: impl_span.start, end: impl_span.start };
                    self.error(m, span, format!("`{shown_target}` does not implement `{iname}`: it has no `{name}`"));
                    continue;
                };
                let have = self.fns[fid].scheme.clone();
                let span = self.fn_decl(fid).map_or(impl_span, |d| d.sig.name.span);
                // The interface's method as this impl has it: `Self` the target, the interface's
                // parameters its arguments, and its own type parameters the impl method's.
                let own: Vec<GParam> = have.tparams[nouter.min(have.tparams.len())..].to_vec();
                if own.len() != want.tparams.len() || have.params.len() != want.params.len() {
                    self.error(m, span, format!("`{name}` does not match `{iname}`'s: it takes other parameters"));
                    continue;
                }
                let mut params: Vec<GParam> = vec![GParam { sym: self_sym.clone(), kind: PKind::Type, bounds: Vec::new(), default: None, comptime: false }];
                params.extend(self.defs[iface].params.iter().cloned());
                params.extend(want.tparams.iter().cloned());
                let mut args: Vec<GArg> = vec![GArg::Ty(target.clone())];
                args.extend(iargs.iter().cloned());
                args.extend(own.iter().map(super::impls::param_arg));
                let map: SubstMap<'_> = params.iter().map(|p| p.sym.id).zip(args.iter()).collect();
                let same = |a: &Ty, b: &Ty| super::impls::erase_regions(a) == super::impls::erase_regions(b);
                let assoc = self.impls[i].assoc_tys.clone();
                let mine = |t: &Ty| own_assoc(&subst(t, &map), &target, &assoc);
                let want_params: Vec<Ty> = want.params.iter().map(|(_, t)| mine(t)).collect();
                let want_ret = mine(&want.ret);
                let fits = have.params.iter().zip(&want_params).all(|((_, a), b)| same(a, b)) && same(&have.ret, &want_ret);
                if !fits {
                    let shown: Vec<String> = want_params.iter().map(|t| format!("{}", Show(t, self))).collect();
                    let ret = format!("{}", Show(&want_ret, self));
                    self.error(m, span, format!("`{name}` does not match `{iname}`'s, which takes `({})` and gives `{ret}`", shown.join(", ")));
                    continue;
                }
                let want_row = subst_effs(&want.effects.clone().unwrap_or_else(EffRow::pure), &map);
                let have_row = have.effects.clone().unwrap_or_else(EffRow::pure);
                if let Some(e) = self.beyond(&have_row, &want_row) {
                    let what = format!("{}", Show(&Ty::Named(e.def, Vec::new()), self));
                    self.error(m, span, format!("`{name}` performs `{what}`, which `{iname}`'s `{name}` does not declare: code calling it through `{iname}` would not handle it"));
                }
            }
            for &fid in &fids {
                let name = self.fns[fid].name.clone();
                if !methods.iter().any(|(n, _)| *n == name) {
                    let span = self.fn_decl(fid).map_or(impl_span, |d| d.sig.name.span);
                    self.error(m, span, format!("`{name}` is not a method of `{iname}`"));
                }
            }
        }
    }

    /// An effect `have` performs that `want` does not allow, if there is one: one of another
    /// effect, or a failure with a tag `want`'s failures lack. A row left open allows anything.
    fn beyond(&self, have: &EffRow, want: &EffRow) -> Option<Eff> {
        if want.tail != Tail::Closed {
            return None;
        }
        let fail = self.known.get("Fail").copied();
        for e in &have.effs {
            let Some(w) = want.effs.iter().find(|w| w.def == e.def) else { return Some(e.clone()) };
            if Some(e.def) == fail
                && let (Some(Ty::Union(he)), Some(Ty::Union(we))) = (e.args.first(), w.args.first())
                && we.tail == Tail::Closed
                && he.labels.keys().any(|k| !we.labels.contains_key(k))
            {
                return Some(e.clone());
            }
        }
        None
    }

    fn placeholder(&mut self, name: &ast::Ident, module: usize) -> DefId {
        self.defs.push(Def {
            name: name.name.clone(),
            module,
            params: Vec::new(),
            kind: DefKind::Struct { fields: None },
            span: name.span,
            private: Vec::new(),
            view: false,
            tag_order: Vec::new(),
            template_fields: None,
            c_layout: false,
            align: None,
        });
        self.defs.len() - 1
    }

    pub fn type_params(&mut self, params: &[ast::TypeParam], scope: &TyScope) -> Vec<GParam> {
        let mut out = Vec::new();
        for p in params {
            let (name, kind, comptime) = match p {
                ast::TypeParam::Region { name, .. } => (name, PKind::Region, false),
                ast::TypeParam::Row { name, .. } => (name, PKind::Row, false),
                ast::TypeParam::Comptime { name, ty } => match &ty.kind {
                    TypeKind::Path { segments, .. } if segments.len() == 1 && segments[0].name == "Type" => (name, PKind::Type, true),
                    _ => (name, PKind::Len, false),
                },
                ast::TypeParam::Type { name, .. } => (name, PKind::Type, false),
            };
            let sym = self.fresh_sym(&name.name);
            out.push(GParam { sym, kind, bounds: Vec::new(), default: None, comptime });
        }
        // Bounds and defaults may mention earlier parameters.
        let inner = scope.with_params(&out);
        for (gp, p) in out.iter_mut().zip(params) {
            match p {
                ast::TypeParam::Type { bounds, default, .. } => {
                    gp.bounds = bounds.iter().map(|b| self.elab_ty(b, &inner)).collect();
                    gp.default = default.as_ref().map(|d| GArg::Ty(self.elab_ty(d, &inner)));
                }
                ast::TypeParam::Row { default, bounds, .. } => {
                    gp.bounds = bounds.iter().map(|b| self.elab_ty(b, &inner)).collect();
                    if let Some(d) = default {
                        gp.default = Some(GArg::Row(self.elab_row_type(d, &inner)));
                    }
                }
                ast::TypeParam::Region { default: Some(d), .. } => gp.default = Some(GArg::Region(self.elab_region(d, &inner))),
                _ => {}
            }
        }
        out
    }

    /// A declaration's generic parameters, before any declaration's body: an alias may be
    /// elaborated before the generic type it applies.
    fn elaborate_params(&mut self, m: usize, item: &ast::Item) {
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
        self.defs[id].params = self.type_params(params, &scope);
    }

    fn elaborate_def(&mut self, m: usize, item: &ast::Item) {
        let scope = TyScope { module: m, ..Default::default() };
        let name = match &item.kind {
            ItemKind::Struct(s) => &s.name,
            ItemKind::Enum(e) => &e.name,
            ItemKind::TypeAlias(a) => &a.name,
            ItemKind::Interface(x) => &x.name,
            ItemKind::Effect(e) => &e.name,
            _ => return,
        };
        let Some(Binding::Def(id)) = self.modules[m].scope.get(&name.name).copied() else { return };
        let gparams = self.defs[id].params.clone();
        let inner = scope.with_params(&gparams);
        match &item.kind {
            ItemKind::Struct(s) => {
                self.defs[id].view = s.view;
                if let Some(l) = &s.layout {
                    if l.name != "c" && l.name != "packed" {
                        self.error(m, l.span, "`@layout` takes `c` or `packed`");
                    }
                    self.defs[id].c_layout = l.name == "c";
                }
                if let Some(a) = s.align {
                    if !a.is_power_of_two() {
                        self.error(m, name.span, "an alignment is a power of two");
                    }
                    self.defs[id].align = Some(a);
                }
                self.defs[id].private =
                    s.fields.iter().flatten().filter(|f| f.private).map(|f| f.name.name.clone()).collect();
                // A struct with a type parameter that is `comptime`, or `comptime` code among its
                // fields, is a template: its fields are computed for each instance.
                let generated = s.fields.iter().flatten().any(|f| f.generate.is_some() || f.computed.is_some());
                if generated || gparams.iter().any(|g| g.comptime) {
                    self.defs[id].template_fields = s.fields.clone();
                    self.defs[id].kind = DefKind::Struct { fields: Some(Vec::new()) };
                    return;
                }
            }
            ItemKind::Enum(e) => {
                self.defs[id].view = e.view;
                self.defs[id].tag_order = e.tags.iter().map(|t| t.name.name.clone()).collect();
            }
            _ => {}
        }
        let kind = match &item.kind {
            ItemKind::Struct(s) => DefKind::Struct {
                fields: s.fields.as_ref().map(|fs| fs.iter().map(|f| (f.name.name.clone(), self.elab_ty(&f.ty, &inner))).collect()),
            },
            ItemKind::Enum(e) => DefKind::Enum {
                tags: e.tags.iter().map(|t| (t.name.name.clone(), self.elab_payload(&t.payload, &inner))).collect(),
            },
            ItemKind::TypeAlias(a) => {
                if self.pending_aliases.remove(&id).is_none() {
                    return;
                }
                self.aliasing.push(id);
                let ty = self.elab_ty(&a.ty, &inner);
                self.aliasing.pop();
                DefKind::Alias { ty }
            }
            ItemKind::Interface(x) => {
                let DefKind::Interface { self_sym, .. } = &self.defs[id].kind else { return };
                let self_sym = self_sym.clone();
                let extends = x.extends.iter().map(|t| self.elab_ty(t, &inner)).collect();
                let self_scope = TyScope { self_ty: Some(Ty::Param(self_sym.clone())), ..inner.clone() };
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
                self.declare_iface_fns(id, m, &methods, &self_sym);
                DefKind::Interface { methods, assoc, self_sym, extends }
            }
            ItemKind::Effect(e) => {
                let ops = e.ops.iter().map(|sig| (sig.name.name.clone(), self.elaborate_sig(sig, &inner, None))).collect();
                DefKind::Effect { ops }
            }
            _ => return,
        };
        self.defs[id].kind = kind;
    }

    /// A nominal type that holds a borrow must be declared `view` (§3.3).
    fn check_views(&mut self) {
        for d in 0..self.defs.len() {
            let def = &self.defs[d];
            if self.modules[def.module].is_std {
                continue;
            }
            let parts: Vec<(String, Ty)> = match &def.kind {
                DefKind::Struct { fields: Some(fs) } => fs.clone(),
                DefKind::Enum { tags } => tags.iter().map(|(k, t)| (format!("#{k}"), t.clone())).collect(),
                _ => continue,
            };
            for (_, ty) in &parts {
                if let Some((c, arg)) = self.borrow_in_container(ty) {
                    let (module, span) = (self.defs[d].module, self.defs[d].span);
                    let msg = super::expr::container_message(self, c, &arg);
                    self.error(module, span, msg);
                }
            }
            if self.defs[d].view {
                continue;
            }
            for (name, ty) in parts {
                if self.class(&ty) == 2 {
                    let shown = format!("{}", Show(&ty, self));
                    let hint = if shown.contains("str") && !shown.contains("u8") {
                        "use an owned `String`"
                    } else {
                        "use an owned type such as `Vec<T>`"
                    };
                    let (module, span, tname) = (self.defs[d].module, self.defs[d].span, self.defs[d].name.clone());
                    self.error(
                        module,
                        span,
                        format!("`{tname}` holds a borrow in `{name}` (`{shown}`): {hint}, or declare `view` if `{tname}` is a temporary view"),
                    );
                    break;
                }
            }
        }
    }

    /// Module-level constants: their declared type, or a literal's.
    fn elaborate_consts(&mut self) {
        for c in 0..self.consts.len() {
            let m = self.consts[c].module;
            let items = self.modules[m].ast.items.clone();
            let ann = items.iter().find_map(|it| match &it.kind {
                ItemKind::Const { name, ty, .. } if name.name == self.consts[c].name => Some(ty.clone()),
                _ => None,
            });
            let scope = TyScope { module: m, ..Default::default() };
            let ty = match ann.flatten() {
                Some(t) => self.elab_ty(&t, &scope),
                None => match &self.consts[c].value.kind {
                    ast::ExprKind::Int(_) => Ty::Prim(Prim::I32),
                    ast::ExprKind::Float(_) => Ty::Prim(Prim::F64),
                    ast::ExprKind::Str(_) => Ty::Prim(Prim::Str),
                    ast::ExprKind::Bool(_) => Ty::bool(),
                    ast::ExprKind::Byte(_) => Ty::Prim(Prim::U8),
                    _ => {
                        let span = self.consts[c].value.span;
                        self.error(m, span, "give this constant a type: `const NAME: Type = …;`");
                        Ty::Error
                    }
                },
            };
            self.consts[c].ty = ty;
        }
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
                found => {
                    let name = &segments[0].name;
                    let msg = if found.is_none() { self.unknown("interface", name) } else { format!("`{name}` is not an interface") };
                    self.error(m, t.span, msg);
                    None
                }
            },
            _ => None,
        });
        let id = self.impls.len();
        let template = params.iter().any(|g| g.comptime);
        let assoc_tys = if template { HashMap::new() } else { imp.assoc.iter().map(|(n, t)| (n.name.clone(), self.elab_ty(t, &inner))).collect() };
        let assoc = imp.assoc.iter().map(|(n, t)| (n.name.clone(), t.clone())).collect();
        self.impls.push(Impl { derived: imp.derived, assoc, assoc_tys, module: m, params: params.clone(), target: target.clone(), interface, methods: Vec::new(), item });
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
                foreign: false,
                iface: None,
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
        Scheme { tparams: all, params, ret, effects, ret_from: sig.ret.from.iter().map(|i| i.name.clone()).collect() }
    }

    /// The scheme of an `extern "C"` function (§8.2): what it takes and gives must be what C has;
    /// one of C's performs `Unsafe` besides what it declares, and one C calls performs nothing.
    fn foreign_scheme(&mut self, m: usize, f: &ast::FnDecl, mut scheme: Scheme) -> Scheme {
        let mut tys: Vec<(Ty, Span)> = scheme.params.iter().zip(&f.sig.params).map(|((_, t), p)| (t.clone(), p.ty.as_ref().map_or(p.name.span, |x| x.span))).collect();
        tys.push((scheme.ret.clone(), f.sig.ret.ty.span));
        for (t, span) in tys {
            if !self.c_representable(&t) {
                let shown = format!("{}", Show(&t, self));
                self.error(m, span, format!("an `extern \"C\"` function takes and gives only what C has — integers, floats, `bool`, pointers and `@layout(c)` structs of them — not `{shown}`"));
            }
        }
        if !scheme.tparams.is_empty() {
            self.error(m, f.sig.name.span, "an `extern \"C\"` function is not generic");
        }
        let unsafe_eff = self.known.get("Unsafe").map(|&d| Eff { def: d, regions: Vec::new(), args: Vec::new() });
        if f.body.is_none() {
            let mut row = scheme.effects.clone().unwrap_or_else(EffRow::pure);
            if let Some(u) = unsafe_eff {
                row.effs.push(u);
            }
            scheme.effects = Some(row);
        } else {
            if scheme.effects.as_ref().is_some_and(|r| !r.effs.is_empty() || r.tail != Tail::Closed) {
                self.error(m, f.sig.name.span, "a function C calls performs nothing: C cannot handle an effect, nor a failure");
            }
            scheme.effects = Some(EffRow::pure());
        }
        scheme
    }

    /// Whether C has values of the type: a number, a `bool`, a pointer, `void`, or a struct laid
    /// out as C lays it out, of those.
    pub fn c_representable(&self, t: &Ty) -> bool {
        match t {
            Ty::Prim(p) => !matches!(p, Prim::Str | Prim::Never | Prim::Type | Prim::I128),
            Ty::Named(d, args) => {
                if self.known.get("Ptr") == Some(d) {
                    return true;
                }
                self.defs[*d].c_layout && self.struct_fields(*d, args).is_some_and(|fs| fs.iter().all(|(_, x)| self.c_representable(x)))
            }
            _ => false,
        }
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
            TypeKind::Spliced(i) => self.spliced[*i].clone(),
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
                // `Type` is the one built-in name a module may declare for itself: a compiler
                // written in Flyscript has a `Type` of its own (§1, goal 6).
                if let Some(p) = Prim::from_name(name)
                    && (p != Prim::Type || !self.modules[m].scope.contains_key(name.as_str()))
                {
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
                let found = self.lookup(m, name);
                if let Some(Binding::Def(d)) = found {
                    if self.aliasing.contains(&d) {
                        let msg = format!("`{name}` refers to itself, but a type alias names a structural type, which cannot be recursive: declare it as an `enum` or a `struct` (§3.3)");
                        self.error(m, t.span, msg);
                        return Ty::Error;
                    }
                    if let Some((am, item)) = self.pending_aliases.get(&d).cloned() {
                        self.elaborate_def(am, &item);
                    }
                }
                match found {
                    Some(Binding::Def(d)) => {
                        let gargs = self.elab_args(d, args, scope, t.span);
                        match &self.defs[d].kind {
                            DefKind::Alias { ty } => {
                                let ty = ty.clone();
                                let params = self.defs[d].params.clone();
                                subst_params(&ty, &params, &gargs)
                            }
                            DefKind::Struct { .. } | DefKind::Enum { .. } => {
                                self.ensure_instance(d, &gargs);
                                Ty::Named(d, gargs)
                            }
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
                    Some(Binding::Const(_)) => {
                        self.error(m, t.span, format!("`{name}` is a constant, not a type"));
                        Ty::Error
                    }
                    None => {
                        let msg = self.unknown("type", name);
                        self.error(m, t.span, msg);
                        Ty::Error
                    }
                }
            }
            TypeKind::Record { fields, rest } => {
                let labels = fields.iter().map(|f| (f.name.name.clone(), self.elab_ty(&f.ty, scope))).collect();
                let tail = rest.as_ref().map_or(Tail::Closed, |r| self.row_tail(r, scope));
                Ty::Record(Row { labels, tail })
            }
            TypeKind::Union { tags, includes, rest } => {
                let mut labels: BTreeMap<String, Ty> = tags.iter().map(|tg| (tg.name.name.clone(), self.elab_payload(&tg.payload, scope))).collect();
                // A named union's tags are part of this one, as rows compose (§3.2).
                for inc in includes {
                    match self.elab_ty(inc, scope) {
                        Ty::Union(r) if r.tail == Tail::Closed => {
                            for (k, v) in r.labels {
                                if labels.get(&k).is_some_and(|w| *w != v) {
                                    self.error(m, inc.span, format!("`#{k}` is in this union twice, carrying different payloads"));
                                }
                                labels.insert(k, v);
                            }
                        }
                        Ty::Error => {}
                        _ => self.error(m, inc.span, "only a closed tag union can be part of a union: an enum is a type of its own"),
                    }
                }
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
            // `T*` is the library's `Ptr<T>` (§8.2).
            TypeKind::Ptr(inner) => {
                let elem = self.elab_ty(inner, scope);
                match self.known.get("Ptr") {
                    Some(&d) => Ty::Named(d, vec![GArg::Ty(elem)]),
                    None => Ty::Error,
                }
            }
            TypeKind::Dyn(_) => {
                self.error(m, t.span, "`dyn` is not supported yet");
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

/// Where packages are found: the installation, beside its `std` (§8.1).
fn package_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn is_relative(import: &str) -> bool {
    import.starts_with("./") || import.starts_with("../")
}

/// Lexically normalizes a path (`a/./b/../c` → `a/c`), so one file is one module however it is
/// reached.
fn normalize(p: &Path) -> PathBuf {
    use std::path::Component;
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            Component::CurDir => {}
            Component::ParentDir => {
                if !out.pop() {
                    out.push("..");
                }
            }
            other => out.push(other.as_os_str()),
        }
    }
    out
}

/// A type of an interface's method as an impl of it has it: the target's associated types its
/// own (`Self.Slice` the impl's `Slice`).
fn own_assoc(t: &Ty, target: &Ty, assoc: &HashMap<String, Ty>) -> Ty {
    let go = |t: &Ty| own_assoc(t, target, assoc);
    match t {
        Ty::Assoc(base, n) if **base == *target => assoc.get(n).cloned().unwrap_or_else(|| t.clone()),
        Ty::Named(d, args) => Ty::Named(*d, args.iter().map(|a| match a { GArg::Ty(x) => GArg::Ty(go(x)), a => a.clone() }).collect()),
        Ty::Tuple(ts) => Ty::Tuple(ts.iter().map(go).collect()),
        Ty::Array(x, l) => Ty::Array(Box::new(go(x)), l.clone()),
        Ty::Slice(x) => Ty::Slice(Box::new(go(x))),
        Ty::Borrow(m, x) => Ty::Borrow(*m, Box::new(go(x))),
        Ty::Record(r) => Ty::Record(Row { labels: r.labels.iter().map(|(k, x)| (k.clone(), go(x))).collect(), tail: r.tail.clone() }),
        Ty::Union(r) => Ty::Union(Row { labels: r.labels.iter().map(|(k, x)| (k.clone(), go(x))).collect(), tail: r.tail.clone() }),
        _ => t.clone(),
    }
}

/// Arguments for generic parameters, by the parameter's symbol id.
pub type SubstMap<'a> = HashMap<u32, &'a GArg>;

/// Substitutes generic parameters by arguments.
pub fn subst_params(t: &Ty, params: &[GParam], args: &[GArg]) -> Ty {
    let map: SubstMap<'_> = params.iter().map(|p| p.sym.id).zip(args).collect();
    subst(t, &map)
}

pub fn subst(t: &Ty, map: &SubstMap<'_>) -> Ty {
    match t {
        Ty::Param(s) => match map.get(&s.id) {
            Some(GArg::Ty(t)) => t.clone(),
            _ => t.clone(),
        },
        Ty::Named(d, args) => Ty::Named(*d, args.iter().map(|a| subst_arg(a, map)).collect()),
        Ty::Record(r) => Ty::Record(subst_row(r, map)),
        Ty::Union(r) => Ty::Union(subst_row(r, map)),
        Ty::Tuple(ts) => match ts.iter().map(|t| subst(t, map)).collect::<Vec<_>>() {
            // A payload of one `void` is no payload (§3.2).
            ts if ts.len() == 1 && ts[0] == Ty::void() => Ty::void(),
            ts => Ty::Tuple(ts),
        },
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

pub fn subst_arg(a: &GArg, map: &SubstMap<'_>) -> GArg {
    match a {
        GArg::Ty(t) => GArg::Ty(subst(t, map)),
        GArg::Region(r) => GArg::Region(subst_region(r, map)),
        GArg::Row(r) => GArg::Row(subst_effs(r, map)),
        GArg::Len(l) => GArg::Len(subst_len(l, map)),
    }
}

pub fn subst_region(r: &Region, map: &SubstMap<'_>) -> Region {
    match r {
        Region::Param(s) => match map.get(&s.id) {
            Some(GArg::Region(r)) => r.clone(),
            _ => r.clone(),
        },
        _ => r.clone(),
    }
}

fn subst_len(l: &Len, map: &SubstMap<'_>) -> Len {
    match l {
        Len::Param(s) => match map.get(&s.id) {
            Some(GArg::Len(l)) => l.clone(),
            _ => l.clone(),
        },
        _ => l.clone(),
    }
}

fn subst_row(r: &Row, map: &SubstMap<'_>) -> Row {
    Row { labels: r.labels.iter().map(|(k, t)| (k.clone(), subst(t, map))).collect(), tail: r.tail.clone() }
}

pub fn subst_effs(r: &EffRow, map: &SubstMap<'_>) -> EffRow {
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
        && let Some(GArg::Row(row)) = map.get(&s.id) {
            effs.extend(row.effs.iter().cloned());
            tail = row.tail.clone();
        }
    EffRow { effs, tail }
}

/// Whether a generic argument is known: no parameter or inference variable in it.
fn concrete_arg(a: &GArg) -> bool {
    match a {
        GArg::Ty(t) => !super::impls::contains_params(t),
        GArg::Len(l) => matches!(l, Len::Known(_)),
        _ => true,
    }
}

/// Every declaration as elaborated, one per line, for comparison with another implementation.
pub fn describe(p: &Program) -> Vec<String> {
    let ty = |t: &Ty| format!("{}", Show(t, p));
    let params = |gs: &[GParam]| {
        gs.iter()
            .map(|g| {
                let bounds: Vec<String> = g.bounds.iter().map(ty).collect();
                format!("{}{}:{:?}[{}]", if g.comptime { "comptime " } else { "" }, g.sym.name, g.kind, bounds.join(" & "))
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    let scheme = |s: &Scheme| {
        let ps: Vec<String> = s.params.iter().map(|(n, t)| format!("{n}: {}", ty(t))).collect();
        let effs = match &s.effects {
            Some(e) => format!("{}", Show(e, p)),
            None => "?".to_string(),
        };
        format!("<{}>({}): {} uses {} from {}", params(&s.tparams), ps.join(", "), ty(&s.ret), effs, s.ret_from.join(","))
    };
    let mut out = Vec::new();
    for (i, d) in p.defs.iter().enumerate() {
        let kind = match &d.kind {
            DefKind::Struct { fields } => match fields {
                Some(fs) => format!("struct {{ {} }}", fs.iter().map(|(k, t)| format!("{k}: {}", ty(t))).collect::<Vec<_>>().join("; ")),
                None => "struct opaque".to_string(),
            },
            DefKind::Enum { tags } => format!("enum {}", tags.iter().map(|(k, t)| format!("#{k} {}", ty(t))).collect::<Vec<_>>().join(" | ")),
            DefKind::Alias { ty: t } => format!("alias {}", ty(t)),
            DefKind::Interface { methods, assoc, extends, .. } => format!(
                "interface extends [{}] assoc [{}] {}",
                extends.iter().map(ty).collect::<Vec<_>>().join(", "),
                assoc.join(", "),
                methods.iter().map(|(n, s)| format!("{n}{}", scheme(s))).collect::<Vec<_>>().join("; ")
            ),
            DefKind::Effect { ops } => format!("effect {}", ops.iter().map(|(n, s)| format!("{n}{}", scheme(s))).collect::<Vec<_>>().join("; ")),
        };
        out.push(format!("def {i} {} <{}> {kind}", d.name, params(&d.params)));
    }
    for (i, c) in p.consts.iter().enumerate() {
        out.push(format!("const {i} {}: {}", c.name, ty(&c.ty)));
    }
    for (i, f) in p.fns.iter().enumerate() {
        out.push(format!("fn {i} {} {}{}", p.modules[f.module].name, f.name, scheme(&f.scheme)));
    }
    for (i, imp) in p.impls.iter().enumerate() {
        let iface = imp.interface.as_ref().map(|(d, args)| format!("{}<{}>", p.defs[*d].name, args.iter().map(|a| format!("{}", Show(a, p))).collect::<Vec<_>>().join(", ")));
        out.push(format!("impl {i} <{}> {} for {} methods {:?}", params(&imp.params), iface.unwrap_or_default(), ty(&imp.target), imp.methods));
    }
    for (m, d) in &p.diags {
        out.push(format!("error {m} {}..{}: {}", d.span.start, d.span.end, d.message));
    }
    out
}

/// What Flyscript has where a TypeScript programmer reaches for something it does not (§2.1).
fn ts_hint(what: &str, name: &str) -> Option<&'static str> {
    Some(match (what, name) {
        ("type", "string") => "Flyscript's strings are `str`, a borrowed view of text, and `String`, which owns its bytes",
        ("type", "number") => "Flyscript's numbers have sizes: `i32`, `i64`, `u32`, `usize`, `f64` and the rest",
        ("type", "boolean") => "Flyscript's is `bool`",
        ("type", "Array") => "a list that grows is a `Vec<T>`, and a fixed one `T[N]`",
        ("type", "Map") => "a map is a `HashMap`, from `std/collections`",
        ("type", "Set") => "a set is a `HashSet`, from `std/collections`",
        ("type", "Promise") => "there is no `async`: I/O is the `Io` effect, and tasks run in `Io.scope`",
        ("type", "any" | "unknown") => "every value has a type; a value of one of several types is a tag union, `#A(T) | #B(U)`",
        ("name", "console") => "print with `println`, from `std/io`",
        ("name", "null" | "undefined") => "there is no null: a value that may be missing is an `Option`, `#Some(x)` or `#None`",
        _ => return None,
    })
}
