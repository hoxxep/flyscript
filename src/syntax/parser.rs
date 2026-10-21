use super::ast::*;
use super::lexer::{Kw, TemplatePart, Tok, Token, lex, lex_range};
use crate::diag::{Diagnostic, Span};

type PResult<T> = Result<T, Diagnostic>;

pub fn parse_module(source: &str) -> PResult<Module> {
    parse(source, false)
}

/// Parses a declaration file (`.d.fly`): functions may end in `;` and structs may be opaque.
pub fn parse_declarations(source: &str) -> PResult<Module> {
    parse(source, true)
}

fn parse(source: &str, declarations: bool) -> PResult<Module> {
    let mut p = Parser::new(source, lex(source)?);
    p.declarations = declarations;
    let mut items = Vec::new();
    while !p.at_eof() {
        items.push(p.item()?);
    }
    Ok(Module { items })
}

pub fn parse_expr(source: &str) -> PResult<Expr> {
    let mut p = Parser::new(source, lex(source)?);
    let e = p.expr()?;
    p.expect_eof()?;
    Ok(e)
}

struct Parser<'a> {
    src: &'a str,
    toks: Vec<Token>,
    pos: usize,
    /// Parsing a `.d.fly` file.
    declarations: bool,
}

/// Binary operators by precedence, lowest first. `as` binds tighter than all of them.
const BINARY: &[&[&str]] = &[
    &["||"],
    &["&&"],
    &["==", "!=", "<", ">", "<=", ">="],
    &["|"],
    &["^"],
    &["&"],
    &["<<", ">>"],
    &["+", "-"],
    &["*", "/", "%"],
];

const ASSIGN: &[&str] = &["=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^="];

impl<'a> Parser<'a> {
    fn new(src: &'a str, toks: Vec<Token>) -> Parser<'a> {
        Parser { src, toks, pos: 0, declarations: false }
    }

    // ---- token helpers ----

    fn tok(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn tok_at(&self, n: usize) -> &Tok {
        let i = (self.pos + n).min(self.toks.len() - 1);
        &self.toks[i].tok
    }

    fn span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn prev_end(&self) -> usize {
        if self.pos == 0 { 0 } else { self.toks[self.pos - 1].span.end }
    }

    fn since(&self, start: Span) -> Span {
        Span::new(start.start, self.prev_end().max(start.start))
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn at_eof(&self) -> bool {
        matches!(self.tok(), Tok::Eof)
    }

    fn at(&self, p: &str) -> bool {
        matches!(self.tok(), Tok::Punct(q) if *q == p)
    }

    fn at_n(&self, n: usize, p: &str) -> bool {
        matches!(self.tok_at(n), Tok::Punct(q) if *q == p)
    }

    fn at_kw(&self, kw: Kw) -> bool {
        matches!(self.tok(), Tok::Kw(k) if *k == kw)
    }

    fn at_word(&self, w: &str) -> bool {
        matches!(self.tok(), Tok::Ident(s) if s == w)
    }

    fn word_at(&self, n: usize, w: &str) -> bool {
        matches!(self.tok_at(n), Tok::Ident(s) if s == w)
    }

    /// `match (e) {` at token `at`: the word begins a `match` only in that shape.
    fn match_at(&self, at: usize) -> bool {
        self.word_at(at - self.pos, "match")
            && matches!(self.tok_at(at - self.pos + 1), Tok::Punct("("))
            && self.close_from(at + 1).is_some_and(|c| matches!(self.toks[(c + 1).min(self.toks.len() - 1)].tok, Tok::Punct("{")))
    }

    /// `handle {` or `region (R) {`: the other contextual expression words.
    fn at_handle(&self) -> bool {
        self.at_word("handle") && self.at_n(1, "{")
    }

    fn at_region(&self) -> bool {
        self.at_word("region") && self.at_n(1, "(") && matches!(self.tok_at(2), Tok::Ident(_)) && self.at_n(3, ")") && self.at_n(4, "{")
    }

    fn eat(&mut self, p: &str) -> bool {
        if self.at(p) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: Kw) -> bool {
        if self.at_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_word(&mut self, w: &str) -> bool {
        if self.at_word(w) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn describe(&self) -> String {
        match self.tok() {
            Tok::Ident(s) => format!("`{s}`"),
            Tok::Kw(k) => format!("`{}`", k.as_str()),
            Tok::Int(s) | Tok::Float(s) => format!("`{s}`"),
            Tok::Byte(_) => "a byte literal".into(),
            Tok::Str(_) => "a string".into(),
            Tok::Template(_) => "a template literal".into(),
            Tok::Tag(s) => format!("`#{s}`"),
            Tok::Punct(p) => format!("`{p}`"),
            Tok::Eof => "end of file".into(),
        }
    }

    fn error<T>(&self, expected: &str) -> PResult<T> {
        Err(Diagnostic::new(self.span(), format!("expected {expected}, found {}", self.describe())))
    }

    fn expect(&mut self, p: &str) -> PResult<Span> {
        if self.at(p) { Ok(self.bump().span) } else { self.error(&format!("`{p}`")) }
    }

    fn expect_kw(&mut self, kw: Kw) -> PResult<Span> {
        if self.at_kw(kw) { Ok(self.bump().span) } else { self.error(&format!("`{}`", kw.as_str())) }
    }

    fn expect_word(&mut self, w: &str) -> PResult<()> {
        if self.eat_word(w) { Ok(()) } else { self.error(&format!("`{w}`")) }
    }

    fn expect_eof(&self) -> PResult<()> {
        if self.at_eof() { Ok(()) } else { self.error("end of input") }
    }

    fn ident(&mut self) -> PResult<Ident> {
        match self.tok().clone() {
            Tok::Ident(name) => {
                let span = self.bump().span;
                Ok(Ident { name, span })
            }
            _ => self.error("an identifier"),
        }
    }

    /// A member name: as in TypeScript, reserved words are allowed after `.`, as effect
    /// operation names and as record fields, so `Yield.yield` and `{ default: 1 }` work.
    fn member_name(&mut self) -> PResult<Ident> {
        match self.tok().clone() {
            Tok::Kw(kw) => {
                let span = self.bump().span;
                Ok(Ident { name: kw.as_str().to_string(), span })
            }
            _ => self.ident(),
        }
    }

    /// Two adjacent single-character tokens, e.g. `>` `>` read as a shift operator.
    fn adjacent(&self, a: &str, b: &str) -> bool {
        self.at(a) && self.at_n(1, b) && self.toks[self.pos].span.end == self.toks[self.pos + 1].span.start
    }

    /// Runs `f`, rewinding and returning `None` if it fails.
    fn attempt<T>(&mut self, f: impl FnOnce(&mut Self) -> PResult<T>) -> Option<T> {
        let saved = self.pos;
        match f(self) {
            Ok(v) => Some(v),
            Err(_) => {
                self.pos = saved;
                None
            }
        }
    }

    /// Index of the token closing the bracket at `self.pos`, if balanced.
    fn matching_close(&self) -> Option<usize> {
        self.close_from(self.pos)
    }

    /// The bracket that closes the one at token `from`.
    fn close_from(&self, from: usize) -> Option<usize> {
        let mut depth = 0usize;
        for (i, t) in self.toks.iter().enumerate().skip(from) {
            match &t.tok {
                Tok::Punct("(" | "[" | "{") => depth += 1,
                Tok::Punct(")" | "]" | "}") => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i);
                    }
                }
                Tok::Eof => return None,
                _ => {}
            }
        }
        None
    }

    // ---- items ----

    fn item(&mut self) -> PResult<Item> {
        let start = self.span();
        let exported = self.eat_kw(Kw::Export);
        let kind = match self.tok() {
            Tok::Kw(Kw::Import) if !exported => self.import()?,
            Tok::Punct("@") => {
                let layout = self.layout()?;
                let view = self.eat_word("view");
                ItemKind::Struct(self.struct_decl(Some(layout), view)?)
            }
            Tok::Ident(w) if w == "view" && matches!(self.tok_at(1), Tok::Kw(Kw::Struct | Kw::Enum)) => {
                self.bump();
                if self.at_kw(Kw::Struct) {
                    ItemKind::Struct(self.struct_decl(None, true)?)
                } else {
                    let mut e = self.enum_decl()?;
                    e.view = true;
                    ItemKind::Enum(e)
                }
            }
            Tok::Kw(Kw::Struct) => ItemKind::Struct(self.struct_decl(None, false)?),
            Tok::Kw(Kw::Enum) => ItemKind::Enum(self.enum_decl()?),
            Tok::Kw(Kw::Const) => {
                self.bump();
                let name = self.ident()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                self.expect("=")?;
                let value = self.expr()?;
                self.expect(";")?;
                ItemKind::Const { name, ty, value }
            }
            Tok::Kw(Kw::Interface) => ItemKind::Interface(self.interface_decl()?),
            Tok::Kw(Kw::Impl) => ItemKind::Impl(self.impl_decl()?),
            Tok::Kw(Kw::Type) => ItemKind::TypeAlias(self.type_alias()?),
            Tok::Ident(w) if w == "effect" && matches!(self.tok_at(1), Tok::Ident(_)) => ItemKind::Effect(self.effect_decl()?),
            Tok::Kw(Kw::Function | Kw::Comptime) => ItemKind::Function(self.fn_decl()?),
            Tok::Kw(Kw::Extern) => {
                self.bump();
                match self.tok() {
                    Tok::Str(abi) if abi == "C" => {
                        self.bump();
                    }
                    _ => return self.error("`\"C\"`"),
                }
                let sig = self.sig(true)?;
                self.expect(";")?;
                ItemKind::Extern(sig)
            }
            _ => return self.error("a declaration"),
        };
        Ok(Item { exported, kind, span: self.since(start) })
    }

    fn import(&mut self) -> PResult<ItemKind> {
        self.expect_kw(Kw::Import)?;
        self.expect("{")?;
        let mut names = Vec::new();
        while !self.at("}") {
            let name = self.ident()?;
            let local = if self.eat_kw(Kw::As) { self.ident()? } else { name.clone() };
            names.push((name, local));
            if !self.eat(",") {
                break;
            }
        }
        self.expect("}")?;
        self.expect_word("from")?;
        let from = match self.tok().clone() {
            Tok::Str(s) => {
                self.bump();
                s
            }
            _ => return self.error("a module path string"),
        };
        self.expect(";")?;
        Ok(ItemKind::Import { names, from })
    }

    fn layout(&mut self) -> PResult<Ident> {
        self.expect("@")?;
        self.expect_word("layout")?;
        self.expect("(")?;
        let kind = self.ident()?;
        self.expect(")")?;
        Ok(kind)
    }

    fn struct_decl(&mut self, layout: Option<Ident>, view: bool) -> PResult<StructDecl> {
        self.expect_kw(Kw::Struct)?;
        let name = self.ident()?;
        let params = self.type_params()?;
        let fields = if self.declarations && self.eat(";") { None } else { Some(self.field_list()?) };
        Ok(StructDecl { layout, view, name, params, fields })
    }

    /// `{ name: Type; … }` with `;` or `,` separators.
    fn field_list(&mut self) -> PResult<Vec<Field>> {
        self.expect("{")?;
        let fields = self.field_items()?;
        self.expect("}")?;
        Ok(fields)
    }

    /// Fields up to a closing `}`: `name: T`, `private name: T`, `[e]: T`, or generated ones.
    fn field_items(&mut self) -> PResult<Vec<Field>> {
        let mut fields = Vec::new();
        while !self.at("}") && !self.at("...") {
            if self.at_kw(Kw::Comptime) && !matches!(self.tok_at(1), Tok::Kw(Kw::For | Kw::If)) && !self.word_at(1, "match") {
                let start = self.span();
                self.bump();
                let e = self.expr()?;
                self.expect(";")?;
                let mut f = Field::new(Ident { name: String::new(), span: self.since(start) }, Type { kind: TypeKind::EmptyRow, span: start }, false);
                f.generate = Some(Box::new(Generate::Do(e)));
                fields.push(f);
                continue;
            }
            if self.at_kw(Kw::Comptime) {
                let start = self.span();
                let g = self.generate(Self::field_items)?;
                let mut f = Field::new(Ident { name: String::new(), span: self.since(start) }, Type { kind: TypeKind::EmptyRow, span: start }, false);
                f.generate = Some(Box::new(g));
                fields.push(f);
                if !self.eat(";") {
                    self.eat(",");
                }
                continue;
            }
            let private = self.at_word("private") && matches!(self.tok_at(1), Tok::Ident(_));
            if private {
                self.bump();
            }
            let (name, computed) = self.entry_name()?;
            self.expect(":")?;
            let ty = self.ty()?;
            fields.push(Field { name, ty, private, computed, generate: None });
            if !self.eat(";") && !self.eat(",") {
                break;
            }
        }
        Ok(fields)
    }

    /// A field's name, or `[e]` for one computed by `comptime` code.
    fn entry_name(&mut self) -> PResult<(Ident, Option<Box<Expr>>)> {
        if self.at("[") {
            let start = self.span();
            self.bump();
            let e = self.expr()?;
            self.expect("]")?;
            return Ok((Ident { name: String::new(), span: self.since(start) }, Some(Box::new(e))));
        }
        Ok((self.member_name()?, None))
    }

    /// `comptime for (const p of e) { … }` or `comptime if (c) { … } else { … }` in a sequence,
    /// the items between the braces parsed by `items`.
    fn generate<T>(&mut self, items: fn(&mut Self) -> PResult<Vec<T>>) -> PResult<Generate<T>> {
        self.expect_kw(Kw::Comptime)?;
        let group = |p: &mut Self| -> PResult<Vec<T>> {
            p.expect("{")?;
            let v = items(p)?;
            p.expect("}")?;
            Ok(v)
        };
        if self.eat_kw(Kw::For) {
            self.expect("(")?;
            if !self.eat_kw(Kw::Const) && !self.eat_kw(Kw::Let) {
                return self.error("`const`");
            }
            let pat = self.pattern_one()?;
            self.expect_word("of")?;
            let iter = self.expr()?;
            self.expect(")")?;
            Ok(Generate::For { pat, iter, body: group(self)? })
        } else if self.eat_kw(Kw::If) {
            let cond = self.paren_expr()?;
            let then = group(self)?;
            let otherwise = if self.eat_kw(Kw::Else) { group(self)? } else { Vec::new() };
            Ok(Generate::If { cond, then, otherwise })
        } else if self.eat_word("match") {
            let scrutinee = self.paren_expr()?;
            self.expect("{")?;
            let mut arms = Vec::new();
            while !self.at("}") {
                let pat = self.pattern()?;
                self.expect("=>")?;
                arms.push((pat, group(self)?));
                self.eat(",");
            }
            self.expect("}")?;
            Ok(Generate::Match { scrutinee, arms })
        } else {
            self.error("`for`, `if` or `match` after `comptime`")
        }
    }

    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        self.expect_kw(Kw::Enum)?;
        let name = self.ident()?;
        let params = self.type_params()?;
        self.expect("{")?;
        let mut tags = Vec::new();
        while !self.at("}") {
            tags.push(self.tag_decl()?);
            if !self.eat(",") {
                break;
            }
        }
        self.expect("}")?;
        Ok(EnumDecl { view: false, name, params, tags })
    }

    fn tag_decl(&mut self) -> PResult<TagDecl> {
        let name = match self.tok().clone() {
            Tok::Tag(name) => Ident { name, span: self.bump().span },
            _ => return self.error("a tag such as `#Some`"),
        };
        let payload = if self.at("(") {
            self.bump();
            let mut tys = Vec::new();
            while !self.at(")") {
                tys.push(self.ty()?);
                if !self.eat(",") {
                    break;
                }
            }
            self.expect(")")?;
            TagPayload::Tuple(tys)
        } else if self.at("{") {
            TagPayload::Record(self.field_list()?)
        } else {
            TagPayload::None
        };
        Ok(TagDecl { name, payload })
    }

    fn interface_decl(&mut self) -> PResult<InterfaceDecl> {
        self.expect_kw(Kw::Interface)?;
        let name = self.ident()?;
        let params = self.type_params()?;
        let extends = if self.eat_kw(Kw::Extends) { self.bounds()? } else { Vec::new() };
        self.expect("{")?;
        let mut members = Vec::new();
        while !self.at("}") {
            if self.eat_kw(Kw::Type) {
                let name = self.ident()?;
                let bounds = if self.eat_kw(Kw::Extends) { self.bounds()? } else { Vec::new() };
                members.push(InterfaceMember::AssocType { name, bounds });
            } else {
                members.push(InterfaceMember::Method(self.member_sig()?));
            }
            self.expect(";")?;
        }
        self.expect("}")?;
        Ok(InterfaceDecl { name, params, extends, members })
    }

    fn impl_decl(&mut self) -> PResult<ImplDecl> {
        self.expect_kw(Kw::Impl)?;
        let params = self.type_params()?;
        let first = self.ty()?;
        let (interface, target) = if self.eat_kw(Kw::For) { (Some(first), self.ty()?) } else { (None, first) };
        if interface.is_some() && self.eat(";") {
            return Ok(ImplDecl { params, interface, target, methods: Vec::new(), assoc: Vec::new(), derived: true });
        }
        self.expect("{")?;
        let mut methods = Vec::new();
        let mut assoc = Vec::new();
        while !self.at("}") {
            if self.eat_kw(Kw::Type) {
                let name = self.ident()?;
                self.expect("=")?;
                assoc.push((name, self.ty()?));
                self.expect(";")?;
                continue;
            }
            let exported = self.eat_kw(Kw::Export);
            let sig = self.member_sig()?;
            let body = if self.declarations && self.eat(";") { None } else { Some(self.block()?) };
            methods.push(Method { exported, decl: FnDecl { sig, body } });
        }
        self.expect("}")?;
        Ok(ImplDecl { params, interface, target, methods, assoc, derived: false })
    }

    fn type_alias(&mut self) -> PResult<TypeAlias> {
        self.expect_kw(Kw::Type)?;
        let name = self.ident()?;
        let params = self.type_params()?;
        self.expect("=")?;
        let ty = self.ty()?;
        self.expect(";")?;
        Ok(TypeAlias { name, params, ty })
    }

    fn effect_decl(&mut self) -> PResult<EffectDecl> {
        self.expect_word("effect")?;
        let name = self.ident()?;
        let params = self.type_params()?;
        self.expect("{")?;
        let mut ops = Vec::new();
        while !self.at("}") {
            // Operations are written without `function`; tolerate it for symmetry with interfaces.
            let with_kw = self.at_kw(Kw::Function);
            ops.push(self.sig(with_kw)?);
            self.expect(";")?;
        }
        self.expect("}")?;
        Ok(EffectDecl { name, params, ops })
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        let sig = self.sig(true)?;
        let body = if self.declarations && self.eat(";") { None } else { Some(self.block()?) };
        Ok(FnDecl { sig, body })
    }

    /// A method's signature: its name may be any word, reserved ones included (§2.3).
    fn member_sig(&mut self) -> PResult<FnSig> {
        self.sig_named(true, true)
    }

    fn sig(&mut self, function_kw: bool) -> PResult<FnSig> {
        self.sig_named(function_kw, !function_kw)
    }

    fn sig_named(&mut self, function_kw: bool, member: bool) -> PResult<FnSig> {
        let start = self.span();
        let comptime = self.eat_kw(Kw::Comptime);
        if function_kw {
            self.expect_kw(Kw::Function)?;
        }
        let name = if member { self.member_name()? } else { self.ident()? };
        let type_params = self.type_params()?;
        let params = self.params(true)?;
        self.expect(":")?;
        let ret = self.ret()?;
        let uses = self.uses()?;
        Ok(FnSig { comptime, name, type_params, params, ret, uses, span: self.since(start) })
    }

    fn params(&mut self, typed: bool) -> PResult<Vec<Param>> {
        self.expect("(")?;
        let mut params = Vec::new();
        while !self.at(")") {
            let comptime = self.eat_kw(Kw::Comptime);
            let name = self.ident()?;
            let ty = if self.eat(":") {
                Some(self.ty()?)
            } else if typed {
                return self.error("`:` and a parameter type");
            } else {
                None
            };
            params.push(Param { comptime, name, ty });
            if !self.eat(",") {
                break;
            }
        }
        self.expect(")")?;
        Ok(params)
    }

    /// A lambda's parameters, which, as in TypeScript, may take their argument apart:
    /// `([k, v]) => …` and `({ name }) => …` take a parameter and bind its parts with `const`.
    fn lambda_params(&mut self) -> PResult<(Vec<Param>, Vec<Stmt>)> {
        self.expect("(")?;
        let mut params = Vec::new();
        let mut unpack = Vec::new();
        while !self.at(")") {
            if self.at("[") || self.at("{") {
                let pat = self.pattern()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                let at = Span { start: pat.span.end, end: pat.span.end };
                let name = Ident { name: format!("${}", params.len()), span: pat.span };
                unpack.push(Stmt::Let {
                    mutable: false,
                    span: pat.span,
                    pat,
                    ty: None,
                    init: Expr { kind: ExprKind::Ident(name.name.clone()), span: at },
                });
                params.push(Param { comptime: false, name, ty });
            } else {
                let comptime = self.eat_kw(Kw::Comptime);
                let name = self.ident()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                params.push(Param { comptime, name, ty });
            }
            if !self.eat(",") {
                break;
            }
        }
        self.expect(")")?;
        Ok((params, unpack))
    }

    fn ret(&mut self) -> PResult<Return> {
        let ty = self.ty()?;
        let mut from = Vec::new();
        if self.eat_word("from") {
            from.push(self.ident()?);
            // More sources, unless the comma starts the next parameter (`, name:`).
            while self.at(",") && matches!(self.tok_at(1), Tok::Ident(_)) && !matches!(self.tok_at(2), Tok::Punct(":")) {
                self.bump();
                from.push(self.ident()?);
            }
        }
        Ok(Return { ty, from })
    }

    fn uses(&mut self) -> PResult<Option<Vec<RowItem>>> {
        if !self.eat_kw(Kw::Uses) {
            return Ok(None);
        }
        let mut row = vec![self.row_item()?];
        // A comma continues the row unless it starts the next parameter (`, name:`).
        while self.at(",") && self.row_continues() {
            self.bump();
            row.push(self.row_item()?);
        }
        Ok(Some(row))
    }

    fn row_continues(&self) -> bool {
        match self.tok_at(1) {
            Tok::Punct("...") => true,
            Tok::Ident(_) => !matches!(self.tok_at(2), Tok::Punct(":")),
            _ => false,
        }
    }

    fn row_item(&mut self) -> PResult<RowItem> {
        if self.eat("...") {
            Ok(RowItem::Spread(self.ident()?))
        } else {
            let start = self.span();
            let segments = self.path()?;
            let args = self.type_args()?;
            Ok(RowItem::Effect(Type { kind: TypeKind::Path { segments, args }, span: self.since(start) }))
        }
    }

    fn type_params(&mut self) -> PResult<Vec<TypeParam>> {
        if !self.eat("<") {
            return Ok(Vec::new());
        }
        let mut params = Vec::new();
        while !self.at(">") {
            let param = if self.at_word("region") && matches!(self.tok_at(1), Tok::Ident(_)) {
                self.bump();
                let name = self.ident()?;
                let default = if self.eat("=") { Some(self.ty()?) } else { None };
                TypeParam::Region { name, default }
            } else if self.at_word("row") && matches!(self.tok_at(1), Tok::Ident(_)) {
                self.bump();
                let name = self.ident()?;
                let bounds = if self.eat_kw(Kw::Extends) { self.bounds()? } else { Vec::new() };
                let default = if self.eat("=") { Some(self.ty()?) } else { None };
                TypeParam::Row { name, bounds, default }
            } else if self.eat_kw(Kw::Comptime) {
                let name = self.ident()?;
                self.expect(":")?;
                TypeParam::Comptime { name, ty: self.ty()? }
            } else {
                let name = self.ident()?;
                let bounds = if self.eat_kw(Kw::Extends) { self.bounds()? } else { Vec::new() };
                let default = if self.eat("=") { Some(self.ty()?) } else { None };
                TypeParam::Type { name, bounds, default }
            };
            params.push(param);
            if !self.eat(",") {
                break;
            }
        }
        self.expect(">")?;
        Ok(params)
    }

    fn bounds(&mut self) -> PResult<Vec<Type>> {
        let mut bounds = vec![self.ty_postfix()?];
        while self.eat("&") {
            bounds.push(self.ty_postfix()?);
        }
        Ok(bounds)
    }

    fn path(&mut self) -> PResult<Vec<Ident>> {
        let mut segments = vec![self.ident()?];
        while self.at(".") && matches!(self.tok_at(1), Tok::Ident(_) | Tok::Kw(_)) {
            self.bump();
            segments.push(self.member_name()?);
        }
        Ok(segments)
    }

    fn type_args(&mut self) -> PResult<Vec<Type>> {
        if !self.eat("<") {
            return Ok(Vec::new());
        }
        let mut args = Vec::new();
        while !self.at(">") {
            args.push(self.ty()?);
            if !self.eat(",") {
                break;
            }
        }
        self.expect(">")?;
        Ok(args)
    }

    // ---- types ----

    fn ty(&mut self) -> PResult<Type> {
        let start = self.span();
        if self.at("|") || matches!(self.tok(), Tok::Tag(_)) {
            return self.union_ty();
        }
        // A named union followed by `|` starts a union that includes it: `JsonError | #Port(u16)`.
        if matches!(self.tok(), Tok::Ident(_)) {
            let save = self.pos;
            let first = self.ty_postfix()?;
            if !self.at("|") {
                return Ok(first);
            }
            self.pos = save;
            return self.union_ty();
        }
        let kind = match self.tok() {
            Tok::Kw(Kw::Mut) if self.at_n(1, "(") => {
                self.bump();
                return self.fn_ty(FnMode::Mut, start);
            }
            Tok::Kw(Kw::Once) => {
                self.bump();
                return self.fn_ty(FnMode::Once, start);
            }
            Tok::Kw(Kw::Mut) => {
                self.bump();
                TypeKind::Mut(Box::new(self.ty()?))
            }
            Tok::Kw(Kw::Readonly) => {
                self.bump();
                TypeKind::Readonly(Box::new(self.ty()?))
            }
            Tok::Punct("(") => return self.fn_ty(FnMode::Shared, start),
            _ => return self.ty_postfix(),
        };
        Ok(Type { kind, span: self.since(start) })
    }

    fn fn_ty(&mut self, mode: FnMode, start: Span) -> PResult<Type> {
        let params = self.params(false)?;
        self.expect("=>")?;
        let ret = Box::new(self.ret()?);
        let uses = self.uses()?;
        Ok(Type { kind: TypeKind::Fn { mode, params, ret, uses }, span: self.since(start) })
    }

    fn union_ty(&mut self) -> PResult<Type> {
        let start = self.span();
        self.eat("|");
        let mut tags = Vec::new();
        let mut includes = Vec::new();
        let mut rest = None;
        loop {
            if self.eat("...") {
                rest = Some(self.ident()?);
                break;
            }
            if matches!(self.tok(), Tok::Ident(_)) {
                includes.push(self.ty_postfix()?);
            } else {
                tags.push(self.tag_decl()?);
            }
            if !self.eat("|") {
                break;
            }
        }
        Ok(Type { kind: TypeKind::Union { tags, includes, rest }, span: self.since(start) })
    }

    fn ty_postfix(&mut self) -> PResult<Type> {
        let start = self.span();
        let mut ty = self.ty_atom()?;
        loop {
            if self.at("[") {
                self.bump();
                let len = if self.at("]") { None } else { Some(Box::new(self.expr()?)) };
                self.expect("]")?;
                ty = Type { kind: TypeKind::Array { elem: Box::new(ty), len }, span: self.since(start) };
            } else if self.at("*") {
                self.bump();
                ty = Type { kind: TypeKind::Ptr(Box::new(ty)), span: self.since(start) };
            } else {
                return Ok(ty);
            }
        }
    }

    fn ty_atom(&mut self) -> PResult<Type> {
        let start = self.span();
        let kind = match self.tok().clone() {
            Tok::Punct("[") => {
                self.bump();
                if self.eat("]") {
                    TypeKind::EmptyRow
                } else {
                    let mut tys = vec![self.ty()?];
                    while self.eat(",") {
                        if self.at("]") {
                            break;
                        }
                        tys.push(self.ty()?);
                    }
                    self.expect("]")?;
                    TypeKind::Tuple(tys)
                }
            }
            Tok::Punct("{") => {
                self.bump();
                let mut fields = Vec::new();
                let mut rest = None;
                while !self.at("}") {
                    if self.eat("...") {
                        rest = Some(self.ident()?);
                        self.eat(";");
                        break;
                    }
                    let items = self.field_items()?;
                    if items.is_empty() {
                        break;
                    }
                    fields.extend(items);
                }
                self.expect("}")?;
                TypeKind::Record { fields, rest }
            }
            Tok::Kw(Kw::Dyn) => {
                self.bump();
                TypeKind::Dyn(self.path()?)
            }
            Tok::Ident(_) => {
                let segments = self.path()?;
                TypeKind::Path { segments, args: self.type_args()? }
            }
            Tok::Int(_) => TypeKind::Expr(Box::new(self.primary()?)),
            _ => return self.error("a type"),
        };
        Ok(Type { kind, span: self.since(start) })
    }

    // ---- blocks and statements ----

    fn block(&mut self) -> PResult<Block> {
        let start = self.expect("{")?;
        let mut stmts = Vec::new();
        let mut tail = None;
        while !self.at("}") {
            if self.at_kw(Kw::Const) || self.at_kw(Kw::Let) {
                let s = self.span();
                let mutable = self.bump().tok == Tok::Kw(Kw::Let);
                let pat = self.pattern_one()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                self.expect("=")?;
                let init = self.expr()?;
                self.expect(";")?;
                stmts.push(Stmt::Let { mutable, pat, ty, init, span: self.since(s) });
                continue;
            }
            if self.eat_kw(Kw::Defer) {
                // `defer { … }` defers a block, `defer e` an expression.
                let e = if self.at("{") { self.block_like()? } else { self.expr()? };
                stmts.push(Stmt::Defer(e));
                self.expect(";")?;
                continue;
            }
            let block_like = self.at_block_like();
            let e = if block_like { self.block_like()? } else { self.expr()? };
            if self.eat(";") {
                stmts.push(Stmt::Expr(e));
            } else if self.at("}") {
                tail = Some(Box::new(e));
            } else if block_like {
                stmts.push(Stmt::Expr(e));
            } else {
                return self.error("`;` or `}`");
            }
        }
        self.expect("}")?;
        Ok(Block { stmts, tail, span: self.since(start) })
    }

    /// Whether the `{` at token `at` begins a record literal: it is followed by an entry
    /// (`name:`, `[e]:`), or by a `comptime for` or `comptime if` whose items are entries.
    /// Flyscript has no labeled statements, so such a brace never begins a block.
    fn record_at(&self, at: usize) -> bool {
        let tok = |i: usize| &self.toks[i.min(self.toks.len() - 1)].tok;
        match tok(at + 1) {
            Tok::Ident(_) | Tok::Kw(_) if matches!(tok(at + 2), Tok::Punct(":")) => !matches!(tok(at + 1), Tok::Kw(Kw::Comptime)),
            // A shorthand entry followed by a comma: there is no comma operator, so no block
            // starts `{ name,` (`{ defs, main }`).
            Tok::Ident(_) if matches!(tok(at + 2), Tok::Punct(",")) => true,
            Tok::Punct("[") => self.close_from(at + 1).is_some_and(|c| matches!(tok(c + 1), Tok::Punct(":"))),
            Tok::Kw(Kw::Comptime) if matches!(tok(at + 2), Tok::Kw(Kw::For | Kw::If)) && matches!(tok(at + 3), Tok::Punct("(")) => {
                self.close_from(at + 3).is_some_and(|c| matches!(tok(c + 1), Tok::Punct("{")) && self.record_at(c + 1))
            }
            _ => false,
        }
    }

    fn at_block_like(&self) -> bool {
        if self.at("{") && self.record_at(self.pos) {
            return false;
        }
        matches!(
            self.tok(),
            Tok::Kw(Kw::If | Kw::While | Kw::For | Kw::Try | Kw::Unsafe) | Tok::Punct("{")
        ) || self.match_at(self.pos)
            || self.at_handle()
            || self.at_region()
            || self.at_kw(Kw::Comptime) && (matches!(self.tok_at(1), Tok::Kw(Kw::If | Kw::For)) || self.match_at(self.pos + 1))
    }

    /// A block-like expression in statement position: it is not continued by operators.
    fn block_like(&mut self) -> PResult<Expr> {
        if self.at("{") {
            let b = self.block()?;
            let span = b.span;
            return Ok(Expr { kind: ExprKind::Block(b), span });
        }
        if self.at_kw(Kw::Comptime) {
            let start = self.span();
            self.bump();
            let e = self.primary()?;
            return Ok(Expr { kind: ExprKind::Comptime(Box::new(e)), span: self.since(start) });
        }
        self.primary()
    }

    // ---- expressions ----

    fn expr(&mut self) -> PResult<Expr> {
        let start = self.span();
        let lhs = self.range()?;
        for op in ASSIGN {
            if self.at(op) {
                self.bump();
                let value = self.expr()?;
                return Ok(Expr {
                    kind: ExprKind::Assign { op, target: Box::new(lhs), value: Box::new(value) },
                    span: self.since(start),
                });
            }
        }
        Ok(lhs)
    }

    fn range(&mut self) -> PResult<Expr> {
        let start = self.span();
        let lo = if self.at("..") { None } else { Some(Box::new(self.binary(0)?)) };
        if !self.eat("..") {
            return Ok(*lo.expect("a non-range expression has a left operand"));
        }
        let hi = if matches!(self.tok(), Tok::Punct("]" | ")" | "," | ";" | "}")) {
            None
        } else {
            Some(Box::new(self.binary(0)?))
        };
        Ok(Expr { kind: ExprKind::Range { lo, hi }, span: self.since(start) })
    }

    fn binary_op(&self, level: usize) -> Option<(&'static str, usize)> {
        for &op in BINARY[level] {
            match op {
                "<<" if self.adjacent("<", "<") => return Some(("<<", 2)),
                ">>" if self.adjacent(">", ">") => return Some((">>", 2)),
                "<" | ">" if self.adjacent(op, op) => continue,
                _ if self.at(op) => return Some((op, 1)),
                _ => {}
            }
        }
        None
    }

    fn binary(&mut self, level: usize) -> PResult<Expr> {
        if level == BINARY.len() {
            return self.cast();
        }
        let start = self.span();
        let mut lhs = self.binary(level + 1)?;
        while let Some((op, width)) = self.binary_op(level) {
            for _ in 0..width {
                self.bump();
            }
            let rhs = self.binary(level + 1)?;
            lhs = Expr {
                kind: ExprKind::Binary { op, lhs: Box::new(lhs), rhs: Box::new(rhs) },
                span: self.since(start),
            };
        }
        Ok(lhs)
    }

    fn cast(&mut self) -> PResult<Expr> {
        let start = self.span();
        let mut e = self.unary()?;
        while self.eat_kw(Kw::As) {
            let ty = self.ty_postfix()?;
            e = Expr { kind: ExprKind::Cast { expr: Box::new(e), ty }, span: self.since(start) };
        }
        Ok(e)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let start = self.span();
        let kind = match self.tok() {
            Tok::Punct(op @ ("!" | "-" | "~")) => {
                let op = *op;
                self.bump();
                ExprKind::Unary { op, operand: Box::new(self.unary()?) }
            }
            Tok::Kw(Kw::Mut) => {
                self.bump();
                ExprKind::BorrowMut(Box::new(self.unary()?))
            }
            Tok::Kw(Kw::Throw) => {
                self.bump();
                ExprKind::Throw(Box::new(self.expr()?))
            }
            Tok::Kw(Kw::Yield) => {
                self.bump();
                ExprKind::Yield(Box::new(self.expr()?))
            }
            // A prefix operator, like TypeScript's `await`: `n < comptime -(1 << b)`.
            Tok::Kw(Kw::Comptime) => {
                self.bump();
                ExprKind::Comptime(Box::new(self.unary()?))
            }
            Tok::Kw(Kw::Return) => {
                self.bump();
                let value = if matches!(self.tok(), Tok::Punct(";" | "}" | "," | ")")) {
                    None
                } else {
                    Some(Box::new(self.expr()?))
                };
                ExprKind::Return(value)
            }
            _ => return self.postfix(),
        };
        Ok(Expr { kind, span: self.since(start) })
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let start = self.span();
        let mut e = self.primary()?;
        loop {
            if self.at(".") && self.at_n(1, "[") {
                self.bump();
                self.bump();
                let name = self.expr()?;
                self.expect("]")?;
                e = Expr { kind: ExprKind::FieldAt { target: Box::new(e), name: Box::new(name) }, span: self.since(start) };
            } else if self.at(".") {
                self.bump();
                let name = self.member_name()?;
                e = Expr { kind: ExprKind::Field { target: Box::new(e), name }, span: self.since(start) };
            } else if self.at("(") {
                let args = self.args()?;
                e = Expr {
                    kind: ExprKind::Call { callee: Box::new(e), type_args: Vec::new(), args },
                    span: self.since(start),
                };
            } else if self.at("[") {
                self.bump();
                let index = self.expr()?;
                self.expect("]")?;
                e = Expr {
                    kind: ExprKind::Index { target: Box::new(e), index: Box::new(index) },
                    span: self.since(start),
                };
            } else if self.at("<") && matches!(e.kind, ExprKind::Ident(_) | ExprKind::Field { .. }) {
                // TypeScript's rule: `f<…>(` is a generic call when the `<…>` parses as type
                // arguments and is followed directly by `(`; otherwise `<` is less-than.
                let Some(type_args) = self.attempt(|p| {
                    let args = p.type_args()?;
                    if p.at("(") { Ok(args) } else { p.error("`(`") }
                }) else {
                    return Ok(e);
                };
                let args = self.args()?;
                e = Expr {
                    kind: ExprKind::Call { callee: Box::new(e), type_args, args },
                    span: self.since(start),
                };
            } else {
                return Ok(e);
            }
        }
    }

    fn tag_args(&mut self) -> PResult<TagArgs> {
        Ok(if self.at("(") {
            TagArgs::Tuple(self.args()?)
        } else if self.at("{") {
            TagArgs::Record(self.field_inits()?)
        } else {
            TagArgs::None
        })
    }

    fn args(&mut self) -> PResult<Vec<Expr>> {
        self.expect("(")?;
        let mut args = Vec::new();
        while !self.at(")") {
            args.push(self.expr()?);
            if !self.eat(",") {
                break;
            }
        }
        self.expect(")")?;
        Ok(args)
    }

    fn is_lambda(&self) -> bool {
        self.matching_close().is_some_and(|close| matches!(self.toks[(close + 1).min(self.toks.len() - 1)].tok, Tok::Punct("=>")))
    }

    fn primary(&mut self) -> PResult<Expr> {
        let start = self.span();
        let kind = match self.tok().clone() {
            Tok::Int(s) => {
                self.bump();
                ExprKind::Int(s)
            }
            Tok::Float(s) => {
                self.bump();
                ExprKind::Float(s)
            }
            Tok::Byte(b) => {
                self.bump();
                ExprKind::Byte(b)
            }
            Tok::Str(s) => {
                self.bump();
                ExprKind::Str(s)
            }
            Tok::Template(parts) => {
                self.bump();
                ExprKind::Template(self.template(parts)?)
            }
            Tok::Kw(Kw::True) => {
                self.bump();
                ExprKind::Bool(true)
            }
            Tok::Kw(Kw::False) => {
                self.bump();
                ExprKind::Bool(false)
            }
            Tok::Kw(Kw::Break) => {
                self.bump();
                ExprKind::Break
            }
            Tok::Kw(Kw::Continue) => {
                self.bump();
                ExprKind::Continue
            }
            Tok::Tag(name) => {
                self.bump();
                ExprKind::Tag { name, args: self.tag_args()? }
            }
            Tok::Punct("#[") => {
                self.bump();
                let name = self.expr()?;
                self.expect("]")?;
                ExprKind::TagAt { name: Box::new(name), args: self.tag_args()? }
            }
            Tok::Ident(name) if !self.match_at(self.pos) && !self.at_region() && !self.at_handle() => {
                // `Name { … }` is a struct literal; blocks never follow an expression directly.
                if name.starts_with(|c: char| c.is_uppercase()) && self.at_n(1, "{") {
                    let ident = self.ident()?;
                    let fields = self.field_inits()?;
                    ExprKind::Record { name: Some(vec![ident]), fields }
                } else {
                    self.bump();
                    ExprKind::Ident(name)
                }
            }
            Tok::Punct("(") if self.is_lambda() => {
                let (params, unpack) = self.lambda_params()?;
                self.expect("=>")?;
                let body = if self.at("{") {
                    let mut b = self.block()?;
                    b.stmts.splice(0..0, unpack);
                    let span = b.span;
                    Expr { kind: ExprKind::Block(b), span }
                } else {
                    let e = self.expr()?;
                    if unpack.is_empty() {
                        e
                    } else {
                        let span = e.span;
                        Expr { kind: ExprKind::Block(Block { stmts: unpack, tail: Some(Box::new(e)), span }), span }
                    }
                };
                ExprKind::Lambda { params, body: Box::new(body) }
            }
            Tok::Punct("(") => {
                self.bump();
                let e = self.expr()?;
                self.expect(")")?;
                return Ok(e);
            }
            Tok::Punct("[") => {
                self.bump();
                let mut items = Vec::new();
                while !self.at("]") {
                    items.push(self.expr()?);
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("]")?;
                ExprKind::List(items)
            }
            Tok::Punct("{") => ExprKind::Record { name: None, fields: self.field_inits()? },
            Tok::Kw(Kw::If) => self.if_expr()?,
            Tok::Kw(Kw::While) => {
                let kw = self.span();
                self.bump();
                // `while (const #Some(x) = e) { … }` loops while `e` matches.
                if let Some((pat, scrutinee, body)) = self.let_head()? {
                    // Each piece has a span of its own: what is recorded about it is keyed by span.
                    let all = Span { start: kw.start, end: body.span.end };
                    let end = Span { start: body.span.end, end: body.span.end };
                    let head = Span { start: scrutinee.span.start, end: body.span.end };
                    let arms = vec![
                        MatchArm::new(pat, None, Expr { kind: ExprKind::Block(body.clone()), span: body.span }),
                        MatchArm::new(Pattern { kind: PatternKind::Wild, span: end }, None, Expr { kind: ExprKind::Break, span: end }),
                    ];
                    let m = Expr { kind: ExprKind::Match { scrutinee: Box::new(scrutinee), arms }, span: head };
                    let yes = Expr { kind: ExprKind::Bool(true), span: kw };
                    ExprKind::While { cond: Box::new(yes), body: Block { stmts: vec![Stmt::Expr(m)], tail: None, span: all } }
                } else {
                    let cond = self.paren_expr()?;
                    ExprKind::While { cond: Box::new(cond), body: self.block()? }
                }
            }
            Tok::Kw(Kw::For) => {
                self.bump();
                self.expect("(")?;
                let mutable = match self.tok() {
                    Tok::Kw(Kw::Const) => false,
                    Tok::Kw(Kw::Let) => true,
                    _ => return self.error("`const` or `let`"),
                };
                self.bump();
                let pat = self.pattern_one()?;
                self.expect_word("of")?;
                let iter = self.expr()?;
                self.expect(")")?;
                ExprKind::For { mutable, pat, iter: Box::new(iter), body: self.block()? }
            }
            Tok::Ident(w) if w == "match" && self.match_at(self.pos) => {
                self.bump();
                let scrutinee = self.paren_expr()?;
                self.expect("{")?;
                let arms = self.arm_items()?;
                self.expect("}")?;
                ExprKind::Match { scrutinee: Box::new(scrutinee), arms }
            }
            Tok::Kw(Kw::Try) => {
                self.bump();
                let body = self.block()?;
                self.expect_kw(Kw::Catch)?;
                self.expect("(")?;
                let pat = self.pattern()?;
                self.expect(")")?;
                ExprKind::Try { body, pat, handler: self.block()? }
            }
            Tok::Ident(_) if self.at_region() => {
                self.bump();
                self.expect("(")?;
                let name = self.ident()?;
                self.expect(")")?;
                ExprKind::Region { name, body: self.block()? }
            }
            Tok::Ident(_) if self.at_handle() => {
                self.bump();
                let mut body = self.block()?;
                // `handle { … } with A { … } with B { … }` handles `A` innermost, then `B`.
                let mut handled = None;
                while self.eat_word("with") {
                    if let Some(kind) = handled.take() {
                        let span = self.since(start);
                        body = Block { stmts: Vec::new(), tail: Some(Box::new(Expr { kind, span })), span };
                    }
                    let effect = self.ty_postfix()?;
                    self.expect("{")?;
                    let mut arms = Vec::new();
                    while !self.at("}") {
                        let op = self.member_name()?;
                        self.expect("(")?;
                        let mut params = Vec::new();
                        while !self.at(")") {
                            params.push(self.ident()?);
                            if !self.eat(",") {
                                break;
                            }
                        }
                        self.expect(")")?;
                        let resumes = if self.eat_word("resumes") { Some(self.ident()?) } else { None };
                        self.expect("=>")?;
                        // An arm's body is a block or an expression, as in `match`.
                        let arm_body = if self.at("{") {
                            let b = self.block()?;
                            self.eat(",");
                            b
                        } else {
                            let e = self.expr()?;
                            let span = e.span;
                            self.eat(",");
                            Block { stmts: Vec::new(), tail: Some(Box::new(e)), span }
                        };
                        arms.push(HandlerArm { op, params, resumes, body: arm_body });
                    }
                    self.expect("}")?;
                    handled = Some(ExprKind::Handle { body: body.clone(), effect, arms });
                }
                match handled {
                    Some(kind) => kind,
                    None => return self.error("`with`"),
                }
            }
            Tok::Kw(Kw::Unsafe) => {
                self.bump();
                ExprKind::Unsafe(self.block()?)
            }
            _ => return self.error("an expression"),
        };
        Ok(Expr { kind, span: self.since(start) })
    }

    /// Match arms up to a closing `}`.
    fn arm_items(&mut self) -> PResult<Vec<MatchArm>> {
        let mut arms = Vec::new();
        while !self.at("}") {
            if self.at_kw(Kw::Comptime) && (matches!(self.tok_at(1), Tok::Kw(Kw::For | Kw::If)) || self.word_at(1, "match")) {
                let start = self.span();
                let g = self.generate(Self::arm_items)?;
                let span = self.since(start);
                let mut arm = MatchArm::new(Pattern { kind: PatternKind::Wild, span }, None, Expr { kind: ExprKind::Break, span });
                arm.generate = Some(Box::new(g));
                arms.push(arm);
                self.eat(",");
                continue;
            }
            let pat = self.pattern()?;
            let guard = if self.eat_kw(Kw::If) { Some(self.expr()?) } else { None };
            self.expect("=>")?;
            if self.at("{") {
                let b = self.block()?;
                let span = b.span;
                arms.push(MatchArm::new(pat, guard, Expr { kind: ExprKind::Block(b), span }));
                self.eat(",");
            } else {
                arms.push(MatchArm::new(pat, guard, self.expr()?));
                if !self.eat(",") {
                    break;
                }
            }
        }
        Ok(arms)
    }

    fn paren_expr(&mut self) -> PResult<Expr> {
        self.expect("(")?;
        let e = self.expr()?;
        self.expect(")")?;
        Ok(e)
    }

    /// The head and block of `if (const|let Pat = e) { … }` or its `while`, if that is next.
    fn let_head(&mut self) -> PResult<Option<(Pattern, Expr, Block)>> {
        if !(self.at("(") && matches!(self.tok_at(1), Tok::Kw(Kw::Const | Kw::Let))) {
            return Ok(None);
        }
        self.bump();
        let mutable = self.eat_kw(Kw::Let);
        if !mutable {
            self.bump();
        }
        let pat = self.pattern()?;
        self.expect("=")?;
        let scrutinee = self.expr()?;
        self.expect(")")?;
        let mut body = self.block()?;
        // `let` makes the names it binds mutable in the block.
        if mutable {
            let mut names = Vec::new();
            bound_names(&pat, &mut names);
            let lets = names.into_iter().map(|(name, span)| Stmt::Let {
                mutable: true,
                pat: Pattern { kind: PatternKind::Bind(name.clone()), span },
                ty: None,
                init: Expr { kind: ExprKind::Ident(name), span },
                span,
            });
            body.stmts.splice(0..0, lets);
        }
        Ok(Some((pat, scrutinee, body)))
    }

    fn if_expr(&mut self) -> PResult<ExprKind> {
        self.expect_kw(Kw::If)?;
        // `if (const #Some(x) = e) { … } else { … }` is a two-armed `match`.
        if let Some((pat, scrutinee, then)) = self.let_head()? {
            let start = self.span();
            let otherwise = if self.eat_kw(Kw::Else) {
                if self.at_kw(Kw::If) {
                    let kind = self.if_expr()?;
                    Expr { kind, span: self.since(start) }
                } else {
                    let b = self.block()?;
                    let span = b.span;
                    Expr { kind: ExprKind::Block(b), span }
                }
            } else {
                Expr { kind: ExprKind::Block(Block { stmts: Vec::new(), tail: None, span: start }), span: start }
            };
            let span = then.span;
            let rest = Pattern { kind: PatternKind::Wild, span: otherwise.span };
            let arms = vec![MatchArm::new(pat, None, Expr { kind: ExprKind::Block(then), span }), MatchArm::new(rest, None, otherwise)];
            return Ok(ExprKind::Match { scrutinee: Box::new(scrutinee), arms });
        }
        let cond = self.paren_expr()?;
        let then = self.block()?;
        let otherwise = if self.eat_kw(Kw::Else) {
            let start = self.span();
            let e = if self.at_kw(Kw::If) {
                let kind = self.if_expr()?;
                Expr { kind, span: self.since(start) }
            } else {
                let b = self.block()?;
                let span = b.span;
                Expr { kind: ExprKind::Block(b), span }
            };
            Some(Box::new(e))
        } else {
            None
        };
        Ok(ExprKind::If { cond: Box::new(cond), then, otherwise })
    }

    fn field_inits(&mut self) -> PResult<Vec<FieldInit>> {
        self.expect("{")?;
        let fields = self.init_items()?;
        self.expect("}")?;
        Ok(fields)
    }

    /// Record-literal entries up to a closing `}`.
    fn init_items(&mut self) -> PResult<Vec<FieldInit>> {
        let mut fields = Vec::new();
        while !self.at("}") {
            if self.at_kw(Kw::Comptime) && (matches!(self.tok_at(1), Tok::Kw(Kw::For | Kw::If)) || self.word_at(1, "match")) {
                let start = self.span();
                let g = self.generate(Self::init_items)?;
                let mut f = FieldInit::new(Ident { name: String::new(), span: self.since(start) }, None);
                f.generate = Some(Box::new(g));
                fields.push(f);
                self.eat(",");
                continue;
            }
            let (name, computed) = self.entry_name()?;
            let value = if computed.is_some() || self.at(":") {
                self.expect(":")?;
                Some(self.expr()?)
            } else {
                None
            };
            fields.push(FieldInit { name, value, computed, generate: None });
            if !self.eat(",") {
                break;
            }
        }
        Ok(fields)
    }

    fn template(&mut self, parts: Vec<TemplatePart>) -> PResult<Vec<TemplatePiece>> {
        parts
            .into_iter()
            .map(|part| match part {
                TemplatePart::Lit(s) => Ok(TemplatePiece::Lit(s)),
                TemplatePart::Expr(span) => {
                    let mut sub = Parser::new(self.src, lex_range(self.src, span.start, span.end)?);
                    let e = sub.expr()?;
                    sub.expect_eof()?;
                    Ok(TemplatePiece::Expr(e))
                }
            })
            .collect()
    }

    // ---- patterns ----

    fn pattern(&mut self) -> PResult<Pattern> {
        let start = self.span();
        let first = self.pattern_one()?;
        if !self.at("|") {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat("|") {
            alts.push(self.pattern_one()?);
        }
        Ok(Pattern { kind: PatternKind::Or(alts), span: self.since(start) })
    }

    fn pattern_one(&mut self) -> PResult<Pattern> {
        let start = self.span();
        let kind = match self.tok().clone() {
            Tok::Ident(name) if name == "_" => {
                self.bump();
                PatternKind::Wild
            }
            Tok::Ident(name) if name.starts_with(|c: char| c.is_uppercase()) && self.at_n(1, "{") => {
                let ident = self.ident()?;
                PatternKind::Record { name: Some(vec![ident]), fields: self.field_pats()? }
            }
            Tok::Ident(name) => {
                self.bump();
                PatternKind::Bind(name)
            }
            Tok::Tag(name) => {
                self.bump();
                PatternKind::Tag { name, args: self.tag_pat_args()? }
            }
            Tok::Punct("#[") => {
                self.bump();
                let name = self.expr()?;
                self.expect("]")?;
                PatternKind::TagAt { name: Box::new(name), args: self.tag_pat_args()? }
            }
            // A value computed by `comptime` code: `comptime f.name => …`.
            Tok::Kw(Kw::Comptime) => {
                let start = self.span();
                self.bump();
                let e = self.postfix()?;
                PatternKind::Lit(Box::new(Expr { kind: ExprKind::Comptime(Box::new(e)), span: self.since(start) }))
            }
            Tok::Punct("[") => {
                self.bump();
                let mut pats = Vec::new();
                while !self.at("]") {
                    pats.push(self.pattern()?);
                    if !self.eat(",") {
                        break;
                    }
                }
                self.expect("]")?;
                PatternKind::Tuple(pats)
            }
            Tok::Punct("{") => PatternKind::Record { name: None, fields: self.field_pats()? },
            Tok::Int(_) | Tok::Float(_) | Tok::Byte(_) | Tok::Str(_) | Tok::Kw(Kw::True | Kw::False) => {
                PatternKind::Lit(Box::new(self.primary()?))
            }
            Tok::Punct("-") => PatternKind::Lit(Box::new(self.unary()?)),
            _ => return self.error("a pattern"),
        };
        Ok(Pattern { kind, span: self.since(start) })
    }

    fn tag_pat_args(&mut self) -> PResult<TagPatArgs> {
        Ok(if self.at("(") {
            self.bump();
            let mut pats = Vec::new();
            while !self.at(")") {
                pats.push(self.pattern()?);
                if !self.eat(",") {
                    break;
                }
            }
            self.expect(")")?;
            TagPatArgs::Tuple(pats)
        } else if self.at("{") {
            TagPatArgs::Record(self.field_pats()?)
        } else {
            TagPatArgs::None
        })
    }

    fn field_pats(&mut self) -> PResult<Vec<(Ident, Option<Pattern>)>> {
        self.expect("{")?;
        let mut fields = Vec::new();
        while !self.at("}") {
            let name = self.ident()?;
            let pat = if self.eat(":") { Some(self.pattern()?) } else { None };
            fields.push((name, pat));
            if !self.eat(",") {
                break;
            }
        }
        self.expect("}")?;
        Ok(fields)
    }
}

/// The names a pattern binds, with where.
fn bound_names(p: &Pattern, out: &mut Vec<(String, Span)>) {
    match &p.kind {
        PatternKind::Bind(n) => out.push((n.clone(), p.span)),
        PatternKind::Tuple(ps) | PatternKind::Or(ps) => ps.iter().for_each(|q| bound_names(q, out)),
        PatternKind::Record { fields, .. } => {
            for (n, q) in fields {
                match q {
                    Some(q) => bound_names(q, out),
                    None => out.push((n.name.clone(), n.span)),
                }
            }
        }
        PatternKind::Tag { args, .. } | PatternKind::TagAt { args, .. } => match args {
            TagPatArgs::None => {}
            TagPatArgs::Tuple(ps) => ps.iter().for_each(|q| bound_names(q, out)),
            TagPatArgs::Record(fs) => {
                for (n, q) in fs {
                    match q {
                        Some(q) => bound_names(q, out),
                        None => out.push((n.name.clone(), n.span)),
                    }
                }
            }
        },
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kind(src: &str) -> ExprKind {
        parse_expr(src).unwrap_or_else(|d| panic!("{}", d.render("test", src))).kind
    }

    #[test]
    fn generic_call_versus_comparison() {
        assert!(matches!(kind("HashMap.new<String, u64>()"), ExprKind::Call { type_args, .. } if type_args.len() == 2));
        assert!(matches!(kind("x < 0 || y > 0"), ExprKind::Binary { op: "||", .. }));
        assert!(matches!(kind("a < b > (c)"), ExprKind::Call { .. }));
    }

    #[test]
    fn shifts_are_adjacent_angle_brackets() {
        assert!(matches!(kind("a >> 2"), ExprKind::Binary { op: ">>", .. }));
        assert!(matches!(kind("a > b"), ExprKind::Binary { op: ">", .. }));
    }

    #[test]
    fn lambdas_records_and_tags() {
        assert!(matches!(kind("(p, _) => p.x"), ExprKind::Lambda { .. }));
        assert!(matches!(kind("(a + b)"), ExprKind::Binary { op: "+", .. }));
        assert!(matches!(kind("{ x, y: 2 }"), ExprKind::Record { name: None, .. }));
        assert!(matches!(kind("#Get { key, reply }"), ExprKind::Tag { args: TagArgs::Record(_), .. }));
        assert!(matches!(kind("Decl { name, ty: Cell.new(0) }"), ExprKind::Record { name: Some(_), .. }));
    }

    /// The value of a block's tail: `{ { a: 1 } }` holds a record, `{ { x } }` a block.
    fn tail(src: &str) -> ExprKind {
        match kind(&format!("() => {src}")) {
            ExprKind::Lambda { body, .. } => match body.kind {
                ExprKind::Block(b) => b.tail.expect("a tail").kind,
                other => other,
            },
            other => other,
        }
    }

    #[test]
    fn braces_at_statement_start() {
        assert!(matches!(tail("{ { a: 1, b } }"), ExprKind::Record { .. }));
        assert!(matches!(tail("{ { [k]: 1 } }"), ExprKind::Record { .. }));
        assert!(matches!(tail("{ { comptime for (const f of fs) { [f.name]: 0, } } }"), ExprKind::Record { .. }));
        assert!(matches!(tail("{ { x } }"), ExprKind::Block(_)));
        assert!(matches!(tail("{ { comptime for (const f of fs) { f(); } } }"), ExprKind::Block(_)));
        assert!(matches!(tail("{ { [a, b] } }"), ExprKind::Block(_)));
    }

    #[test]
    fn ranges_inside_index() {
        assert!(matches!(kind("raw[0..8]"), ExprKind::Index { .. }));
        assert!(matches!(kind("buf[..n]"), ExprKind::Index { .. }));
    }

    #[test]
    fn reserved_words_as_member_names() {
        let src = "effect Yield<T> { yield(item: T): void; }";
        parse_module(src).unwrap_or_else(|d| panic!("{}", d.render("test", src)));
        assert!(matches!(kind("Yield.yield(x)"), ExprKind::Call { .. }));
        assert!(matches!(kind("{ default: 1 }"), ExprKind::Record { .. }));
    }

    #[test]
    fn type_rows_stop_at_the_next_parameter() {
        let src = "function zip<A, row E>(a: once () => void uses Yield<A>, ...E, b: i32): void uses ...E {}";
        let m = parse_module(src).unwrap_or_else(|d| panic!("{}", d.render("test", src)));
        let ItemKind::Function(f) = &m.items[0].kind else { panic!() };
        assert_eq!(f.sig.params.len(), 2);
    }
}
