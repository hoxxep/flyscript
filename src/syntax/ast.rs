//! The surface syntax tree. It mirrors the grammar in docs/spec.md §2.3 closely; desugaring
//! (`throw`, `try`, `yield`, `for`) happens in later passes, not here.

use crate::diag::Span;

#[derive(Clone, Debug, PartialEq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Module {
    pub items: Vec<Item>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Item {
    pub exported: bool,
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ItemKind {
    Import { names: Vec<Ident>, from: String },
    Struct(StructDecl),
    Enum(EnumDecl),
    Interface(InterfaceDecl),
    Impl(ImplDecl),
    TypeAlias(TypeAlias),
    Effect(EffectDecl),
    Function(FnDecl),
    Extern(FnSig),
}

#[derive(Clone, Debug, PartialEq)]
pub struct StructDecl {
    pub layout: Option<Ident>,
    pub name: Ident,
    pub params: Vec<TypeParam>,
    /// `None` for an opaque declaration (`struct Socket;`), allowed only in `.d.fly` files.
    pub fields: Option<Vec<Field>>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub name: Ident,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumDecl {
    pub name: Ident,
    pub params: Vec<TypeParam>,
    pub tags: Vec<TagDecl>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TagDecl {
    pub name: Ident,
    pub payload: TagPayload,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TagPayload {
    None,
    Tuple(Vec<Type>),
    Record(Vec<Field>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct InterfaceDecl {
    pub name: Ident,
    pub params: Vec<TypeParam>,
    pub members: Vec<InterfaceMember>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum InterfaceMember {
    Method(FnSig),
    AssocType { name: Ident, bounds: Vec<Type> },
}

#[derive(Clone, Debug, PartialEq)]
pub struct ImplDecl {
    pub params: Vec<TypeParam>,
    /// `impl I for T` has `interface: Some(I)` and `target: T`; `impl T` has `interface: None`.
    pub interface: Option<Type>,
    pub target: Type,
    pub methods: Vec<Method>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Method {
    pub exported: bool,
    pub decl: FnDecl,
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeAlias {
    pub name: Ident,
    pub params: Vec<TypeParam>,
    pub ty: Type,
}

#[derive(Clone, Debug, PartialEq)]
pub struct EffectDecl {
    pub name: Ident,
    pub params: Vec<TypeParam>,
    pub ops: Vec<FnSig>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FnSig {
    pub comptime: bool,
    pub name: Ident,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub ret: Return,
    /// `None` when there is no `uses` clause.
    pub uses: Option<Vec<RowItem>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FnDecl {
    pub sig: FnSig,
    /// `None` for a signature ending in `;`, allowed only in `.d.fly` files.
    pub body: Option<Block>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub comptime: bool,
    pub name: Ident,
    /// `None` only for untyped lambda parameters.
    pub ty: Option<Type>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Return {
    pub ty: Type,
    pub from: Option<Ident>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeParam {
    Region { name: Ident, default: Option<Type> },
    Row { name: Ident, default: Option<Type> },
    Comptime { name: Ident, ty: Type },
    Type { name: Ident, bounds: Vec<Type>, default: Option<Type> },
}

#[derive(Clone, Debug, PartialEq)]
pub enum RowItem {
    Effect(Type),
    Spread(Ident),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum FnMode {
    Shared,
    Mut,
    Once,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeKind {
    /// A primitive, a named type, a type parameter or an associated type (`C.View`).
    Path { segments: Vec<Ident>, args: Vec<Type> },
    /// A `comptime` type function application: `Ring(u8, 1024)`.
    Call { path: Vec<Ident>, args: Vec<Expr> },
    Record { fields: Vec<Field>, rest: Option<Ident> },
    Union { tags: Vec<TagDecl>, rest: Option<Ident> },
    Tuple(Vec<Type>),
    /// `[]`: the empty row, used as a row default.
    EmptyRow,
    Fn { mode: FnMode, params: Vec<Param>, ret: Box<Return>, uses: Option<Vec<RowItem>> },
    /// `T[N]` when `len` is present, the slice `T[]` otherwise.
    Array { elem: Box<Type>, len: Option<Box<Expr>> },
    Mut(Box<Type>),
    Readonly(Box<Type>),
    Ptr(Box<Type>),
    Dyn(Vec<Ident>),
    /// A `comptime` expression in type position, e.g. an array length.
    Expr(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<Box<Expr>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Let { mutable: bool, pat: Pattern, ty: Option<Type>, init: Expr, span: Span },
    Defer(Expr),
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldInit {
    pub name: Ident,
    /// `None` for a punned field: `{ x }` means `{ x: x }`.
    pub value: Option<Expr>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TagArgs {
    None,
    Tuple(Vec<Expr>),
    Record(Vec<FieldInit>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TemplatePiece {
    Lit(String),
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Int(String),
    Float(String),
    Byte(u8),
    Str(String),
    Template(Vec<TemplatePiece>),
    Bool(bool),
    Ident(String),
    Tag { name: String, args: TagArgs },
    /// `{ … }` or `Name { … }`.
    Record { name: Option<Vec<Ident>>, fields: Vec<FieldInit> },
    /// `[a, b]`: a tuple or array literal, resolved by type.
    List(Vec<Expr>),
    /// An anonymous struct type built by `comptime` code: `struct { … }`.
    StructType(Vec<Field>),
    Field { target: Box<Expr>, name: Ident },
    Index { target: Box<Expr>, index: Box<Expr> },
    Call { callee: Box<Expr>, type_args: Vec<Type>, args: Vec<Expr> },
    Unary { op: &'static str, operand: Box<Expr> },
    /// `mut e` at a call site.
    BorrowMut(Box<Expr>),
    Binary { op: &'static str, lhs: Box<Expr>, rhs: Box<Expr> },
    Assign { op: &'static str, target: Box<Expr>, value: Box<Expr> },
    Cast { expr: Box<Expr>, ty: Type },
    Range { lo: Option<Box<Expr>>, hi: Option<Box<Expr>> },
    Lambda { params: Vec<Param>, body: Box<Expr> },
    Block(Block),
    If { cond: Box<Expr>, then: Block, otherwise: Option<Box<Expr>> },
    While { cond: Box<Expr>, body: Block },
    For { mutable: bool, pat: Pattern, iter: Box<Expr>, body: Block },
    Match { scrutinee: Box<Expr>, arms: Vec<MatchArm> },
    Try { body: Block, pat: Pattern, handler: Block },
    Throw(Box<Expr>),
    Yield(Box<Expr>),
    Return(Option<Box<Expr>>),
    Break,
    Continue,
    Region { name: Ident, body: Block },
    Handle { body: Block, effect: Type, arms: Vec<HandlerArm> },
    Unsafe(Block),
    Comptime(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct MatchArm {
    pub pat: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub struct HandlerArm {
    pub op: Ident,
    pub params: Vec<Ident>,
    pub resumes: Option<Ident>,
    pub body: Block,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum PatternKind {
    Wild,
    Bind(String),
    Lit(Box<Expr>),
    Tag { name: String, args: TagPatArgs },
    Tuple(Vec<Pattern>),
    Record { name: Option<Vec<Ident>>, fields: Vec<(Ident, Option<Pattern>)> },
    Or(Vec<Pattern>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum TagPatArgs {
    None,
    Tuple(Vec<Pattern>),
    Record(Vec<(Ident, Option<Pattern>)>),
}
