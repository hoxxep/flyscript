# Attributes, and one data model for every format: a proposal

Flyscript has one attribute today. `@layout(c)` and `@layout(c, align = N)` are written before `struct`, and both parsers handle them as a special case (`layout()` in `selfhost/parse.fly` and in `src/syntax/parser.rs`). Three pieces of work now need more. A single file run outside a package declares what it depends on with `@!script(…)`. Tests are marked `@test` and test-only code `@only(test)`, which another proposal is designing (`docs/reviews/2026-10-25-unit-tests-design.md`, on its own branch). And a serious codec has to be told, at the declaration, that a field is called `user_name` on the wire.

This proposal is in two parts. **Part 1** makes the attribute general: where one may go, what its arguments are, how a library declares one, what is reported, and the exact form of `@!script`. **Part 2** builds Fly's counterpart of Rust's serde on top of it. It first explains how `std/json` works today. It then weighs JSON's per-format derivations against a data model that every format shares, and proposes `std/codec`: one derivation per direction over reflection, read through `@wire(…)` attributes, with formats as libraries. Neither part is implemented, and `docs/spec.md` is not changed.

Examples use today's imports, `import { x } from "m"`. The dotted form being designed in another session changes only how they are spelled (`import std.codec.{ wire, Encode }`). Wherever a feature already exists, the code parses today once its attributes are removed. Code that uses a feature proposed here is marked as a sketch.

## The design in brief

1. **An attribute is data attached to a declaration.** `@name(…)` holds a compile-time constant for the declaration that follows it. It runs nothing and rewrites nothing. The compiler reads its own attributes, and any other is read by `comptime` code through reflection. Attributes are never macros.
2. **One grammar:** `@name`, `@name(flag)`, `@name(key = e, …)` and `@a.b(…)` for a namespaced one. A bare name is a flag (`key = true`). A value is an expression evaluated at compile time. The only unnamed value is an attribute's one declared *main* argument, which comes first: `@only(test && !wasm)`.
3. **They go on declarations and their members:** items and imports, struct fields, enum tags and the fields of a tag's record, functions in impls and interfaces, and effect operations. They do not go on expressions, statements, parameters or structural types. `@!name(…)` goes on the module, at the top of the file.
4. **A library declares an attribute as a struct**, marked `@attribute(on = […])`. Its fields are the attribute's arguments, and it is imported and namespaced like any other name. The compiler's own attributes are declared the same way, in the prelude.
5. **Conditional compilation is `@only(c)`.** `c` is a boolean expression (`!`, `&&`, `||`, `==`, `!=`) over a closed set of build facts: `test`, `native`, `freestanding`, `wasm`, `page`, `js`, `os`, `arch` and `pointerWidth`. It is decided before names are resolved. Code may name what is gated only under a condition that implies the gate, and that is checked across every build, so the error is the same in every build.
6. **An attribute that is not declared is an error**, and so is an argument the attribute lacks, a value of the wrong type, or an attribute in a place it does not allow.
7. **`@!script(package = {…}, dependencies = {…})`** takes `fly.toml`'s tables with `fly.toml`'s keys, written as Flyscript records of literal data. `fly` reads it with the compiler's parser before anything is compiled, and the compiler checks only its shape.
8. **Encoding gets one data model.** A type is encoded through `Encode` and decoded through `Decode`, each derived once over reflection. A format implements `Encoder` and `Decoder`. Field and tag names reach the format as compile-time constants, so JSON escapes a key once, in the compiler, and matches keys without allocating.
9. **`@wire(…)`** on structs, enums, fields and tags covers `rename`, `renameAll`, `alias`, `skip`, `default`, `flatten`, `omitNone`, `tag`/`content`/`untagged` and `denyUnknown`. JSON's output for an unannotated type is unchanged.

---

# Part 1: Attributes

## 1.1 What an attribute is

An attribute is a value the compiler holds for a declaration. Nothing happens because an attribute is there. What it means is decided by whatever reads it. The compiler reads its own attributes, which are `@layout`, `@attribute`, `@!script` and the test proposal's `@test` and `@only`, and a library's derivation reads the library's attributes through `Type.info`.

That is law 5 applied to annotations. Rust's attributes are token trees, and a procedural macro turns them into code. Flyscript already generates code with `comptime`, so an attribute only has to be data that a derivation can see: typed, checked where it is written, and read as a constant. No macro system is needed, and no second language runs inside the compiler.

## 1.2 Where attributes go

| Place | Example | Reflected |
| :--- | :--- | :--- |
| A module (`@!`) | `@!script(dependencies = { … })` | no |
| An item: struct, enum, interface, impl, type alias, effect, function, extern, const | `@layout(c) struct Pair { … }` | struct and enum |
| An import or re-export | `@only(test) import { assertEq } from "std/test";` | no |
| A braced group of items | `@only(test) { … }` | no |
| A struct field | `@wire(rename = "user_name") userName: String;` | yes |
| An enum tag | `@wire(rename = "rect") #Rectangle { … }` | yes |
| A field of a tag's record, in an enum | `#Circle { @wire(rename = "r") radius: f64 }` | yes |
| A function in an impl or interface, an effect operation | `@only(test) function sample(): Self { … }` | no |

Attributes come **before `export`**: `@layout(c) export struct Pair`. That puts every attribute in the same place, and it is the order the test proposal already chose. The parser today accepts `@layout` only after `export`, but nothing in the repository exports a struct with a layout, so the order can change now.

Four places are left out on purpose.

- **Structural types.** Records, tuples and tag unions are structural. `{ id: u64 }` written in two modules is the same type, and a type alias is only another name for it. An attribute on a structural type would make two equal types different, or would be lost when the alias expands. A type that needs a wire format of its own is declared as a struct or enum, which has a name to carry the attribute. A tag's record payload in an enum is the one exception, because it is written inside a nominal declaration. Its attributes belong to the enum, and reflection gives them to the tag (§1.10).
- **Parameters.** No attribute needs one yet, and functions are not reflected (`#Fn` carries nothing), so a library could not read it. The parser reserves the position: `@` before a parameter is an error that says parameters take no attributes yet.
- **Statements and expressions.** Code is chosen with `comptime if`. Test-only code is the one exception, and it is gated at the item level (§1.9).
- **Lambdas and match arms**, for the same reason.

An attribute on a declaration that reflection does not show, such as a function, an impl or a const, is for the compiler and for tools that read syntax: `fly`, a formatter, or a documentation generator. A library may declare one for those places, but no `comptime` code can read it until those declarations are reflected.

## 1.3 Grammar

This replaces `Layout` in §2.3 and includes the test proposal's rules unchanged:

```ebnf
Module      = [ Shebang ] { ModuleAttr } { Item } ;
Shebang     = "#!" { any character but a newline } ;   (* only at the file's first byte *)
ModuleAttr  = "@!" AttrBody ;                           (* `@` and `!` with nothing between *)
Item        = { Attr } ( Import | Reexport | ["export"] Decl ) | { Attr } Attr "{" { Item } "}" ;
Attr        = "@" AttrBody ;
AttrBody    = Ident { "." Ident } [ "(" [ AttrArg { "," AttrArg } [ "," ] ] ")" ] ;
AttrArg     = Name [ "=" Expr ] | Expr ;                (* a name alone is a flag, `name = true`; an unnamed value, *)
                                                        (* first, is the attribute's main argument (§1.4)          *)

Struct      = [ "view" ] "struct" Ident [ TypeParams ] "{" { { Attr } [ "private" ] Field | "comptime" Expr ";" } "}" ;
Enum        = [ "view" ] "enum" Ident [ TypeParams ] "{" { Attr } EnumTag { "," { Attr } EnumTag } [ "," ] "}" ;
EnumTag     = "#" Ident [ "(" Type { "," Type } ")" | "{" { Attr } Field { ( ";" | "," ) { Attr } Field } [ ";" | "," ] "}" ] ;
Interface   = "interface" Ident [ TypeParams ] [ "extends" Bounds ] "{" { { Attr } ( Sig | "type" Ident [ "extends" Bounds ] ) ";" } "}" ;
Impl        = "impl" [ TypeParams ] Type [ "for" Type ] "{" { { Attr } ["export"] Function | "type" Ident "=" Type ";" } "}"
            | "impl" Type "for" Type ";" ;
Effect      = "effect" Ident [ TypeParams ] "{" { { Attr } Op ";" } "}" ;
```

Some notes on the grammar:

- **`@!` is two tokens**, `@` and `!`, with nothing between them. The parser already tests that two punctuation tokens touch (`adjacent` in `selfhost/parse.fly`), so the lexer does not change. `@ !x` is an error.
- **The shebang** is the lexer's only new rule: `#!` at byte 0 runs to the end of the line and is skipped. `#` begins a tag anywhere else, and a tag never starts a file.
- **Module attributes come first.** An `@!` after an import or a declaration is an error that names the rule: ``a module attribute goes at the top of the file, before its imports``. Comments may come before and between module attributes.
- **A braced group** (`@only(test) { … }`) belongs to the test proposal. It is not a scope, and what it declares belongs to the module. The grammar allows a group after any attribute, but only an attribute declared to allow groups may have one (`@attribute(group)`, §1.5), and today that is `@only`.
- **No ambiguity is added.** `@` is not an operator anywhere else in the language, and attributes appear only where a declaration or member begins. Inside the parentheses, an argument is named if it begins with a name followed by `=` (not `==`), is a flag if it is a name alone, and is otherwise an unnamed expression.
- **In generated fields**, an attribute may be written inside a `comptime for` over a struct's fields. Its arguments may then use the loop's constants: `comptime for (const f of fieldsOf(T)) { @wire(rename = f.name) [f.name]: Option<f.type>; }`.

## 1.4 Arguments

An argument is `name = e` or a bare `name`. The bare form is a flag, which means `name = true` and is allowed only for a `bool` argument. Every value says what it is where it is written, a new argument never shifts the others, and the one rule covers `@layout(c)`, `@wire(skip)` and `@test(world = ADA, seeds = 50)`.

**One argument may go unnamed.** An attribute may declare a *main* argument (`@attribute(main = "when")`, §1.5), which may be written first without its name: `@only(test && !wasm)` means `@only(when = test && !wasm)`. A lone name is a flag when the attribute has a `bool` argument of that name, and is the main argument otherwise. So `@only(test)` is the condition `test`. The only attribute with a main argument today is `@only`, whose single argument is a condition, and a condition is clearer without a name.

**A value is an expression, evaluated at compile time** in the scope where the attribute is written. That is the module's scope, so the value may name the module's constants and imports. Inside a `comptime for` that generates fields, the loop's constants are in scope too. The value is checked against the declared type of the argument, as a module `const` is checked against its type, and it is then a constant: what reflection returns is that constant, not the expression.

The following are all well formed:

```ts
@layout(c, align = 16) struct Block { words: u64[8]; }
@test(world = ADA, seeds = 50) function retries(): void { … }
@wire(renameAll = #SnakeCase, denyUnknown) struct Config { … }
struct Contact { @wire(alias = ["e-mail", "mail"]) email: String; }
```

**Literal data** is the subset of values that needs no names. It is strings (not templates), integers, booleans, payload-less tags (`#SnakeCase`), and lists and records of these. Some values must be known before anything is resolved:

- an attribute that **a tool reads without compiling** (`@!script`) is limited to literal data, because `fly` reads it with the parser alone. `@attribute(literal)` marks such an attribute (§1.5);
- an attribute that decides **what is compiled** (`@only`) takes a *condition*, which reads the build's facts and nothing else (§1.9). That is the prelude type `Cond`, and only `@only` takes one. Any name, call or template inside such an attribute is an error at the value: ``an argument of `@!script` is literal data: `fly` reads it before anything is compiled``.

## 1.5 Declaring an attribute

An attribute is an ordinary struct, marked `@attribute`. Its fields are the attribute's arguments:

```ts
// std/codec.fly, sketch: how a type, a field or a tag looks on the wire, in every format.
export type Case = #CamelCase | #SnakeCase | #KebabCase | #PascalCase | #ScreamingSnakeCase;

@attribute(on = [#Struct, #Enum, #Field, #Tag])
export struct wire {
  rename: Option<str>;
  renameAll: Option<Case>;
  alias: str[];
  skip: bool;
  default: bool;
  flatten: bool;
  omitNone: bool;
  tag: Option<str>;
  content: Option<str>;
  untagged: bool;
  denyUnknown: bool;
}
```

The rules:

- **A field that is not written takes an empty value.** A `bool` is `false`, an `Option` is `#None`, and a list is empty. A field of any other type is required. So `@wire(skip)` sets one field and leaves the others empty, and no syntax for defaults is needed. An `Option<T>` argument is written as a `T`: `rename = "id"`.
- **An attribute struct exists only at compile time**, as `Type` does. Its values live only in the compiler, so it may hold `str`, `Type` and lists without being `view`. It cannot be built or named at run time.
- **`@attribute`'s own arguments** are:
  - `on`, the places it may go: `#Module`, `#Item` (any item), `#Struct`, `#Enum`, `#Field`, `#Tag`, `#Function`, `#Impl`, `#Import`, `#Member`;
  - `repeat`, which allows it more than once on one declaration;
  - `group`, which allows it before braces of items;
  - `literal`, which limits its values to literal data (§1.4);
  - `main`, the one argument that may be written first without its name (§1.4).
- **Names.** An attribute is written by the name it is imported under, `@wire(…)`, or through a module imported whole, `@codec.wire(…)`. Two libraries can both declare an attribute named `wire`, and a module that imports both uses at least one through its module's name, as it would for any other clash. Reflection finds an attribute by its declaration, never by its spelling (§1.10).
- **Attribute structs are named in lowercase**, as they are written. This is the one place a Flyscript type is named that way. It reads `@wire(skip)` rather than `@Wire(skip)`, and it matches Rust and the attributes the language already has.

**The compiler's attributes are declared in the prelude**, written the same way, so they report errors the same way and reflection shows `@layout`:

```ts
// The prelude, sketch.
// The struct is an attribute, which goes where `on` says.
@attribute(on = [#Struct], literal)
export struct attribute {
  on: Place[];
  repeat: bool;
  group: bool;
  literal: bool;
  main: Option<str>;
}

// Kept to the builds where `when` holds (§1.9).
@attribute(on = [#Module, #Item, #Import, #Member], group, main = "when")
export struct only { when: Cond; }

// Laid out as C lays it out (§8.2), or packed; `align`, a power of two.
@attribute(on = [#Struct])
export struct layout { c: bool; packed: bool; align: Option<u64>; }

// A file that is a program of its own: `fly.toml`'s tables, which `fly` reads (§1.8).
@attribute(on = [#Module], literal)
export struct script { … }
```

The compiler checks what a struct cannot express: that `@layout` names exactly one of `c` and `packed`, and that `align` is a power of two. A prelude attribute's name is reserved. A module cannot declare an attribute `test`, or import one under that name, so `@test` always means the compiler's attribute.

## 1.6 What is reported

Each of these is an error, at the attribute or argument where the problem is:

| Written | Reported |
| :--- | :--- |
| `@tset function t()` | ``no attribute `tset`; did you mean `test`?`` |
| `@Point(x = 1)` | `` `Point` is not an attribute: a struct is one when it is marked `@attribute` `` |
| `@wire(renam = "id")` | ``@wire has no argument `renam`; did you mean `rename`?`` |
| `@wire(rename)` | `` `rename` takes a value: `rename = "…"` `` |
| `@wire(skip = 1)` | `` `skip` is a `bool`, not an integer `` |
| `@wire(rename = "a") function f()` | `` @wire goes on structs, enums, fields and tags, not functions `` |
| `@wire(skip) @wire(flatten) x: T;` | `` @wire is given twice; write its arguments in one: `@wire(skip, flatten)` `` |
| `import { x } from "m"; @!script(…)` | `` a module attribute goes at the top of the file, before its imports `` |
| `@only(os == "lunix")` | `` `lunix` is not an os fly builds for: linux, macos, windows, none, wasi, browser, node `` |
| `@only(debug)` | `` `debug` is not a build fact; a condition reads test, native, freestanding, wasm, page, js, os, arch, pointerWidth `` |
| `sample()`, in code with no condition, of `@only(test) function sample()` | `` `sample` exists only in builds where `test`; this code is also in builds where it does not hold `` |

An attribute that is declared but never read is not an error, because a type may carry `@wire` long before anything encodes it. Checks of meaning that the struct's types cannot state, such as `flatten` on a field that is not a struct or `tag` together with `untagged`, are made by the code that reads the attribute when it reads it. That code reports the error at the attribute, not inside the derivation (§1.10).

A dependency's attributes are checked the same way. They are syntax and types, which a package's lock already holds to its commit.

## 1.7 The compiler's attributes

| Attribute | Goes on | Means |
| :--- | :--- | :--- |
| `@layout(c)`, `@layout(packed)`, `@layout(c, align = N)` | struct | C's layout, or packed (§8.2). Unchanged, except that it is now a general attribute and comes before `export`. |
| `@attribute(on = […], repeat, group, literal)` | struct | The struct is an attribute (§1.5). |
| `@!script(…)` | module | The file is a program of its own (§1.8). |
| `@test`, `@test(world = W, seeds = n, panics = "…")` | function | A test, in the test proposal. |
| `@only(c)`, `@only(c) { … }`, `@!only(c)` | item, import, group, member, module | Kept to the builds where `c` holds (§1.9). `@only(test)` is the test proposal's. |

Other attributes the compiler might take later, such as `@deprecated(note = "…")`, a `@caller` for panics that name the caller's line (raised in the test proposal), and `@inline`, fit the same grammar. None of them is proposed here.

## 1.8 `@!script`: a file that is its own package

A single `.fly` file run outside a package must carry `@!script(…)` and a `main`. The arguments are `fly.toml`'s tables, each written as a record with `fly.toml`'s keys:

```ts
#!/usr/bin/env fly
@!script(
  dependencies = {
    json: { git: "https://github.com/example/fly-json", version: "1.2" },
    web: { path: "../web" },
  },
)

import { parse } from "json/parse";
import { println } from "std/io";

export function main(args: readonly String[]): void uses Io {
  …
}
```

The table maps one to one onto `fly.toml`:

| `fly.toml` | `@!script` |
| :--- | :--- |
| `[package]` `name = "deploy"` `version = "0.1.0"` | `package = { name: "deploy", version: "0.1.0" }` |
| `[dependencies]` `json = { git = "…", version = "1.2" }` | `dependencies = { json: { git: "…", version: "1.2" } }` |
| `web = { path = "../web" }` | `web: { path: "../web" }` |
| a string, integer, boolean, array, inline table | a string, integer, boolean, list, record |

The exact rules:

- **The arguments are `package` and `dependencies`**, both optional, so `@!script` alone is a script with no dependencies. A script is always a program whose entry module is the file itself. `package` therefore takes only `name` and `version`, and `kind`, `entry` and `app` are errors. `name` defaults to the file's name without `.fly`. Because package names must be identifiers, so are the keys of `dependencies`.
- **Values are literal data** (§1.4). A template, a name or a call is an error, because nothing has been compiled when `fly` reads the attribute.
- **One `@!script` per file.**
- **Checking.** `fly` checks the values exactly as it checks `fly.toml`: a dependency names `git` or `path` but not both, and `version` is a requirement. The rules stay in one place. The compiler checks only that `@!script`'s arguments are `package` and `dependencies` and that they are literal data. It never needs to understand them.

**How `fly` reads it.** `fly` (`selfhost/fly.fly`) imports the compiler's parser, `./parse`, and reads the file's header: the shebang, then module attributes up to the first token that is not `@!`. It reads only the header, so an error later in the file is reported by the compiler, as usual. The header's `script` attribute becomes a `toml.Value` table, mapping strings to `#Str`, integers to `#Int`, booleans to `#Bool`, lists to `#Array` and records to `#Table`. The values TOML has and Flyscript's literal data has are the same, which is why the keys can be `fly.toml`'s exactly. `readManifest` is split so that its checks run on a table whether the table came from a file or from an attribute:

```ts
// selfhost/fly.fly, sketch.
function readManifest(dir: str): Manifest uses Io, Fail<Stop> {
  const file = join(dir, "fly.toml");
  const doc = try { parse(readText(file.asStr()).asStr()) } catch (#BadToml(line, why)) { throw #Stop(`${file}:${line}: ${why}`) };
  manifestOf(doc, dir, file.asStr())
}

// A script: its `@!script`'s tables as `fly.toml`'s, its entry the file itself.
function readScript(file: str): Manifest uses Io, Fail<Stop> {
  const header = try { parseHeader(readText(file).asStr()) } catch (d) { throw #Stop(`${file}: ${d}`) };
  const doc = match (scriptOf(header)) {
    #Some(t) => t,
    #None => throw #Stop(`${file} is not in a package; a file run on its own begins with @!script`),
  };
  let m = manifestOf(doc, parent(file).asStr(), file);
  m.entry = fileName(file).toString();
  m
}
```

**Running one.** `fly deploy.fly args…` means `fly run deploy.fly args…`, and with the shebang, `./deploy.fly args…` does the same. `fly` treats a first argument that names an existing file as a script. Inside a package's directory, a file with `@!script` still runs as a script, its own package, which ignores the `fly.toml` around it. A module of a package that carries `@!script` is an error when the package is built: ``deploy.fly is a script; a package's modules are not``.

**Its lock and its build.** A script's dependencies are held to a lock like any package's. `fly.lock`'s purpose is to hold a dependency to the commit, files and effects it was accepted with, and a script is no exception. The lock is written beside the script, as `deploy.fly.lock`, only when the script has a dependency from git. The build goes to `$FLY_HOME/scripts/<hash of the script's absolute path>/`. It is rebuilt when the script's content hash, its lock or the compiler changes, so the second run of `./deploy.fly` starts as fast as the program does.

## 1.9 Conditional compilation: `@only`

`@only(c)` keeps what follows it to the builds where the condition `c` holds. That can be a declaration, an import, a member of an impl, interface or effect, or a braced group of items, and `@!only(c)` does the same for a whole module. The test proposal's `@only(test)` is the simplest case. A condition is a boolean expression over the build's facts. It is written as Flyscript writes booleans, rather than with Rust's `any(…)`, `all(…)` and `not(…)`:

```ts
@only(test) import { assertEq } from "std/test";

@only(native && os == "linux") extern "C" function epoll_create1(flags: i32): i32;

// One `now` for each kind of target; code with no condition calls either.
@only(wasm || js) function now(): u64 { … }
@only(!(wasm || js)) function now(): u64 { … }

@only(test && !freestanding) {
  import { World } from "std/test";
  const ADA: World = World.empty().profile("ada", "Ada Lovelace");
}
```

**The facts** are a closed set, and they are fixed when the build starts:

| Fact | Type | Holds, or is |
| :--- | :--- | :--- |
| `test` | `bool` | A test build of the package being tested. A dependency is never compiled as one. |
| `native` | `bool` | A hosted native program (§8.3). |
| `freestanding` | `bool` | A kernel or firmware, with no operating system and no `main`. |
| `wasm` | `bool` | WebAssembly, for WASI or for a page. |
| `page` | `bool` | A FlyNext page's program. This implies `wasm`. |
| `js` | `bool` | JavaScript, as the compiler's own JavaScript build is. |
| `os` | `str` | `"linux"`, `"macos"` or `"windows"` natively; `"none"` freestanding; `"wasi"`; `"browser"` for a page; `"node"` for JavaScript. |
| `arch` | `str` | `"x86_64"`, `"aarch64"`, `"wasm32"` or `"js"`. |
| `pointerWidth` | `u32` | `64`; `32` for WebAssembly; `53` for JavaScript, whose integers are exact to that width (§3.1). |

Exactly one of `native`, `freestanding`, `wasm` and `js` holds.

**A condition** is made of the facts, `true` and `false`, `!`, `&&`, `||`, parentheses, and `==` or `!=` between a fact and a literal. Precedence is the language's own. Nothing else may appear, so a condition names no module, calls nothing, and reads no constant. Each fact's values are a closed set, so `os == "lunix"` is an error at the condition, a typo that Rust's cfg let through for years (§1.6).

**It is decided before names are resolved.** The facts come from the build, not from any module. The loader therefore evaluates every condition first and drops what does not hold, imports included, before it builds the import graph that §8.1 fixes before any `comptime` code runs. This is why gating is an attribute and not a `comptime if`, as the test proposal argues.

**Parsed always, checked where it holds.** Gated code is parsed in every build, so it is always well formed and its names are known. Its names, types, effects and ownership are checked only in builds where its condition holds.

**A reference needs the same condition or a stronger one.** Code under condition A may name a declaration under condition B only if A implies B, that is, if B holds in every build where A holds. Code with no condition is under `true`. The compiler decides implication exactly, by evaluating both conditions in every build it can make: each target it knows, with and without `test`. That is a few dozen assignments, so the check costs nothing, and it is made from the text, not from the build at hand. The error is therefore the same in every build: `` `sample` exists only in builds where `test`; this code is also in builds where it does not hold ``. It is never "unknown name" in one build and fine in another.

**Conditions accumulate.** An item in a group is under the group's condition and its own, joined with `&&`, and a module's `@!only` adds to everything in it. `@test` on a function implies `test`, so `@test @only(native)` is a test that runs only natively.

**Alternatives.** Two declarations of one name in one module are allowed when no build has both, which is checked the same way. A reference under A then needs A to imply at least one of them. That is how `now` above is written once for each kind of target and called by code with no condition. Each alternative is checked in its own builds.

**Exports.** A gated export is part of the package's face only in the builds where it holds. A dependent may name it only under a condition that implies it. A dependency is never built as a test, so a `test` export never reaches a dependent, and the lockfile never lists its effects.

**The same facts in code.** The facts are also the fields of the prelude's constant `build`, so `comptime if (build.pointerWidth == 64) { … }` chooses code inside a function body, where an attribute cannot go. `comptime if` can never choose an import.

`@test` and the rest of the test proposal sit inside this unchanged. `@test(world = ADA, seeds = 50, panics = "overflow")` uses `name = e`, and `ADA` is a module constant evaluated at compile time (§1.4). The proposal's grammar (`Attr = "@" Ident [ "(" [ AttrArg … ] ")" ]`, groups, attributes before `export`, unknown attributes as errors) is a subset of §1.3. A module made only of fixtures is `@!only(test)`.

## 1.10 Reading attributes

Reflection gains attributes where it already shows declarations:

```ts
// The prelude, sketch: what `Type.info` returns, with what each declaration carries.
type Field   = { name: str; type: Type; attrs: Attrs };
type TagInfo = { name: str; payload: Option<Type>; fields: Field[]; attrs: Attrs };
type TypeInfo =
  | #Int { signed: bool; bits: u8 } | #Float(u8) | #Bool | #Str | #Void | #Fn
  | #Record(Field[]) | #Tuple(Type[]) | #Union(TagInfo[])
  | #Struct { name: str; fields: Field[]; attrs: Attrs } | #Enum { name: str; tags: TagInfo[]; attrs: Attrs }
  | #Array { item: Type; len: usize } | #Slice(Type) | #Borrow { mutable: bool; type: Type }
  | #Opaque { name: str; args: Type[] };
```

- **`Attrs`** is a compile-time handle on a declaration's attributes. `attrs.get<A>()` is the `A` written there, as an `Option<A>`. `attrs.all<A>()` is every `A` written, for an attribute marked `repeat`. `attrs.fail(message)` is a compile error at the attribute, the way `comptime panic` is a compile error at the template.
- **An attribute is found by its declaration.** `f.attrs.get<wire>()` finds `std/codec`'s `wire`, however the user's module imported it, and never another library's attribute that happens to share the name.
- **Structural types carry no attributes.** A record's fields, a tuple, and a union's tags have an empty `Attrs`.
- **A tag's record payload**, written inside an enum, also gives its fields with their attributes, in the order they were declared, as `TagInfo.fields`. Through `Type.info(payload)` it is a plain record, which has no order. A tag with a payload that is not a record has no `fields`.
- **Privacy.** A private field's attributes are visible wherever the field is (§7.2).
- **What reflection does not show**, such as functions, impls and module attributes, keeps its attributes for the compiler and for tools.

A derivation reads attributes like any other constant, and checks their meaning as it does so:

```ts
// std/codec.fly, sketch. The `@wire` a field or type carries, or the empty one.
const NONE: wire = {
  rename: #None, renameAll: #None, alias: [], skip: false, default: false, flatten: false,
  omitNone: false, tag: #None, content: #None, untagged: false, denyUnknown: false,
};

comptime function attrsOf(T: Type): Attrs {
  match (Type.info(T)) {
    #Struct { attrs } | #Enum { attrs } => attrs,
    _ => Attrs.none(),
  }
}

comptime function wireOf(a: Attrs): wire {
  match (a.get<wire>()) {
    #Some(w) => w,
    #None => NONE,
  }
}

comptime function checked(f: Field): wire {
  const w = wireOf(f.attrs);
  if (w.flatten && !hasFields(f.type)) { f.attrs.fail("`flatten` is for a field whose type is a struct or record"); }
  if (w.skip && w.flatten) { f.attrs.fail("a field is skipped or flattened, not both"); }
  w
}
```

## 1.11 What was weighed

- **Macros.** Rust's derive macros and attribute macros are a second language over tokens. `comptime` already does what they do here, with types, so an attribute only has to be data.
- **Positional values** (`@rename("id")`, `@deprecated("use x")`). They are shorter, but every attribute would then need an order, and adding an argument would break what was written before. `name = value` is what `@layout(align = …)` and serde both use. The one exception, a declared main argument, exists for `@only`, whose single argument is a condition.
- **Rust's `cfg(any(…), all(…), not(…))`.** It is a second boolean syntax beside the language's own. `&&`, `||` and `!` read as every TypeScript programmer already reads them, and because a condition may contain only facts and literals, it can still be decided before anything is resolved.
- **Attributes on structural types.** Rejected because two equal types would differ by an annotation (§1.2).
- **A declaration form of its own**, `attribute wire { … }`. A struct already has fields, types and the reflection over them. One meta-attribute is a smaller addition to the language than one more kind of declaration.
- **Arguments as tokens that the reader interprets**, as in Rust. Then `@wire(renam = "x")` would be an error only if a derivation happened to read it, and nothing would type it. Typed fields catch the mistake where it is written.
- **One attribute per meaning** (`@rename`, `@skip`, `@flatten`). They collide across libraries: an ORM wants `@rename` too. One attribute per library, `@wire(…)`, is how serde, clap and sqlx do it.

---

# Part 2: Encoding

## 2.1 How JSON works today

`std/json` is a JSON codec written in Flyscript, and the compiler knows nothing about it (spec §7.5, std.md §16).

**Two interfaces.** `ToJson.toJson(self: readonly Self, out: mut String)` writes a value. `FromJson.fromJson(p: mut JsonParser): Self uses Fail<JsonError>` reads one. They are separate because a value that borrows, such as `{ status: "ok", user: req.user }`, can be encoded without being decodable, and `FromJson extends Send` means that what is decoded owns everything in it. `stringify(v)` and `parse<T>(text)` are the front doors.

**Impls written by hand** cover `String`, `Vec<T>` and `Option<T>`. An `Option` is its value or `null`. Every other type gets one **derivation** per interface, `impl<comptime T: Type> ToJson for T`. It is specialized for each type it is used at, and it branches with `comptime match (Type.info(T))`:

- numbers and booleans are written with `${self}`, and `str` by `writeString`, which copies runs between escapes whole, finding them sixteen bytes at a time with `Simd`;
- a struct or record is an object. A `comptime for` over its fields writes `writeString(f.name)`, `:`, and `self.[f.name].toJson(out)`, so the loop is unrolled into straight-line code for that type;
- tuples, arrays and slices are arrays;
- a tag without a payload is `"Name"`, and a tag with one is `{ "Name": payload }`. The `match` arms are generated, one per tag.

**Decoding** is the same shape. For a struct, the derivation builds a record type of `Option` slots, one per field (`{ comptime for (const f of fields) { [f.name]: Option<f.type>; } }`). It loops over the object's keys, matching each `key.asStr()` against arms generated from the field names, so unknown keys are skipped and keys may come in any order. It then builds the value, and a missing key is `#MissingField` unless the field is an `Option`. That last test is `isOption`, a `comptime function`. Integers of every width share one arm, which checks the range against bounds computed at compile time.

**A type asks for the derivation** with an empty impl in its own module, `impl FromJson for Signup;` (§7.3). Records, tuples and tag unions belong to no module, so they get it automatically. That is why `stringify(#Created { id: nextId, name: s.name })` in `examples/derive_json.fly` (spec A.9) needs no declaration. A derivation a struct asked for may read and build the struct's private fields.

**`JsonParser`** is a `view struct` over the text, a cursor with a pull API: `peek`, `bool`, `int`, `uint`, `float`, `string`, `beginObject`/`nextKey`/`key`, `beginArray`/`nextItem`, `skip` and `finish`. A hand-written `fromJson` reads through it, and so does the derivation. `JsonError` is `#BadJson(at) | #MissingField(name) | #UnknownTag(name) | #OutOfRange(at)`.

**`tests/run/json.fly` is a different thing.** It tests `examples/json.fly` (spec A.1), a dynamic JSON tree, `Json`, parsed into a region and matched by hand. That is the "value" approach, with no derivation at all. It shows that a region-allocated `Value` needs nothing from the codec.

## 2.2 What it lacks

- **The wire format is the declaration.** A Flyscript field is `userName` and an API's key is `user_name`, and nothing can say so. Nor can a field be skipped, defaulted or flattened, a `#None` be left out instead of written as `null`, an unknown key be refused, or an enum be tagged in any way but `{ "Name": payload }`.
- **Each format derives itself.** A TOML or CBOR package would write its own `impl<comptime T: Type> ToToml for T`, repeating the walk over `Type.info`, and would have to re-implement every attribute above to match JSON.
- **Each type asks for each format**, `impl ToJson for User; impl ToToml for User; …`.
- **A hand-written encoding is written once per format.** A `Uuid` that is a string in every format needs an impl for each.
- **The orphan rule makes that impossible across packages.** An impl lives with its interface or with its type. A `uuid` package cannot implement a `cbor` package's interface without depending on it, and `cbor` cannot implement it for `Uuid` without depending on `uuid`. This is the problem serde's data model exists to solve.
- **Keys cost at run time** even though they are known when the program is compiled. The encoder escapes each field name with `writeString` on every value it writes. The decoder makes a `String` of every key it reads (`p.key()`) before matching it.

## 2.3 Two designs

**Per-format derivations**, today's approach: each format has its own `ToX`/`FromX` and its own derivation over `Type.info`.

**One data model**, serde's approach: the type side implements `Encode`/`Decode` once, against an `Encoder`/`Decoder` interface. Each format implements that interface once.

| | Per-format derivations | One data model |
| :--- | :--- | :--- |
| **Work, for M types and N formats** | M·N comptime specializations: each format's derivation runs once for each type. | M per direction: the derivation runs once for each type, and is then an ordinary generic over the encoder, monomorphized per format without running `comptime` again. |
| **Code size** | One straight-line encoder per (type, format). | The same after monomorphization. Every call through `E extends Encoder` is static and inlined, so the machine code matches what a hand-written per-format encoder would be. |
| **Attributes** | Each format interprets `rename`, `flatten` and tagging itself, and may disagree with the others. | Interpreted once, in the derivation. A format never sees an attribute. |
| **Hand-written impls** | One per (type, format). | One per type: `impl Encode for Uuid` serves every format. |
| **Across packages** | Impossible for a third party's type and a third party's format. | Both depend only on `std/codec`. |
| **What a format can do** | Anything, because it sees the type. | What the data model expresses. A format that needs more, such as TOML putting tables after scalars, builds a tree inside its encoder. |
| **Effects** | Each format declares its own. | Each `Encoder` declares its own, as a row (`Encoder<[Io]>`). `Encode.encode` carries that row through, so encoding to a `String` stays pure. |
| **Ownership** | `readonly Self` in, owned out. | The same, and a decoder lends what it reads (`string(): str from self`), so a key is matched where it lies and a value is copied only into the field that keeps it. |

Two features of Flyscript change the usual trade-off.

**Reflection replaces visitors.** serde's `Deserialize` is a visitor. The format drives decoding and calls `visit_map`, `visit_str` and so on, and a proc macro generates the visitor, a `__Field` enum for the keys and a visitor for that enum too. Rust needs this because a derive macro sees only tokens. In Fly, the derivation sees the type's whole shape at compile time, so the type can drive: it asks for a struct, receives keys as indexes into names it already knows, and decodes each field by its type. Decoding is a *pull* API, the same one `JsonParser` has today, and no visitor trait is needed. The one case where a format must say what comes next, an untagged enum or a dynamic `Value`, is a single method, `kind()` (§2.4).

**Names are compile-time constants.** serde passes field names to the format as `&'static str`, and `serde_json` escapes them again for every value. Here a name is a `comptime` parameter of the encoder's method, so a format may do its work on the name in the compiler. JSON pushes the literal `"user_name":`, escaped once. On the decoding side, the decoder is handed the list of keys at compile time and returns an index, so JSON can compare the key's bytes in place against constants with no `String` at all, and a future version could compile them into a perfect hash.

**Effects as the data model** were considered and rejected. An `Encode` could perform `Emit` operations that a format's handler interprets, and that would be very Flyscript. But a handler is reached dynamically, at the cost of a call per scalar that a monomorphized interface does not pay, and an encoder has nothing to suspend. Interfaces, monomorphized, are the zero-cost form. Effects remain the right tool at the edges: an encoder that writes to a file has `Io` in its row, and a decoder over JSON Lines can be a generator, `uses Yield<T>`.

**Recommendation: one data model**, `std/codec`, with the type side generated by `comptime` over reflection and attributes, and the format side made of interfaces whose names are compile-time constants. It keeps today's speed and today's output, and it adds attributes and third-party formats.

## 2.4 `std/codec`

A sketch of the whole interface:

```ts
// std/codec.fly, sketch. What a type is on the wire, in any format.

// A value, written.
export interface Encode {
  function encode<row E, C extends Encoder<E>>(self: readonly Self, out: mut C): void uses ...E;
}

// A value, read; it owns all it holds.
export interface Decode extends Send {
  function decode<row E, D extends Decoder<E>>(d: mut D): Self uses ...E;
}

// A format's writer. `E` is what it performs: `[]` for one into a `String`, `[Io]` for one into
// a file, with its own failures, such as a TOML writer's for a value TOML cannot hold.
export interface Encoder<row E = []> {
  function bool(self: mut Self, v: bool): void uses ...E;
  function int(self: mut Self, v: i64): void uses ...E;
  function uint(self: mut Self, v: u64): void uses ...E;
  function float(self: mut Self, v: f64): void uses ...E;
  function string(self: mut Self, v: str): void uses ...E;
  function bytes(self: mut Self, v: readonly u8[]): void uses ...E;
  function none(self: mut Self): void uses ...E;
  // Whether `none` can be written where a field is; TOML has no null, so a `#None` field is left out.
  function writesNull(self: readonly Self): bool;

  // A list of `len` items, each after `item()`.
  function beginSeq(self: mut Self, len: usize): void uses ...E;
  function item(self: mut Self): void uses ...E;
  function endSeq(self: mut Self): void uses ...E;

  // A map of `len` entries, each after `entry()`: a key's value, then the value's.
  function beginMap(self: mut Self, len: usize): void uses ...E;
  function entry(self: mut Self): void uses ...E;
  function endMap(self: mut Self): void uses ...E;

  // A struct or record of `len` fields, each after `field(key)`, the keys known at compile time.
  function beginStruct(self: mut Self, comptime name: str, len: usize): void uses ...E;
  function field(self: mut Self, comptime key: str): void uses ...E;
  function endStruct(self: mut Self): void uses ...E;

  // A tag, the `index`th of its type's, named `name`; one with a payload is followed by it and
  // then `endVariant()`.
  function unitVariant(self: mut Self, comptime index: u32, comptime name: str): void uses ...E;
  function beginVariant(self: mut Self, comptime index: u32, comptime name: str): void uses ...E;
  function endVariant(self: mut Self): void uses ...E;
}

export type Next = #Field(usize) | #Unknown | #End;
export type Kind = #Null | #Bool | #Int | #Float | #Str | #Bytes | #Seq | #Map | #Unknown;

// A format's reader, pulled by the type being read.
export interface Decoder<row E = []> {
  type Mark extends Copy;

  function bool(self: mut Self): bool uses ...E;
  function int(self: mut Self): i64 uses ...E;
  function uint(self: mut Self): u64 uses ...E;
  function float(self: mut Self): f64 uses ...E;
  // Lent: the text itself where it needs no unescaping, or the decoder's buffer.
  function string(self: mut Self): str from self uses ...E;
  function bytes(self: mut Self): readonly u8[] from self uses ...E;
  // Consumes a null if one is next.
  function isNone(self: mut Self): bool uses ...E;
  // What comes next, for a format that says; `#Unknown` for one that does not.
  function kind(self: mut Self): Kind uses ...E;
  function skip(self: mut Self): void uses ...E;

  function beginSeq(self: mut Self): void uses ...E;
  function nextItem(self: mut Self): bool uses ...E;
  function beginMap(self: mut Self): void uses ...E;
  function nextEntry(self: mut Self): bool uses ...E;
  // The next field, as its index among `keys`, which are known at compile time.
  function beginStruct(self: mut Self, comptime name: str, comptime keys: str[]): void uses ...E;
  function nextField(self: mut Self, comptime keys: str[]): Next uses ...E;
  // A tag, as its index among `names`, and whether a payload follows; `endVariant()` after one.
  function beginVariant(self: mut Self, comptime names: str[]): [usize, bool] uses ...E;
  function endVariant(self: mut Self): void uses ...E;

  // What the derivation finds wrong, failed by the format, so the failure says where.
  function missing(self: mut Self, comptime key: str): never uses ...E;
  function unknownField(self: mut Self): never uses ...E;
  function outOfRange(self: mut Self): never uses ...E;

  // Where the decoder is, and a way back there: for an untagged enum, which tries each tag.
  function mark(self: readonly Self): Self.Mark;
  function rewind(self: mut Self, m: Self.Mark): void uses ...E;
}
```

**The interfaces' rules:**

- **Effects.** An `Encoder<E>` or `Decoder<E>` names its whole row, failures included: JSON's is `[Fail<JsonError>]`, and a CBOR reader over a socket has `[Io, Fail<CborError>]`. `Encode.encode` and `Decode.decode` perform exactly that row, nothing more. A derived `encode` adds no effect of its own, so `stringify` stays pure (law 2).
- **Failures belong to the format.** When a field is missing, the derivation calls `d.missing("email")`, and the format fails with its own error. JSON's is `#MissingField("email")`, as now, and it can report where in the text. So the codec defines no error type, and `JsonError` keeps its tags.
- **Ownership.** `encode` borrows `readonly`, so a value that borrows can be encoded. `Decode extends Send`, as `FromJson` does. Strings are lent out of the decoder with `from self` and are copied only when a `String` field keeps them. Because a lent `str` is second-class, nothing can hold one past the next call to the decoder.
- **Lengths are given up front.** A definite-length format (CBOR, MessagePack) writes the length first. The derivation knows it at compile time, less the `#None` fields it leaves out, which it counts first.
- **`kind()` and `mark()`/`rewind()`** serve the self-describing cases: an untagged enum and a dynamic `Value`. A format that is not self-describing (postcard, bincode) answers `#Unknown`, and its `rewind` fails. That is a decoding failure for an untagged type, which such formats cannot represent anyway. JSON's mark is a byte offset, so trying the tags of an untagged enum in turn allocates nothing, where serde buffers the input into a `Content` tree.

**Impls written by hand** cover what reflection does not show: `String`, `Vec<T>`, `Option<T>`, `HashMap<K, V>` (a map) and `Box<T>` (its contents). Every other type gets the derivation. A type that knows its own encoding writes it once, for every format:

```ts
// In uuid's own package, sketch: a string in JSON, TOML and CBOR alike.
impl Encode for Uuid {
  function encode<row E, C extends Encoder<E>>(self: readonly Self, out: mut C): void uses ...E {
    out.string(self.text().asStr());
  }
}
```

**The derivation** has one arm per kind of type, as JSON's does today. Its struct arm, with the attributes that act there, is a sketch:

```ts
// std/codec.fly, sketch: structs and records.
impl<comptime T: Type> Encode for T {
  function encode<row E, C extends Encoder<E>>(self: readonly Self, out: mut C): void uses ...E {
    comptime match (Type.info(T)) {
      #Record(_) | #Struct { fields: _ } => {
        // How many fields are written: known at compile time, less the `#None`s left out.
        const len = present(self, out);
        out.beginStruct(comptime Type.name(T), len);
        encodeFields(self, mut out);
        out.endStruct();
      }
      // … numbers, strings, tuples, arrays; tags by how the enum is tagged
      _ => comptime panic(`${Type.name(T)} cannot be encoded`),
    }
  }
}

// What a field is on the wire, decided at compile time from its type and its `@wire`.
type Role = #Skip | #Flatten | #Optional(bool) | #Plain;

comptime function roleOf(f: Field): Role {
  const w = checked(f);
  if (w.skip) { #Skip } else if (w.flatten) { #Flatten } else if (isOption(f.type)) { #Optional(w.omitNone) } else { #Plain }
}

// Writes the fields of a struct or record as the keys of the object being written: renamed,
// the skipped left out, a `#None` left out where it is not written as null, and a flattened
// field's own fields in its place.
function encodeFields<comptime T: Type, row E, C extends Encoder<E>>(v: readonly T, out: mut C): void uses ...E {
  comptime for (const f of fieldsOf(T)) {
    comptime match (roleOf(f)) {
      #Skip => {}
      #Flatten => { encodeFields(v.[f.name], mut out); }
      #Optional(omit) => {
        if (const #Some(x) = v.[f.name]) {
          out.field(comptime keyOf(T, f));
          x.encode(mut out);
        } else if (!omit && out.writesNull()) {
          out.field(comptime keyOf(T, f));
          out.none();
        }
      }
      #Plain => {
        out.field(comptime keyOf(T, f));
        v.[f.name].encode(mut out);
      }
    }
  }
}

// A field's key: its `rename`, or its name recased as its type's `renameAll` says.
comptime function keyOf(T: Type, f: Field): str {
  match (checked(f).rename) {
    #Some(k) => k,
    #None => match (wireOf(attrsOf(T)).renameAll) {
      #Some(c) => recase(f.name, c),
      #None => f.name,
    },
  }
}
```

Decoding a struct is today's decoder with three changes. Keys are matched by index. Missing fields consult `@wire`. A flattened field's fields have slots of their own in the same record, and the field's value is built from them:

```ts
// std/codec.fly, sketch: `Decode`'s derivation, at structs and records.
impl<comptime T: Type> Decode for T {
  function decode<row E, D extends Decoder<E>>(d: mut D): T uses ...E {
    comptime match (Type.info(T)) {
      #Record(fields) | #Struct { fields } => {
        let slots: { comptime for (const f of fields) { [f.name]: Option<f.type>; } } =
          { comptime for (const f of fields) { [f.name]: #None, } };
        d.beginStruct(comptime Type.name(T), comptime keysOf(T));
        while (true) {
          match (d.nextField(comptime keysOf(T))) {
            // One arm for each key a field is read from: its own, then its aliases.
            comptime for (const k of keyTable(T)) {
              #Field(comptime k.index) => { slots.[k.field] = #Some(k.type.decode(mut d)); },
            }
            #Unknown => { comptime if (wireOf(attrsOf(T)).denyUnknown) { d.unknownField(); } else { d.skip(); } }
            #End => { break; }
          }
        }
        {
          comptime for (const f of fields) {
            [f.name]: match (slots.[f.name]) {
              #Some(v) => v,
              #None => comptime match (ifMissing(T, f)) {
                #Default => f.type.default(),
                #Absent => #None,
                #Required => d.missing(comptime keyOf(T, f)),
              },
            },
          }
        }
      }
      // … numbers, strings, tuples, arrays; tags by how the enum is tagged
      _ => comptime panic(`${Type.name(T)} cannot be decoded`),
    }
  }
}
```

**Compile time.** The comptime work for a type runs once per direction, whatever the number of formats. `keyOf`, `keyTable` and `roleOf` are evaluated once per field. The interpreter's memo of specializations (§7.1) already makes the struct arm's work proportional to the number of fields.

## 2.5 `@wire`

| Argument | On | Encoding | Decoding |
| :--- | :--- | :--- | :--- |
| `rename = "k"` | field, tag | The key or tag name is `k`. | Read from `k`. |
| `renameAll = #SnakeCase` (`#CamelCase`, `#KebabCase`, `#PascalCase`, `#ScreamingSnakeCase`) | struct, enum | Every field's key, or every tag's name, recased at compile time. A field's own `rename` wins. | The same. |
| `alias = ["a", "b"]` | field | — | Also read from `a` and `b`. |
| `skip` | field | Left out. | Not read; its type's `Default`. |
| `default` | field | — | A missing field is its type's `Default`. |
| `default` | struct | — | A missing field is that field of the struct's own `Default`, as in serde (`port: 8080` comes from `impl Default for Config`). |
| `flatten` | field of a struct or record type | Its fields are written as the outer object's. | Read from the outer object. No buffering, because every key is known at compile time. |
| `omitNone` | `Option` field, or struct (every `Option` field) | `#None` is left out instead of `null`. | Unchanged: missing or `null` is `#None`. |
| `denyUnknown` | struct | — | An unknown key fails (`d.unknownField()`) instead of being skipped. |
| (none) | enum | External: `"Name"`, or `{ "Name": payload }`, as now. | The same. |
| `tag = "type"` | enum | Internal: `{ "type": "Name", …payload's fields }`. Each tag's payload must be a struct or record, which is checked at compile time. | The tag is read wherever it falls among the keys. Every tag's fields are known at compile time, so they share one set of slots and the tag is matched at the end. If two tags share a key with different types, the decoder falls back to `mark`/`rewind`. |
| `tag = "t", content = "c"` | enum | Adjacent: `{ "t": "Name", "c": payload }`. | The same. |
| `untagged` | enum | The payload alone. | Each tag in order, from a mark; the first that decodes wins. |

`Option` is `null` by default, which is today's behaviour and TypeScript's `T | null`. `omitNone` gives TypeScript's optional property, `x?: T`. Decoding accepts both either way, as `parse` does now. A format without null, such as TOML, leaves a `#None` field out whatever the attribute says (`writesNull()`).

Structural types get the defaults and nothing else (§1.2). An API whose tags need names of their own declares an enum:

```ts
// Sketch: what `@wire` looks like at the declaration.
import { wire, Encode, Decode } from "std/codec";

@wire(renameAll = #SnakeCase, denyUnknown)
struct Signup {
  email: String;
  @wire(rename = "name") displayName: String;
  @wire(omitNone) referrer: Option<String>;
  @wire(alias = ["utm"]) campaign: Option<String>;
  @wire(skip) private seen: u64;
}
impl Encode for Signup;
impl Decode for Signup;

@wire(tag = "type", renameAll = #SnakeCase)
enum Shape {
  #Circle { radius: f64 },
  @wire(rename = "rect") #Rectangle { @wire(rename = "w") width: f64; @wire(rename = "h") height: f64 },
}
impl Encode for Shape;
impl Decode for Shape;
```

`{"email":"a@b.c","name":"Ada","utm":"x"}` decodes as a `Signup`, with `campaign` as `#Some("x")`, `referrer` as `#None` and `seen` as `0`. `{"email":"a@b.c","name":"Ada","seen":3}` is an error under `denyUnknown`: a skipped field is not read from the wire, so `"seen"` is an unknown key. A `Shape` that is `#Rectangle { width: 2, height: 3 }` encodes as `{"type":"rect","w":2,"h":3}`, and a `#Circle` as `{"type":"circle","radius":…}`.

**What reflection must give** (§1.10), all of it new:

1. `attrs` on `Field`, `TagInfo`, `#Struct` and `#Enum`, with `Attrs.get<A>()`, `all<A>()` and `fail(message)`.
2. `TagInfo.fields`: a tag's record payload with its fields' attributes, in declaration order.
3. An attribute found by its declaration, never by its name.
4. Attribute values as comptime constants, including `str` and lists of `str`, usable at run time as literals: `out.field(comptime keyOf(T, f))`.
5. A `comptime function` that returns a `str` it built (`recase`). Comptime strings belong to the compiler, and as literals they last as long as the program.
6. `comptime` value parameters on interface methods (`field(self, comptime key: str)`), each impl's method specialized per value as a template is. The grammar has them (`Param = [ "comptime" ] Ident ":" …`), but nothing in the standard library uses one yet.
7. `Default`, a derived prelude interface, for `skip` and `default`: zero, `false`, empty, `#None`, and fieldwise for records and structs that ask (`impl Default for Config;`).

## 2.6 A format of one's own

A format package depends on `std/codec` alone, and every type that asks for `Encode`/`Decode` works with it, including types from packages it has never seen.

**JSON**, as `std/json` would be:

```ts
// std/json.fly, sketch: the writer.
export struct JsonWriter { out: String; first: bool; }

impl Encoder for JsonWriter {
  function beginStruct(self: mut Self, comptime name: str, len: usize): void {
    self.out.push("{");
    self.first = true;
  }
  function field(self: mut Self, comptime key: str): void {
    if (!self.first) { self.out.push(","); }
    self.first = false;
    // `"user_name":`, escaped once, by the compiler.
    self.out.push(comptime quoted(key));
  }
  function endStruct(self: mut Self): void {
    self.out.push("}");
    self.first = false;
  }
  function writesNull(self: readonly Self): bool { true }
  …
}

export function stringify<T extends Encode>(v: readonly T): String {
  let w = JsonWriter { out: String.new(), first: true };
  v.encode(mut w);
  w.out
}
```

```ts
// std/json.fly, sketch: the reader matches a key where it lies in the text.
impl Decoder<[Fail<JsonError>]> for JsonParser {
  function nextField(self: mut Self, comptime keys: str[]): Next uses Fail<JsonError> {
    if (!self.nextKey()) { return #End; }
    const k = self.rawKey();
    comptime for (const [i, key] of keys.enumerate()) {
      if (k == key) { return #Field(i); }
    }
    #Unknown
  }
  function missing(self: mut Self, comptime key: str): never uses Fail<JsonError> {
    throw #MissingField(key.toString())
  }
  …
}
```

`rawKey` lends the key's bytes from the text when the key has no escapes, and decodes it into the parser's buffer otherwise. Either way it allocates no `String`. `parse<T extends Decode>(text)`, `stringify<T extends Encode>(v)` and `JsonError` keep their names and behaviour, and `JsonParser` keeps its methods, so a hand-written reader still works. `ToJson`/`FromJson` become `Encode`/`Decode`: `impl FromJson for Signup;` becomes `impl Decode for Signup;`. The output for every type without `@wire` is byte for byte what it is now, so spec A.9, `examples/derive_json.fly` and their tests change only their imports.

**TOML** is the hard case, and it shows where a format does the work the data model leaves to it. A TOML document is a table, and its nested tables come after its scalar keys, as `[a.b]` sections. The writer therefore builds a tree and prints it at the end:

```ts
// toml/encode.fly, in a package of its own, sketch.
import { Encoder, Encode } from "std/codec";

export type TomlError = #NotATable | #NullInArray | #MixedArray;

export struct TomlWriter { stack: Vec<Value>; keys: Vec<String>; }

impl Encoder<[Fail<TomlError>]> for TomlWriter {
  function field(self: mut Self, comptime key: str): void uses Fail<TomlError> {
    self.keys.push(key.toString());
  }
  function none(self: mut Self): void uses Fail<TomlError> { throw #NullInArray }
  function writesNull(self: readonly Self): bool { false }
  …
}

export function toToml<T extends Encode>(v: readonly T): String uses Fail<TomlError> {
  let w = TomlWriter { stack: Vec.new(), keys: Vec.new() };
  v.encode(mut w);
  w.finish()
}
```

`writesNull` is `false`, so the derivation leaves `#None` fields out and `none()` is reached only for a `#None` inside a list, which TOML cannot hold. A top-level value that is not a struct fails with `#NotATable`. The TOML package declares no attribute of its own, and `renameAll = #KebabCase` on a config struct is the same `@wire` that JSON obeys.

**CBOR** is the easy case: a binary format, self-describing, with definite lengths. `beginStruct(name, len)` writes major type 5 with `len`, `field(key)` writes the key's text string, which the compiler can encode in full (`comptime cborText(key)` is its header byte and bytes), `bytes()` is major type 2, and the `Decoder`'s `kind()` reads the next item's major type. `Mark` is an offset into the input, as it is for JSON.

A format may also declare attributes for itself, read the same way. For example, a CBOR package could take `@cbor(keyAsInt = 3)` on a field, for COSE's integer keys, through a method of its own that the derivation does not call. Whether the codec should give formats a place for such attributes is an open question below.

## 2.7 Where it would be built

To give the reviewer a sense of size, not as a plan to follow:

- **Parsing** (`selfhost/parse.fly`, `src/syntax/parser.rs`, both lexers): `layout()` becomes `attrs()`, which every item and member carries; the shebang; `@!` at the top; and `parseHeader`, exported for `fly`. `StructDecl.layout`/`align` become the `@layout` attribute read by the checker.
- **Checking** (`env.fly`/`env.rs`): attribute names are resolved like other names, arguments are checked against the attribute's struct and evaluated by the comptime interpreter, and places are checked. `@only` is acted on before resolution.
- **Reflection** (`comptime.fly`/`comptime.rs`): `attrs`, `TagInfo.fields`, `Attrs`, and `comptime` value parameters on methods.
- **`fly`**: `readScript`, `manifestOf`, running a file by its path, the script lock and the script cache.
- **`std/codec`** (new) and **`std/json`** on it, with `Default` in the prelude.

It would be two roadmap steps, attributes and `@!script` first, then the codec, after the import change, whose spelling the examples here would then use.

## Open questions

1. **Lowercase attribute structs** (`struct wire`) or a declaration of their own (`attribute wire { … }`)? This proposal takes the struct, because it adds nothing new to the language, at the cost of the one lowercase type name.
2. **Names at compile time or `dyn`.** A `comptime key` parameter makes `Encoder` a template interface, so `dyn Encoder` is impossible, and with it erased-serde's single copy of each type's encoder for all formats. That copy matters for a page's WebAssembly size. Should the codec also offer a `DynEncoder` with names passed at run time, for code size over speed?
3. **Zero-copy decoding.** serde's `'de` lets a `&str` field borrow the input. In Fly, that would be a `view struct` decoded with `parse<T>(text): T from text`, which `Decode extends Send` forbids today. Is that worth a second interface, `DecodeIn`, whose result is tied to the decoder?
4. **`default = e` per field**, a value instead of the type's `Default`. Functions are not compile-time values, so `e` would be an expression spliced where the field is built. That is a quotation, which this proposal avoids. Is the struct-level `@wire(default)` with `impl Default` enough?
5. **A format's view of a type**: a `Duration` as `"1.5s"` in JSON but as nanoseconds in CBOR (serde's `is_human_readable`). Is this a method of `Encoder` that hand-written impls consult, or do formats get attributes of their own (`@cbor(…)`) that the derivation passes through?
6. **The script lock**: `deploy.fly.lock` beside the script, as proposed, or inside the cache, out of sight but lost when the script is copied? And should a script run by its shebang be allowed without `.fly` (`/usr/local/bin/deploy`)?
7. **`fly add` for a script**, which would rewrite `@!script`'s text the way it now appends to `fly.toml`. Should it, or should a script's dependencies be edited by hand?
8. **More build facts.** Should `fly.toml` grow features (Cargo's), read as `features.tls`? Should there be a `debug` fact for a build with assertions or sanitizers? And should alternatives (`@only(wasm) function now` and `@only(!wasm) function now`) be required to have one signature, so that a library's face is the same on every target?
9. **The lockfile and target-gated exports.** Test-only exports never appear in the lock. Should an export that exists only on some targets be listed with its condition, or should the lock list only what every target exports?
10. **Attributes in template structs**: should `Partial<T>` be able to copy each field's attributes (`@...f.attrs [f.name]: Option<f.type>;`), so that a partial update decodes under the same keys as the whole?
