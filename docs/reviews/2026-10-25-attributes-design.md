# Attributes and conditional compilation — a design

A proposal, for review, to make attributes general. Flyscript has one attribute today. `@layout(c)` and `@layout(c, align = N)` are written before `struct`, and both parsers handle them as a special case (`layout()` in `selfhost/parse.fly` and in `src/syntax/parser.rs`). Three designs now need more:

- the packages and imports design (`2026-10-25-packages-and-imports-design.md`) lets a single file declare what it depends on with `@!script(…)`;
- the unit tests design (`2026-10-25-unit-tests-design.md`) marks tests with `@test` and keeps test-only code to test builds;
- the codec design (`2026-10-25-codec-design.md`) needs to be told, at the declaration, that a field is called `user_name` on the wire.

This design covers where an attribute may go, what its arguments are, how a library declares one, and what is reported. It also gives the exact form of `@!script` and conditional compilation, `@only(c)`. Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

Examples use today's imports, `import { x } from "m"`. Under the packages and imports design they are spelled `import std.codec.{ wire, Encode }`, and nothing else changes. Wherever a feature already exists, the code parses today once its attributes are removed.

## The design in brief

1. **An attribute is data attached to a declaration.** `@name(…)` holds a compile-time constant for the declaration that follows it. It runs nothing and rewrites nothing. The compiler reads its own attributes, and any other is read by `comptime` code through reflection. Attributes are never macros.
2. **One grammar:** `@name`, `@name(flag)`, `@name(key = e, …)` and `@a.b(…)` for a namespaced one. A bare name is a flag (`key = true`). A value is an expression evaluated at compile time. An attribute may declare one *main* argument, written first without its name, with every other argument named after it: `@only(test && !wasm)`, `@deprecated("use parseAll", since = "0.140")`.
3. **They go on declarations and their members:** items and imports, struct fields, enum tags and the fields of a tag's record, functions in impls and interfaces, and effect operations. They do not go on expressions, statements, parameters or structural types. `@!name(…)` goes on the module, at the top of the file.
4. **A library declares an attribute as a struct**, marked `@attribute(on = […])`. Its fields are the attribute's arguments, and it is imported and namespaced like any other name. The compiler's own attributes are declared the same way, in the prelude.
5. **An attribute that is not declared is an error**, and so is an argument the attribute lacks, a value of the wrong type, or an attribute in a place it does not allow.
6. **Conditional compilation is `@only(c)`.** `c` is a boolean expression (`!`, `&&`, `||`, `==`, `!=`) over the build's facts, which are Rust's cfg facts under Rust's names and values: `target.os`, `target.arch`, `target.family`, `target.env`, `target.endian`, `target.pointerWidth`, and `test`. It is decided before names are resolved. Code may name what is gated only under a condition that implies the gate, and that is checked across every build, so the error is the same in every build.
7. **`@!script(dependencies = {…})`** takes `fly.toml`'s tables with `fly.toml`'s keys, written as Flyscript records of literal data. `fly` reads it with the compiler's parser before anything is compiled, and the compiler checks only its shape.

## 1. What an attribute is

An attribute is a value the compiler holds for a declaration. Nothing happens because an attribute is there. What it means is decided by whatever reads it. The compiler reads its own attributes, which are `@layout`, `@attribute`, `@!script` and the unit tests design's `@test` and `@only`, and a library's derivation reads the library's attributes through `Type.info`.

That is law 5 applied to annotations. Rust's attributes are token trees, and a procedural macro turns them into code. Flyscript already generates code with `comptime`, so an attribute only has to be data that a derivation can see: typed, checked where it is written, and read as a constant. No macro system is needed, and no second language runs inside the compiler.

## 2. Where attributes go

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

Attributes come **before `export`**: `@layout(c) export struct Pair`. That puts every attribute in the same place, and it is the order the unit tests design already chose. The parser today accepts `@layout` only after `export`, but nothing in the repository exports a struct with a layout, so the order can change now.

Four places are left out on purpose.

- **Structural types.** Records, tuples and tag unions are structural. `{ id: u64 }` written in two modules is the same type, and a type alias is only another name for it. An attribute on a structural type would make two equal types different, or would be lost when the alias expands. A type that needs a wire format of its own is declared as a struct or enum, which has a name to carry the attribute. A tag's record payload in an enum is the one exception, because it is written inside a nominal declaration. Its attributes belong to the enum, and reflection gives them to the tag (section 10).
- **Parameters.** No attribute needs one yet, and functions are not reflected (`#Fn` carries nothing), so a library could not read it. The parser reserves the position: `@` before a parameter is an error that says parameters take no attributes yet.
- **Statements and expressions.** Code is chosen with `comptime if`. Test-only code is the one exception, and it is gated at the item level (section 9).
- **Lambdas and match arms**, for the same reason.

An attribute on a declaration that reflection does not show, such as a function, an impl or a const, is for the compiler and for tools that read syntax: `fly`, a formatter, or a documentation generator. A library may declare one for those places, but no `comptime` code can read it until those declarations are reflected.

## 3. Grammar

This replaces `Layout` in §2.3 and includes the unit tests design's rules unchanged:

```ebnf
Module      = [ Shebang ] { ModuleAttr } { Item } ;
Shebang     = "#!" { any character but a newline } ;   (* only at the file's first byte *)
ModuleAttr  = "@!" AttrBody ;                           (* `@` and `!` with nothing between *)
Item        = { Attr } ( Import | Reexport | ["export"] Decl ) | { Attr } Attr "{" { Item } "}" ;
Attr        = "@" AttrBody ;
AttrBody    = Ident { "." Ident } [ "(" [ AttrArg { "," AttrArg } [ "," ] ] ")" ] ;
AttrArg     = Name [ "=" Expr ] | Expr ;                (* a name alone is a flag, `name = true`; an unnamed value, *)
                                                        (* first, is the attribute's main argument (section 4)          *)

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
- **A braced group** (`@only(test) { … }`) belongs to the unit tests design. It is not a scope, and what it declares belongs to the module. The grammar allows a group after any attribute, but only an attribute declared to allow groups may have one (`@attribute(group)`, section 5), and today that is `@only`.
- **No ambiguity is added.** `@` is not an operator anywhere else in the language, and attributes appear only where a declaration or member begins. Inside the parentheses, an argument is named if it begins with a name followed by `=` (not `==`), is a flag if it is a name alone, and is otherwise an unnamed expression.
- **In generated fields**, an attribute may be written inside a `comptime for` over a struct's fields. Its arguments may then use the loop's constants: `comptime for (const f of fieldsOf(T)) { @wire(rename = f.name) [f.name]: Option<f.type>; }`.

## 4. Arguments

An argument is `name = e` or a bare `name`. The bare form is a flag, which means `name = true` and is allowed only for a `bool` argument. Every value says what it is where it is written, a new argument never shifts the others, and the one rule covers `@layout(c)`, `@wire(skip)` and `@test(world = ADA, seeds = 50)`.

**One argument may go unnamed.** An attribute may declare a *main* argument (`@attribute(main = "when")`, section 5), which may be written first without its name: `@only(test && !wasm)` means `@only(when = test && !wasm)`. Every other argument stays named and optional as usual, and comes after it:

```ts
@deprecated("use parseAll", since = "0.140") function parse(text: str): Doc { … }
@deprecated(since = "0.140") function parseOld(text: str): Doc { … }
@deprecated function parseOlder(text: str): Doc { … }
```

The rules (`@deprecated` is only an illustration here; it is not proposed):

- **Only the first argument may go unnamed.** A second unnamed value is an error: `` only the first argument goes without its name; write `since = "0.140"` ``.
- **The main argument is optional only if its field is.** `@deprecated(since = …)` and a bare `@deprecated` leave `note: Option<str>` empty. `@only`'s `when` is required, so a bare `@only` is an error: ``@only needs a condition: `@only(test)` ``.
- **It may also be named:** `@only(when = test)`. Writing it both ways in one attribute is an error.
- **A lone name is a flag when the attribute has a `bool` argument of that name, and the main argument otherwise.** So `@only(test)` is the condition `test`, because `only` has no `bool` field called `test`. The question is settled by the attribute's declaration, never by what the name means in the module.

Only `@only` has a main argument today. Its single argument is a condition, and a condition reads better without a name.

**A value is an expression, evaluated at compile time** in the scope where the attribute is written. That is the module's scope, so the value may name the module's constants and imports. Inside a `comptime for` that generates fields, the loop's constants are in scope too. The value is checked against the declared type of the argument, as a module `const` is checked against its type, and it is then a constant: what reflection returns is that constant, not the expression.

The following are all well formed:

```ts
@layout(c, align = 16) struct Block { words: u64[8]; }
@test(world = ADA, seeds = 50) function retries(): void { … }
@wire(renameAll = #SnakeCase, denyUnknown) struct Config { … }
struct Contact { @wire(alias = ["e-mail", "mail"]) email: String; }
```

**Literal data** is the subset of values that needs no names. It is strings (not templates), integers, booleans, payload-less tags (`#SnakeCase`), and lists and records of these. Some values must be known before anything is resolved:

- an attribute that **a tool reads without compiling** (`@!script`) is limited to literal data, because `fly` reads it with the parser alone. `@attribute(literal)` marks such an attribute (section 5);
- an attribute that decides **what is compiled** (`@only`) takes a *condition*, which reads the build's facts and nothing else (section 9). That is the prelude type `Cond`, and only `@only` takes one. Any name, call or template inside such an attribute is an error at the value: ``an argument of `@!script` is literal data: `fly` reads it before anything is compiled``.

## 5. Declaring an attribute

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
  - `literal`, which limits its values to literal data (section 4);
  - `main`, the one argument that may be written first without its name, before the named ones (section 4).
- **Names.** An attribute is written by the name it is imported under, `@wire(…)`, or through a module imported whole, `@codec.wire(…)`. Two libraries can both declare an attribute named `wire`, and a module that imports both uses at least one through its module's name, as it would for any other clash. Reflection finds an attribute by its declaration, never by its spelling (section 10).
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

// Kept to the builds where `when` holds (section 9).
@attribute(on = [#Module, #Item, #Import, #Member], group, main = "when")
export struct only { when: Cond; }

// Laid out as C lays it out (§8.2), or packed; `align`, a power of two.
@attribute(on = [#Struct])
export struct layout { c: bool; packed: bool; align: Option<u64>; }

// A file that is a program of its own: `fly.toml`'s tables, which `fly` reads (section 8).
@attribute(on = [#Module], literal)
export struct script { … }
```

The compiler checks what a struct cannot express: that `@layout` names exactly one of `c` and `packed`, and that `align` is a power of two. A prelude attribute's name is reserved. A module cannot declare an attribute `test`, or import one under that name, so `@test` always means the compiler's attribute.

## 6. What is reported

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
| `@only(target.os == "lunix")` | `` `lunix` is not a `target.os`; did you mean `linux`? `` |
| `@only(debug)` | `` `debug` is not a build fact; a condition reads `test`, `page` and `target`'s `arch`, `os`, `family`, `env`, `endian` and `pointerWidth` `` |
| `sample()`, in code with no condition, of `@only(test) function sample()` | `` `sample` exists only in builds where `test`; this code is also in builds where it does not hold `` |

An attribute that is declared but never read is not an error, because a type may carry `@wire` long before anything encodes it. Checks of meaning that the struct's types cannot state, such as `flatten` on a field that is not a struct or `tag` together with `untagged`, are made by the code that reads the attribute when it reads it. That code reports the error at the attribute, not inside the derivation (section 10).

A dependency's attributes are checked the same way. They are syntax and types, which a package's lock already holds to its commit.

## 7. The compiler's attributes

| Attribute | Goes on | Means |
| :--- | :--- | :--- |
| `@layout(c)`, `@layout(packed)`, `@layout(c, align = N)` | struct | C's layout, or packed (§8.2). Unchanged, except that it is now a general attribute and comes before `export`. |
| `@attribute(on = […], repeat, group, literal)` | struct | The struct is an attribute (section 5). |
| `@!script(…)` | module | The file is a program of its own (section 8). |
| `@test`, `@test(world = W, seeds = n, panics = "…")` | function | A test, in the unit tests design. |
| `@only(c)`, `@only(c) { … }`, `@!only(c)` | item, import, group, member, module | Kept to the builds where `c` holds (section 9). `@only(test)` is the unit tests design's. |

Other attributes the compiler might take later, such as `@deprecated(note = "…")`, a `@caller` for panics that name the caller's line (raised in the unit tests design), and `@inline`, fit the same grammar. None of them is proposed here.

## 8. `@!script`: a file that is its own package

The packages and imports design decides that a `.fly` file outside a package is a program only if it says `@!script` at its top and exports a `main`. It also settles how such a file is run (`fly file.fly`, or the shebang) and locked (`fly lock file.fly`, which writes `file.fly.lock`). This section settles the attribute's syntax: its arguments are `fly.toml`'s tables, each written as a record with `fly.toml`'s keys.

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
| `[dependencies]` `json = { git = "…", version = "1.2" }` | `dependencies = { json: { git: "…", version: "1.2" } }` |
| `web = { path = "../web" }` | `web: { path: "../web" }` |
| a string, integer, boolean, array, inline table | a string, integer, boolean, list, record |

The exact rules:

- **An argument is a table of `fly.toml`'s, under the same name, if that table means something for a single file.** Today that is `dependencies` alone, and it is optional, so `@!script` by itself is a program with no dependencies. `[package]` does not apply: the program's name is the file's, and its targets are the file itself. A key `fly.toml` gains later that applies to one file, such as the `fly = "0.140"` the packages and imports design raises, joins `@!script` under the same name. Because package names are identifiers, so are the keys of `dependencies`.
- **Values are literal data** (section 4). A template, a name or a call is an error, because nothing has been compiled when `fly` reads the attribute.
- **One `@!script` per file.**
- **Checking.** `fly` checks the values exactly as it checks `fly.toml`: a dependency names `git` or `path` but not both, and `version` is a requirement. The rules stay in one place, and a key `fly` does not know is an error at that key. The compiler checks only that `@!script`'s arguments are literal data. It never needs to understand them.

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
  // One program, the file itself, its dependencies checked as a manifest's are.
  manifestOf(doc, parent(file).asStr(), file)
}
```

**Running and locking** are as the packages and imports design says. This design adds one error: a module that carries `@!script` and is also imported by a package's modules is reported when the package is built, as ``deploy.fly is a program of its own; a package's modules do not import it``.

## 9. Conditional compilation: `@only`

`@only(c)` keeps what follows it to the builds where the condition `c` holds. That can be a declaration, an import, a member of an impl, interface or effect, or a braced group of items, and `@!only(c)` does the same for a whole module. The unit tests design's `@only(test)` is the simplest case. A condition is a boolean expression over the build's facts. Its facts are Rust's `cfg` facts, with Rust's values, read as fields: `target.os` is Rust's `target_os`. It is written as Flyscript writes booleans, rather than with `cfg`'s `any(…)`, `all(…)` and `not(…)`:

```ts
@only(test) import { assertEq } from "std/test";

@only(target.os == "linux") extern "C" function epoll_create1(flags: i32): i32;

// One `now` for the web and JavaScript, one for everything else; code with no condition calls either.
@only(target.family == "wasm" || target.family == "js") function now(): u64 { … }
@only(target.family != "wasm" && target.family != "js") function now(): u64 { … }

@only(test && target.os != "none") {
  import { World } from "std/test";
  const ADA: World = World.empty().profile("ada", "Ada Lovelace");
}
```

**The facts** are fixed when the build starts:

| Fact | Rust's | Type | Values |
| :--- | :--- | :--- | :--- |
| `test` | `test` | `bool` | Whether this is a test build of the package being tested. A dependency is never compiled as one. |
| `target.arch` | `target_arch` | `str` | `"x86_64"`, `"aarch64"`, `"wasm32"`; `"js"` for JavaScript. |
| `target.os` | `target_os` | `str` | `"linux"`, `"macos"`; `"none"` freestanding (§8.3); `"wasi"`; `"node"` for JavaScript. |
| `target.family` | `target_family` | `str` | `"unix"` on Linux and macOS, `"wasm"` for WebAssembly, `"js"` for JavaScript, and `""` freestanding, where Rust sets none. |
| `target.env` | `target_env` | `str` | `"gnu"` or `"musl"`, the C library linked on Linux; otherwise `""`. |
| `target.endian` | `target_endian` | `str` | `"little"` on every target Fly has. |
| `target.pointerWidth` | `target_pointer_width` | `u32` | `64`; `32` for WebAssembly; `53` for JavaScript, whose integers are exact to that width (§3.1). Rust writes it as a string, but Flyscript can compare a number. |
| `page` | — | `bool` | Whether this is a FlyNext page's program (§8.3): `wasi` code that a page's host runs and splits into routes. Rust has no fact for this. |

Names are Flyscript's, so Rust's `target_pointer_width` is `target.pointerWidth`, and the values are Rust's strings. `"js"`, `"node"` and `page` are Flyscript's own, for the targets Rust does not have. Rust's shorthands `unix` and `windows` are not copied, because `target.family == "unix"` says the same thing.

**A condition** is made of the facts, `true` and `false`, `!`, `&&`, `||`, parentheses, and `==` or `!=` between a fact and a literal. Precedence is the language's own. Nothing else may appear, so a condition names no module, calls nothing, and reads no constant. A string fact may be compared only with a value Rust's `cfg` knows for that fact, or with Flyscript's own values for the targets above. So `target.os == "freebsd"` is allowed, and is false on every target Fly builds today, while `target.os == "lunix"` is an error at the condition, as Rust's `check-cfg` makes it (section 6).

**It is decided before names are resolved.** The facts come from the build, not from any module. The loader therefore evaluates every condition first and drops what does not hold, imports included, before it builds the import graph that §8.1 fixes before any `comptime` code runs. This is why gating is an attribute and not a `comptime if`, as the unit tests design argues.

**Parsed always, checked where it holds.** Gated code is parsed in every build, so it is always well formed and its names are known. Its names, types, effects and ownership are checked only in builds where its condition holds.

**A reference needs the same condition or a stronger one.** Code under condition A may name a declaration under condition B only if A implies B, that is, if B holds in every build where A holds. Code with no condition is under `true`. The compiler decides implication exactly, by evaluating both conditions in every build it can make: each target it knows, with and without `test`. That is a few dozen assignments, so the check costs nothing, and it is made from the text, not from the build at hand. The error is therefore the same in every build: `` `sample` exists only in builds where `test`; this code is also in builds where it does not hold ``. It is never "unknown name" in one build and fine in another.

**Conditions accumulate.** An item in a group is under the group's condition and its own, joined with `&&`, and a module's `@!only` adds to everything in it. `@test` on a function implies `test`, so `@test @only(target.os == "linux")` is a test that runs only on Linux.

**Alternatives.** Two declarations of one name in one module are allowed when no build has both, which is checked the same way. A reference under A then needs A to imply at least one of them. That is how `now` above is written once for each kind of target and called by code with no condition. Each alternative is checked in its own builds.

**Exports.** A gated export is part of the package's face only in the builds where it holds. A dependent may name it only under a condition that implies it. A dependency is never built as a test, so a `test` export never reaches a dependent, and the lockfile never lists its effects.

**The same facts in code.** The facts are the fields of the prelude's constant `build`. A condition is evaluated with `build`'s fields in scope, so `target.os` in a condition is `build.target.os` in code, and `comptime if (build.target.pointerWidth == 64) { … }` chooses code inside a function body, where an attribute cannot go. `comptime if` can never choose an import.

`@test` and the rest of the unit tests design sit inside this unchanged. `@test(world = ADA, seeds = 50, panics = "overflow")` uses `name = e`, and `ADA` is a module constant evaluated at compile time (section 4). That design's grammar (`Attr = "@" Ident [ "(" [ AttrArg … ] ")" ]`, groups, attributes before `export`, unknown attributes as errors) is a subset of section 3. A module made only of fixtures is `@!only(test)`.

## 10. Reading attributes

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

## 11. What was weighed

- **Macros.** Rust's derive macros and attribute macros are a second language over tokens. `comptime` already does what they do here, with types, so an attribute only has to be data.
- **Positional values** (`@rename("id")`, `@deprecated("use x")`). They are shorter, but every attribute would then need an order, and adding an argument would break what was written before. `name = value` is what `@layout(align = …)` and serde both use. The one exception, a declared main argument, exists for `@only`, whose single argument is a condition.
- **Rust's `cfg(any(…), all(…), not(…))`.** It is a second boolean syntax beside the language's own. `&&`, `||` and `!` read as every TypeScript programmer already reads them, and because a condition may contain only facts and literals, it can still be decided before anything is resolved.
- **Attributes on structural types.** Rejected because two equal types would differ by an annotation (section 2).
- **A declaration form of its own**, `attribute wire { … }`. A struct already has fields, types and the reflection over them. One meta-attribute is a smaller addition to the language than one more kind of declaration.
- **Arguments as tokens that the reader interprets**, as in Rust. Then `@wire(renam = "x")` would be an error only if a derivation happened to read it, and nothing would type it. Typed fields catch the mistake where it is written.
- **One attribute per meaning** (`@rename`, `@skip`, `@flatten`). They collide across libraries: an ORM wants `@rename` too. One attribute per library, `@wire(…)`, is how serde, clap and sqlx do it.


## 12. Where it would be built

To give the reviewer a sense of size, not as a plan to follow:

- **Parsing** (`selfhost/parse.fly`, `src/syntax/parser.rs`, both lexers): `layout()` becomes `attrs()`, which every item and member carries. The parsers also gain the shebang, `@!` at the top, groups, and `parseHeader`, which is exported for `fly`. `StructDecl.layout`/`align` become the `@layout` attribute, which the checker reads.
- **Loading** (`env.fly`/`env.rs`): conditions are evaluated before resolution, and what does not hold is dropped. The implication check runs over every build, and alternatives are checked for disjointness.
- **Checking**: attribute names are resolved like other names, arguments are checked against the attribute's struct and evaluated by the comptime interpreter, and places are checked.
- **Reflection** (`comptime.fly`/`comptime.rs`): `attrs`, `TagInfo.fields`, `Attrs`, and the prelude's `build`.
- **`fly`**: `readScript` and `manifestOf`. Running and locking come with the packages and imports design.

It is one roadmap step, after the import change, whose spelling the examples would then use. The unit tests design and the codec design build on it.

## Open questions

1. **Lowercase attribute structs** (`struct wire`) or a declaration of their own (`attribute wire { … }`)? This design takes the struct, because it adds nothing new to the language, at the cost of the one lowercase type name.
2. **More of Rust's facts.**
   - Rust's `debug_assertions`, as `debugAssertions`, for a build with assertions or sanitizers.
   - `target.vendor`.
   - `panic`, because a freestanding program's panics do not unwind (§8.3).
   - Features, once `fly.toml` has them. Rust's `feature = "tls"` is a membership test. A condition cannot call `includes`, so features would be a record of flags: `feature.tls`.
3. **`page`** is Flyscript's own fact. Should it stay, or should it become a feature that FlyNext sets?
4. **Alternatives' signatures.** Should `@only(target.family == "wasm") function now` and its alternative be required to have one signature, so that a library's face is the same on every target?
5. **The lockfile and target-gated exports.** Test-only exports never appear in the lock. Should an export that exists only on some targets be listed with its condition, or should the lock list only what every target exports?
6. **`fly add` for a script**, which would rewrite `@!script`'s text the way it now appends to `fly.toml`. Should it, or should a script's dependencies be edited by hand?
7. **Attributes in template structs**: should `Partial<T>` be able to copy each field's attributes (`@...f.attrs [f.name]: Option<f.type>;`), so that a partial update decodes under the same keys as the whole?
