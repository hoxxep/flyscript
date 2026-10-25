# Packages, dotted imports and single-file programs — a design

A proposal, for review, to replace TypeScript's `import { a } from "path"` with imports that name a package and a path through it, `import std.io.println;`; to make a package's targets follow from its files; and to let one `.fly` file outside any package be a program of its own, declared so at its top. Nothing here is built yet. The text it would put in the specification (§2.1, §2.3, §8.1) and in [fly.md](../fly.md) is at the end.

The attribute this relies on, `@!script(…)`, is designed with every other attribute in the attribute and serialization design; tests written beside the code, `@test`, are designed in `2026-10-25-unit-tests-design.md`. This document uses `@!script` and says what it must hold, not how attributes are parsed.

## Why

Flyscript already knows exactly what a package is: a directory with a `fly.toml`, named by the manifest, whose dependencies the manifest names and the lock holds (fly.md). Its imports do not say so. A string path is either relative to the file (`"../modules/geometry/point"`) or begins with a package's name (`"web/ui"`), and the two look alike; a relative path can climb out of the package into any directory beside it, and the repository does this, from `tests/run` into `examples/` and from `web/` into `selfhost/`. A dotted import names the package it reaches every time, and a package's own modules are reached through `self`, so where a module comes from is in its first word.

The other half is the program of one file. Python and JavaScript let any file run, and what it imports is whatever the directories around it hold: `sys.path`, the nearest `node_modules`. Here a file outside a package runs only if it says it is a program, with the dependencies it needs at its top, and it imports nothing beside it. A program of more than one file is a package.

## Imports

An import names a path of segments, separated by `.`. The first is a package — `std`, a dependency's name, an installation's package — or `self`, this package's root, or `super`, the module above this one. Each segment after it is a module or a name a module exports; the syntax does not say which, and the compiler finds out.

```fly
import std.io.println;                          // one name
import std.collections.{ HashMap, HashSet };    // several, from one module
import std.json.{ stringify, parse as parseJson };
import self.geometry.point.{ Point, origin };   // this package's own modules
import super.shape.area;                        // a module beside this one
import std.io;                                  // a module, whose names are then io.println, io.File
import json;                                    // a package, by its root
```

A path ends either at a segment, which is bound under its own name or the one `as` gives it, or at `.{ … }`, a list of segments each bound so. A module bound this way is a namespace: `io.println(s)` calls the function `println` of `std/io`, `io.File` is its type, and `json.parse.Error` reaches through the module `parse` of the package `json`. A module is not a value: it cannot be passed, stored or returned, and a name bound to one may only be followed by `.` and a name it has. A local binding of the same name hides it, as it would hide any import.

**What a module's names are.** A module's names are its exports and its submodules: the module `a/b.fly` has the names `a/b.fly` exports and a name for each module in the directory `a/b/`. This is already how the repository lays modules out (`tests/modules/geometry.fly` beside `tests/modules/geometry/point.fly`). A name that is both — `b.fly` exports `c` and `b/c.fly` exists — is an error where a path goes through it, saying both; `fly build` of a library checks every module for it, so a package never ships one.

**A package's root.** `import json` binds the root of the package `json`: the exports of its `lib.fly`, if it has one, and a name for each module at its top. A package without a `lib.fly` has the second alone, which is what `std` is. A program's entry module, `main.fly` or one a manifest names, is not one of the root's names: nothing imports an entry.

**`self` and `super`.** `self` is the root of the package the importing module belongs to, as Rust's `crate` is; `super` is the module above the importing one, and `super.super` the one above that. `self.geometry.point` is `geometry/point.fly` of this package wherever the importing module is in it; `super.shape`, written in `geometry/point.fly`, is `geometry/shape.fly`. `self` is also the name of a method's receiver, and in an import it is only the first segment; in a body, a package's own modules are reached through names imported from them. A module is the same module however it is reached, as now (§8.1): `self.parse` in the package `json` and `json.parse` in an app that depends on it are one module.

A program of one file (below) belongs to no package. It can import neither `self` nor `super`.

**Names that are not identifiers.** A segment is an identifier, a reserved word, or a name between backticks, which is the text between them exactly: `` `[id]` ``, `` `$routeid` ``, `` `{-$lang}` ``, `` `404` `` and `` `${id}` `` are file names, braces and all, and nothing in them is interpolated, since a path is fixed before anything runs. `` \` ``, `\\` and `\$` are its escapes, the last needed only before an unbalanced `{`. A segment that is a reserved word or between backticks has no name of its own to bind, so it is imported `as` one:

```fly
import self.app.routes.todos.`[id]` as TodoRoute;
import self.app.routes.{ `$routeid` as Route, `404` as NotFound };
import self.types.`type` as typeModule;
```

Neither lexer needs to change for this. Both keep a template's span, the Rust lexer an `Expr(Span)` for each `${…}` and Flyscript's by scanning to its closing brace, so the parser takes a segment's text from the source between the backticks.

**Re-exports.** `export import` makes what it imports exports of the module, so a package presents one public face over the files behind it:

```fly
export import self.geometry.point.{ Point, origin as zero };
export import self.geometry.shape;
```

Unlike today's `export { … } from`, the names are bound in the module too, as Rust's `pub use` binds them: the statement says `import`, and reading it otherwise would be a trap. `tests/reject/reexport_binds_nothing.fly`, which uses a name it re-exports and expects `unknown name`, becomes a program the checker accepts. A module still exports a name once.

**No globs.** There is no `import a.b.*`. Every name a module uses is named where it is imported, or reached through a namespace it imported.

**The import graph.** An import depends on the module its path ends in, or, when it ends at a name, the module that exports it — not on each module along the way. `import self.geometry.point.Point` depends on `geometry/point.fly`, not on the package's `lib.fly`, so a package's root may re-export its modules and its modules may import each other through `self` without a cycle. A namespace's uses are dependencies too: `io.println` depends on `std/io`, `json.parse.Error` on `json/parse.fly`. The loader finds them in the syntax, as chains of `.` that begin with a name bound to a module, before anything is checked; a chain whose head turns out to be a local, hiding the import, only loads a module that was not needed. The graph must still be acyclic (§8.1).

## Packages

A package's name is an identifier, and is the name its modules are imported by: a repository called `fly-json` is a package called `fly_json` or `json`, as its manifest says. Unlike Cargo, which lets a manifest say `fly-json` and code say `fly_json`, there is one spelling. `fly add` takes the name it is given, or derives one from the repository's (`fly-json` → `fly_json`), and refuses one that is not an identifier, is reserved, or is `self`, `super` or `std`.

**Targets follow from files.** `kind` goes. What a package builds is what it has:

- `lib.fly`: it is a library, whose root is that module's exports and its top-level modules. `fly build` checks every module, as for `kind = "lib"` now.
- `main.fly`: it is a program, entered at that module's `main`. It reaches the package's other modules through `self`, as any of them would; it does not import its own package by name, as a Rust binary must its library, because the unit here is the module, not the crate.
- Both: both. A package may be a library and a program at once.
- `[[bin]] name = "…", entry = "…"`: another program, as Cargo's `src/bin/` are. `fly build` makes each, `target/<name>`.
- `[site]`, with `app = "app"` unless it says otherwise: a FlyNext site, built as `kind = "site"` is now. A site stays declared: its build is a pipeline of its own (`app/.flynext/server.fly`, `FLY_OVERLAY`), and a library with a directory called `app` is not one.

`entry` goes with `kind`: `selfhost/fly.toml`'s `entry = "main.fly"` is the default it no longer needs, and `examples/todo/fly.toml`'s `kind = "site"` becomes `[site]`.

**How the compiler learns of packages.** Both compilers take `--package name=dir`, once for each package, as rustc takes `--extern`, in place of `FLY_PACKAGES`. `fly` passes one for every package of the build: each dependency, the package being built, and the installation's — `std`, `web`, and the compiler's own, `selfhost/`, whose manifest names it `flyc`. A module belongs to the package whose directory holds it, the deepest if several do, and that is the package its `self` names. A compiler run with no `--package` knows the installation's packages from where it is installed, as it finds `std` now.

`check_files`, which the Rust test harness calls on every core at once in one process, takes the map as an argument: an environment variable is the whole process's, the same for every check running beside it. The harness names the packages the test programs import: `examples` (`examples/`), `flyc` (`selfhost/`), `web` and `tests` (`tests/`). `tests/run/http_server.fly`'s `import { serve } from "../../examples/server";` becomes `import examples.server.serve;`, and `tests/reject/reexport_twice.fly`'s `"../modules/geometry/point"` becomes `self.modules.geometry.point`, `tests` being its package. These programs are compiled one by one on purpose, as rustc's `tests/ui` are, each run by every implementation and each rejection on its own; they need no manifest, since they are not run by `fly`.

## Programs of one file

A `.fly` file outside a package is a program if it says so at its top, with the module attribute `@!script`, and exports a `main`:

```fly
#!/usr/bin/env fly
@!script(dependencies = {
  json: { git: "https://github.com/example/fly-json", version: "1.2" },
})

import json.parse.{ parse };
import std.io.println;

export function main(text: str): void uses Io {
  println(`${parse(text)}`);
}
```

- **`@!script(…)`** holds what a manifest's `[dependencies]` does, under the same keys and with the same meanings: a git repository and a version requirement, or a path. A program with no dependencies says `@!script` alone. Its exact syntax is the attribute design's; what is fixed here is that `fly` reads it with the compiler's own parser, which `fly` is written beside, so a key it does not know is an error at that key, and the compiler never needs to understand it.
- **The shebang** is optional and only for the shell: both lexers skip a first line that begins `#!`, as JavaScript's do. What makes the file a program is `@!script`, not the line above it, whose path differs from machine to machine and which Windows ignores.
- **It imports nothing beside it.** Such a program is a package of one module: it reaches `std`, the installation's packages and what `@!script` declares, and no file in its directory. More than one file is a package.

**Running it.** `fly file.fly args…` builds the program and runs it in the process's place, as `fly run` does a package's. A first argument that ends in `.fly` or holds a `/` is a file, since `fly`'s commands are words; `#!/usr/bin/env fly` then makes `./file.fly args…` work on Linux and macOS without `env -S`. `fly run` keeps meaning the package's program, and passes on every argument after it: a package's program may well take a `.fly` file, as the compiler does.

`fly` refuses a file that is not its package's entry and has no `@!script`:

```
error: tools/gen.fly is not a program: it is in no package, and does not say `@!script` at its top.
To run it on its own, begin it with `@!script`; to make it a program of its package, name it in fly.toml's [[bin]].
```

and one with `@!script` but no exported `main`. A file with `@!script` inside a package's directory is still a program of its own, reaching none of the package's modules: it said so.

**Its lock.** A program of one file has no lockfile unless it asks for one, as uv does for a script. `fly lock file.fly` writes `file.fly.lock` beside it, in the format of `fly.lock`; once that file is there, every run uses it and holds each dependency to it, refusing an update that asks for more, as a package's build does, and `fly accept name file.fly` accepts one. `--locked` refuses to run without a lock, or with one the declared dependencies no longer agree with. Without a lock, each git dependency is resolved to the newest version it allows, from `FLY_HOME`'s cache when it is there, and `fly` says once, on standard error, that what it performs is not held:

```
note: json is not locked, so nothing holds it to what it performs; `fly lock gen.fly` locks it.
```

A program that depends only on `std` and the installation's packages has nothing to lock.

## What changes, and in what order

Each step leaves every test green on every back end.

1. **Both forms, in both parsers.** The Rust parser (`src/syntax/parser.rs`) and Flyscript's (`selfhost/parse.fly`) accept dotted imports, `export import`, backtick segments, `self` and `super`, beside the string form, and both loaders resolve them (`src/check/env.rs`, around `package_file`; `selfhost/env.fly`, around `isRelative`). A string import is translated, as it is parsed, into the path it means, so the checker sees one form. `--package` and `check_files`'s map come with it. Namespace imports are a step of their own, 5.
2. **The seed.** `selfhost/bootstrap.sh --update-seed`, so `selfhost/seed.js` parses what the compiler's own source is about to be written in.
3. **Every import rewritten.** A script turns the 616 imports in 331 files — 167 of them relative — into the dotted form; `../`-paths that leave a package become the package's name. By hand: what generates imports — `web/flynext.fly`'s route and layout imports (``self.app.routes.todos.`[id]` ``), `web/flyx.fly`'s prelude (`import web.ui.{ el as __fx_el, … };`) and its `../selfhost/diag`, `fly new`'s templates in `selfhost/fly.fly` — and every example in spec.md, std.md and fly.md.
4. **The string form gone**, from both parsers and the grammar.
5. **Namespace imports**: `import std.io;` and `io.println`, with the loader's scan for the modules a namespace reaches.
6. **`fly`.** Targets from files, `[[bin]]` and `[site]`; `--package` in place of `FLY_PACKAGES`; `fly file.fly`; `@!script`, once the attribute design lands; the shebang in both lexers; `fly lock`, `file.fly.lock` and `--locked`.

Steps 1 to 4 are the change of syntax and can land together; 5 and 6 each stand alone. The proof (`proof/`) is untouched: λ-fly has no modules.

## Open questions

- **Casing.** The design does not depend on it: a path is resolved by looking names up, whatever their case. Whether the compiler should insist on a casing — packages and modules `snake_case`, types, interfaces and effects `UpperCamel` — is a separate decision, and so is whether functions stay `camelCase`, as the library and TypeScript have them, or become `snake_case`, as Rust's are.
- **Modules a package keeps to itself.** Every module of a package is importable by its dependents, as with string paths now; only exports are reached. A module attribute such as `@!internal` could keep a module to its own package.
- **A version of `fly`.** Neither a manifest nor `@!script` can say which compiler it needs. A `fly = "0.140"` key in both would.
- **The goal of a TypeScript surface.** Goal 1 (§1) says a TypeScript programmer can read Flyscript on day one. Dotted imports read easily, but they are not TypeScript's, and the specification should say that this departure is chosen, and why: a package is a thing the language knows.

## The text for the specification

**§2.1**, the row for `import` / `export`:

| TypeScript | Flyscript | Notes |
| :--- | :--- | :--- |
| `import { a, b as c } from "m"` | `import pkg.m.{ a, b as c };` | A path names a package (`std`, a dependency, `self`) and the modules through it (§8.1); the import graph must be acyclic. |
| `import * as m from "m"` | `import pkg.m;` | A module bound as a namespace: `m.f()`, `m.T`. |
| `export { a } from "m"` | `export import pkg.m.a;` | |

**§2.3**, in place of `Module`, `Import`, `Reexport` and `ImportName`:

```ebnf
Module      = { ModuleAttr } { Import | ["export"] Decl } ;   (* after a first line beginning "#!", if any *)
Import      = ["export"] "import" Path [ "as" Ident ] ";"
            | ["export"] "import" Path "." "{" ImportName { "," ImportName } [ "," ] "}" ";" ;
Path        = Head { "." Segment } ;
Head        = "self" | "super" { "." "super" } | Segment ;
Segment     = Ident | Keyword | Quoted ;
Quoted      = "`" { character but "`" and "\" | "\`" | "\\" | "\$" } "`" ;
ImportName  = Segment [ "as" Ident ] ;       (* a Keyword or Quoted segment must be renamed *)
```

**§8.1**, in place of its first two paragraphs:

> Each `.fly` file is a module. Declarations are private unless exported. A module-level `const` is evaluated at compile time (`const MAX_BUF: usize = 512;`).
>
> An import names a path: a package, then the modules and names through it, each segment a module or a name its module has. A module's names are its exports and its submodules, the modules in the directory of its name (`a/b/` for `a/b.fly`); a name that is both is an error. The first segment is `std`, the standard library; a package the build names, which `fly` does for each dependency a manifest declares, as [fly.md](fly.md) says; one of the installation's, such as `web`; `self`, the root of the importing module's package; or `super`, the module above it. A package's root has the exports of its `lib.fly` and its top-level modules. `import web.ui.{ el, text };` binds two names of `web/ui.fly`; `import std.io;` binds the module, whose names are reached through it, `io.println(s)`. A segment that is not an identifier is written between backticks, taken exactly (`` import self.app.routes.todos.`[id]` as Todo; ``), and imported `as` a name. `export import` makes what it imports exports of the module, and binds them in it too, so a package presents one public face over the files behind it; a module exports a name once. A module is the same module however it is reached. The import graph — each import depending on the module its path ends in or the module that exports its name — must be acyclic, so modules compile in parallel in dependency order.

**fly.md**: the manifest's `kind` and `entry` give way to `lib.fly`, `main.fly`, `[[bin]]` and `[site]`; `import { parse } from "json/parse"` becomes `import json.parse.parse;`; a section on programs of one file — `@!script`, the shebang, `fly file.fly`, `fly lock` and `file.fly.lock`; and, under "Where things are", `--package` in place of `FLY_PACKAGES`.
