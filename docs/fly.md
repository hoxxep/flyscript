# fly

`fly` builds, runs and tests a Flyscript package, fetches what it depends on, and holds every dependency to what it was when you accepted it: the same commit, the same files, and no more power than it had. A package's types already say what each of its functions performs; its lockfile writes that down, and a build refuses an update that asks for more.

```sh
fly new hello                 # a package: fly.toml, main.fly and a test, in hello/
cd hello
fly run                       # built natively and run
fly test                      # every program in tests/, held to its `// expect:` lines
fly add json https://github.com/example/fly-json   # a dependency, at its newest version
fly update                    # every dependency moved to the newest version it allows
fly accept json               # what json performs now, accepted
```

`fly` in the repository's root is the command. Put that directory on `PATH` and it works anywhere: the first time, and whenever the compiler's source changes, it builds itself and the native compiler into `target/fly`.

## The manifest: `fly.toml`

```toml
[package]
name = "hello"
version = "0.1.0"
kind = "bin"            # bin (the default), lib or site
entry = "main.fly"      # a program's entry module; main.fly unless it says otherwise

[dependencies]
json = { git = "https://github.com/example/fly-json", version = "1.2" }
web = { path = "../web" }
```

- **A program** (`bin`) is its entry module's `main`. `fly build` compiles it natively, through LLVM on every core if LLVM is there (`LLVM_BIN`, or Homebrew's), else through C, to `target/<name>`; `fly run` builds it and runs it in the process's place, with the arguments after `run`.
- **A library** (`lib`) is its modules. `fly build` checks every one of them, the types, the effects and ownership, and holds its own dependencies to its lock.
- **A site** (`site`) is a FlyNext app in the directory `app` names (`app` unless it says otherwise): `fly build` makes its server and its pages' program in `target/site`, which `target/site/server 3000 target/site` serves.

A dependency is a git repository and a version requirement, or a directory. Its modules are imported by its name: `import { parse } from "json/parse"` is `parse.fly` in the package `json`, wherever `fly` keeps it. A dependency may have a `fly.toml` of its own, whose dependencies are the build's too; two packages of one name must be one package.

A version is a tag of the repository, `v1.2.3` or `1.2.3`, in semantic versioning. A requirement is written as Cargo writes one: `1.2` allows `1.2.0` and every later `1.x`, `0.3` every `0.3.x`, `~1.2` every `1.2.x`, `=1.2.3` that one alone, `>=1.2` anything from it on, and `*` anything. A pre-release, `1.3.0-rc.1`, is had only by asking for it exactly.

## The lockfile: `fly.lock`

`fly` writes `fly.lock` beside the manifest. Commit it: it is what makes a build the same wherever it is made.

```toml
[[package]]
name = "json"
version = "1.2.0"
git = "https://github.com/example/fly-json"
commit = "dd1483f3f025fffda528903fba142288b36d1fbe"
hash = "sha256-c0eb3b39939c65c97f2a97bfa2307a1d30ac6d8aa3ae72620ab90b0a1b156ac7"
unsafe = false
effects = [
  "parse report: Io",
  "parse size:",
]
```

- **The commit** is the one the version's tag named when it was locked. A build fetches that commit, never the tag again, so a tag moved later changes nothing.
- **The hash** is SHA-256 of the package's files, each one's path and bytes in the order of their paths. A build checks the files it has against it, so a package changed after it was fetched — in the cache, or by a repository rewritten under the same commit name — stops the build.
- **The effects** are each exported function's, a method by its type, with the effects its type declares, from the modules of the package the program uses: `parse size:` is pure, `parse report: Io` performs `Io`. **`unsafe`** says whether a module of the package vouches for code the compiler cannot check: an `unsafe` block or an `extern` function.

Two builds from one lockfile are the same, byte for byte: the same sources at the same commits, compiled by the same compiler.

## Holding a dependency to what it was

When a dependency changes — `fly update` moved it to a newer version, or its lock entry was edited — the build compares what it performs now with what the lock accepted. If any exported function performs `Io` or `Unsafe` where it did not, a function that is new among them, or a module now vouches for unchecked code, the build stops and says where:

```
error: a dependency's update asks for more than it had:
  json 1.1.0 performs what the version accepted did not:
    parse report now performs Io
Read what changed; to accept it, `fly accept name`.
```

and it stays stopped until `fly accept json` records what the dependency performs now. A JSON parser that starts reaching the network, or a date library that starts calling C, is a change a person reads before a build trusts it: what it may do is in its types, and the lockfile holds it to them. Any other change — a function gone, one made pure, an effect of the package's own — the lock records as it is.

A dependency first added is accepted as it is: adding it was the decision. A dependency by path is part of the work at hand, and is held to nothing.

## Where things are

- `FLY_ROOT`, which the launcher sets, is the installation: `std/`, `selfhost/`, `web/` and the native compiler, `target/fly/flyc`.
- `FLY_HOME`, `~/.fly` unless it says otherwise, keeps every commit fetched, in `packages/<name>-<commit>`, without its history.
- The compiler learns where each package is from `FLY_PACKAGES`, which `fly` sets: `name=dir` pairs between `:`s (spec §8.1). A package the build does not name is the installation's, beside `std`.
