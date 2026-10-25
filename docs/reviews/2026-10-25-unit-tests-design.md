# Tests in a package: `@test`, `@only(test)` and one program of them all — a proposal

A Flyscript package is tested today by the programs in its `tests/` directory: `fly test` builds each one as a program of its own, through C, runs it, and holds what it prints to its `// expect:` lines (`selfhost/fly.fly`, `test`). That suits a test of a whole program — what it prints, how it ends — and it stays. It does not suit the small test of one function: each is a program with a `main`, compiled and linked apart, so twenty tests are twenty links; it sees only what its module exports, so a private helper is tested through the public functions around it or not at all; and nothing it needs only for testing can live beside the code it tests without being in every build.

This proposes what Rust has for that: functions marked `@test`, beside the code they test, reaching its private items; code marked `@only(test)` that exists only in a test build; and `fly test` compiling every test of the package into one program, linked once, that runs them all, on every core. It says how each kind of test is found, how a test's effects decide how it runs, what a test that fails, panics or ends the program reports, and what each target does. The last part is the text proposed for `docs/spec.md` and `docs/fly.md`, and, since the tests need assertions, for `docs/std.md`. None of those is changed yet.

The examples use today's imports, `import { x } from "m"`. The dotted form being designed separately changes nothing here but spelling: `@only(test) import std.test.{ assertEq };`, and a test's name is its module's dotted path (below), which is the same path that form imports it by.

Attributes in general, and the conditions `@only` takes, are the attribute design's: `docs/reviews/2026-10-25-attributes-design.md`, section 3 for the grammar and section 9 for conditional compilation (on the branch `claude/attribute-design-8601e7`). Its `@only(c)` takes a boolean expression over the build's facts, which are Rust's `cfg` facts with Rust's values, read as fields — `test`, `target.arch`, `target.os`, `target.family`, `target.env`, `target.endian`, `target.pointerWidth` — and Flyscript's own `page`. `@only(test)` is the case tests need. This proposal uses that design as it stands and adds `@test` to it.

## What it looks like

```ts
// parse.fly
@only(test) import { assertEq } from "std/test";

export function parsePort(raw: str): u16 uses Fail<#Empty | #NotANumber | #OutOfRange(u32)> {
  if (raw.len() == 0) { throw #Empty; }
  const n = digits(raw);
  if (n > 65535) { throw #OutOfRange(n); }
  n as u16
}

// Private: no other module may call it, and no program in tests/ can reach it.
function digits(raw: str): u32 uses Fail<#NotANumber> { … }

@test function digitsReadsDecimal(): void uses Fail<#NotANumber> {
  assertEq(digits("8080"), 8080);
}

@test function emptyIsEmpty(): void {
  assertEq(Fail.capture(() => parsePort("")), #Err(#Empty));
}

@test(panics = "overflow") function digitsPastU32(): void {
  const _ = Fail.capture(() => digits("99999999999"));
}
```

A module whose tests need more than an import has a group of them, which a test build has and every other build does not:

```ts
// profile.fly
import { Db } from "std/world";

export function displayName(db: mut Db, user: str): String uses Io, Fail<#NotFound> { … }   // retries the world's faults

@only(test) {
  import { World, assertEq } from "std/test";

  const ADA: World = World.empty().profile("ada", "Ada Lovelace").faults(25).seed(7);

  @test(world = ADA, seeds = 50)
  function retriesThroughFaults(): void uses Io, Fail<#NotFound> {
    let db = Db.connect();
    assertEq(displayName(mut db, "ada"), "Ada Lovelace");
  }
}
```

```
$ fly test
built 4 tests in 2 modules, and 1 program: target/tests/unit
ok   parse.digitsReadsDecimal
ok   parse.emptyIsEmpty
ok   parse.digitsPastU32
ok   profile.retriesThroughFaults (50 seeds)
ok   tests/hello
5/5 passed
```

## The design in brief

1. **Attributes are the attribute design's** (its section 3): `@name(…)` before `export`, an argument a flag or `name = e` with `e` evaluated at compile time, and an attribute that is not declared an error. `@test` is one more of the compiler's attributes.
2. **`@only(test)`** keeps a declaration, an import, an impl's method, or a braced group of them, to a test build; `@!only(test)` at the top of a file keeps the whole module, a module of fixtures. It is the attribute design's `@only(c)` (its section 9) with the condition `test`, and conditions combine: `@only(test && target.family != "wasm")`. A group is not a scope: what it declares is the module's. Code may name what is gated only under a condition that implies the gate, and that is checked across every build, so a build without tests cannot break where a test build does not.
3. **`@test`** before a module's function makes it a test, and implies `test`: `@test @only(target.os == "linux")` is a test that only Linux builds have. A test takes nothing, returns `void`, and performs at most `Io` and failures — what a task may perform (§6.1) — because each runs as a task.
4. **The compiler finds the tests**, when it parses. A test build compiles every module of the package with its test-only code, and an entry module the compiler makes, which names every test, private or not, and gives them to `std/test`'s runner. Nothing searches text.
5. **One program, linked once**: `target/tests/unit`. It runs each test as a task spawned in one scope, so tests run on every core, a panic ends its test alone (§5.7), and what a test prints is kept with it and shown if it fails.
6. **A test against a simulated world** (`@test(world = W)`) runs in a run of that same program of its own, `FLY_WORLD` set to `W` and its seed; `seeds = n` runs it under `n` seeds. The program is linked once and run once per world.
7. **A test that ends the program** — a panic in cleanup, a deadlock, `exit`, the heap gone, a WebAssembly trap — is found by `fly test`, which reports it as the one that did, and runs what had not finished in another run.
8. **Programs in `tests/` stay**, built and run as now, and now read the header lines of §6.4 that the repository's own suite reads, so a whole-program test can run against a world too. A file in `tests/` with no `main` is a module of tests instead, which joins the one program and sees the package as a dependent does.

The rest of this section is why, and what else was weighed. The proposed text follows it.

## How tests are found

**By the compiler, as it parses.** An attribute is syntax, so `@test` and `@only(…)` are known before a name is resolved or a type is checked. The compiler parses every module of the package — each `.fly` file under its directory but `tests/` and `target/`, which is what `fly build` already checks for a library — drops what is under a condition the build does not meet, `test` false in every build but a test build, and in a test build collects each `@test` with its module's path and its attribute's arguments. It then makes the entry module, `main` included, and compiles the whole as one program. A test's name is its module's path within the package, `/` written `.` and `.fly` left off, then the function's name: `lexer/token.fly`'s `numbers` is `lexer.token.numbers`.

The entry module is the one module that may name another's private functions, as a derivation a struct asked for may build its private fields (§7.3): no hand-written module can, and the privacy rules are otherwise unchanged. It is as if it were written:

```ts
import { Case, runTests } from "std/test";

export function main(args: readonly String[]): void uses Io {
  runTests(args, [
    Case { name: "parse.digitsReadsDecimal", body: () => Fail.map(() => parse.digitsReadsDecimal(), (e) => #Failed(`${e}`)),
           world: #None, seeds: 1, panics: #None, ignore: #None },
    …
  ]);
}
```

so the runner is library code, `std/test`, written in Flyscript, and the compiler's part is the table. Each case's body has one type, `() => void uses Io, Fail<#Failed(String)>`, whatever its test performs: a test's failure is shown into a `String` where the compiler knows its type.

What was weighed against it:

- **`fly` finds them**, by reading the files for `@test`. It would have to parse Flyscript to do it right — a test inside a group, an attribute on the line above — and the program it then writes could not call a private test, so tests would have to be exported, which puts them in the package's face, in its lockfile's effects, and in every dependent's way.
- **`comptime` finds them**, through a reflection of the build's tests that `std/test`'s `main` loops over. It is the most Flyscript-like (law 5), and it may be where this goes. It needs a function to be a compile-time value, which `comptime` does not have — `Type` is the one kind of value that stands for code — and it would still need the compiler's leave to call private functions. The table is the smaller step, and is what such a reflection would give.
- **Tests found where they are reached from `main`.** A library has no `main`, and a helper's tests are worth having whether or not a program reaches the helper yet.

A dependency is compiled as in every other build: its tests and its test-only code are not in the package's test build. `fly test` tests the package at hand.

## Test-only code: `@only(test)`

Test-only code is the attribute design's conditional compilation (its section 9) with the condition `test`, and everything a test needs of it, that design gives:

- **An attribute, not `comptime if`.** `comptime if` already chooses code, and a module-level `comptime if (build.test) { … }` would seem to be the way law 5 wants. It is rejected because it would choose imports. The import graph is known before `comptime` runs — `comptime` code calls what the module imports, and modules compile in parallel in the order of their imports (§8.1) — so an import that `comptime` code decides would make the graph depend on what it decides. A condition reads only the build's facts, never a module, so the loader evaluates every one and drops what does not hold before it builds the graph. `comptime if (build.test)` still chooses code inside a body, where an attribute cannot go.
- **Parsed in every build; checked where it holds.** What is `@only(test)` is always well formed and its names are known, and it is checked — its names resolved, its types and effects and ownership — only in a test build.
- **A reference needs the gate's condition or a stronger one.** Code under condition A may name what is under B only if A implies B, which the compiler decides by evaluating both in every build it can make. So the error is the same in every build: `` `sample` exists only in builds where `test`; this code is also in builds where it does not hold ``, not `unknown name` in one build and nothing in another.
- **Conditions accumulate.** A test in an `@only(test && target.family == "unix")` group, or `@test @only(target.family == "unix")`, is a test only native builds have; `fly test --target wasm` leaves it out, and says how many it left out.
- **A test-only export is the tests' alone.** An `export` under `test` is a module's export to the package's other test-only code — a module of fixtures, `@!only(test)` — and to no one else: a dependency is never built as a test, so it is never in what a dependent sees, and the lockfile does not list its effects.

## A test is a task

A test takes nothing, returns `void`, and performs at most `Io` and failures. That is not a rule of its own: it is what a task spawned in a scope may perform (§6.1, rule 4), and every test runs as one. The runner opens one scope and spawns each test in it, its body wrapped so its failure is a value:

```ts
Io.scope((s) => {
  for (const c of cases) {
    const task = s.spawn(() => { report(c.name, Fail.capture(c.body)); });
    …
  }
});
```

What that gives, each from a rule already in the spec:

- **A pure test** cannot observe another (law 2; a module has no mutable state, only compile-time constants), so tests that perform nothing run in any order and at once and cannot interfere. Whether a test can is in its type.
- **A test that `uses Io`** performs it against the machine: its files, its sockets, its clock, from the package's directory as its working directory. Two such tests may meet there — a file both write, a port both listen on — and the type says which tests those are. A test that needs the machine to itself runs against a world instead, or in a directory of its own, `withTempDir`.
- **A test that `uses Fail<E>`** fails when a failure escapes it, and the failure is shown as `main` shows one: `<uncaught: #NotFound>`, here `it failed: #NotFound`. A test of a failure catches it: `assertEq(Fail.capture(() => …), #Err(#Empty))`.
- **A test with an effect of its own** is an error, which says to handle it: `a test performs only Io and failures; checkout performs Clock — handle it in the test`. That is the point of effects as dependency injection (A.11): the test is where the handler goes.
- **A panic ends its test alone** (§5.7): the test's task unwinds, running its cleanup, and its `Task`'s `wait` gives `#Panicked(message)`, which the runner reports. Every other test goes on.
- **A panic a test's own tasks report** — one spawned and never `wait`ed for — fails the test too: it would otherwise go to the program's standard error with no name on it, and pass.
- **`panics = "text"`** reverses it: the test passes if it panics with a message that contains `text`, and fails if it returns or fails. A panic cannot be caught in the language (§5.7), so this is the only way to test one without a program of its own.
- **`ignore = "why"`** keeps the test from running unless asked (`fly test --ignored`); it is still compiled and checked.

**What a test prints is kept.** The runtime gives each task a place its standard output and error go, and a task inherits its starter's; the runner gives each test one of its own. What a test and the tasks it started printed is shown with its failure, and with every test given `--show-output`. The runner's own output is then the report alone. This is the runtime's — the language sees standard output written as ever — and with it a test's output stays its own while tests run on every core, which Rust's capture, thread-local, does not do for threads a test starts.

**A test that never ends.** Cancellation reaches a task only at its `Io` operations (§6.1), so a test in a pure loop cannot be stopped from inside the program; and a test in cleanup that waits holds its task (§5.6). The runner says `slow parse.deepNesting: 60 s and running` once, and `fly test --timeout 300` stops the program after that long on one test, reports the test as having timed out, and runs the rest again (below).

## A test against a simulated world

A world (§6.4) is the runtime's root handler of `Io`, chosen as the program starts: its tasks on one thread, a seeded scheduler, a virtual clock, its sockets and peers. Two tests cannot share one: the order the seed gives to one test's tasks would depend on every other test's, and a test's result would change with the tests beside it. So a test given a world runs alone in a run of the same program, given that world and told to run that test: linked once, run once per world. `fly test` starts those runs, up to `--jobs` at once, beside the run of every other test.

`world = W` takes a `World`, a value `std/test` declares, evaluated at compile time and made into the JSON `FLY_WORLD` takes. Its builder names the header lines of §6.4 one for one: `World.empty().request(text).peer(addr, text).profile(user, name).quota(token, allowed).faults(n).seed(n)`. `@test(world)` alone is the empty world with the default seed: a test of tasks and time with no peers.

`seeds = n` runs the test under `n` seeds, from the world's on, each a run of its own, and fails it on the first seed it fails under, saying which: `FAIL profile.retriesThroughFaults (seed 31): it failed: #NotFound — fly test profile.retriesThroughFaults --seed 31 runs it again`. A seed decides each interleaving and each fault, so fifty seeds are fifty schedules, and the one that fails is reproduced exactly, in every implementation. `fly test --seeds 1000` runs every world test under more.

The other scale of §6.4 needs nothing new: a test that handles `Io` itself, answering `sleep` or `now`, is an ordinary test that performs `Io`, and runs in the one program with the rest.

**Weighed against it: a world in the program.** The runtime could make a world for one scope — a scheduler, a clock and a seed of that scope's own, its tasks on one thread — and then a world test would be a task like any other. It is the better end, and the run of its own is the step to it that needs nothing of the runtime: the world is a property of a run today, read from `FLY_WORLD` as the run starts, in the C, JavaScript and WebAssembly runtimes and the reference evaluator alike.

## When a test ends the program

Some things end the program, not their task (§5.7): a panic in cleanup a panic is running, or out of a destructor; a deadlock, every task waiting and none able to run; `exit`; the heap exhausted; in WebAssembly, the engine's own stack running out, which traps. A test that does one of these takes the run with it.

The runner says as each test starts and as it ends. A run that ends before it has said every test ended is one a test ended: if one test had started and not ended, that test did it, and is reported so — `FAIL lexer.runaway: it ended the program: <panic: stack overflow, in a destructor>`; if several had, each runs again alone, to find which. The tests that had not finished run in another run. A deadlock is found this way too: one test waiting on itself is not the program's deadlock while others run, and becomes it when they have finished, with that test the only one not ended.

## Running them on every core

- **Natively** the tests' tasks run on a worker thread for each core (§8.3), and `--jobs n` keeps at most `n` running at once, the number of cores unless it says otherwise. The runs for worlds are processes, and count in the same `n`.
- **The order of the report** is the order tests end, for the feedback; the failures are said again, by name, at the end, so two reports of one result read the same where it matters.
- **Pure tests' `par`** runs on the program's pool, as any `par` does.

## Targets

`fly test --target native | js | wasm`, native unless it says otherwise.

- **Native.** The program through LLVM if it is there, else through C, as `fly build` makes one, to `target/tests/unit`. Its tasks run on every core. A world's run is the same executable, with `FLY_WORLD` set.
- **JavaScript.** The program compiled to JavaScript and run by Node with the runtime the compiler's own JavaScript build uses. The runtime is one thread: tests run as tasks that interleave where they wait, and pure tests one after another. `fly test` runs one run per core, each given a share of the tests (`--shard i/n`, every `n`th test from the `i`th), for the cores. A stack that runs out is a panic, as it is natively (the runtime makes Node's `RangeError` one), so it ends its test alone.
- **WebAssembly.** The program compiled for WASI and run by `selfhost/wasm.js`, in shards as for JavaScript, since there are no threads (§8.3). A world's run is another instance of the module compiled once, in the same Node, its environment given `FLY_WORLD`: an instance is cheap, and the module is compiled once. A trap ends the instance, and is reported as a test that ended the program.
- **Freestanding.** A freestanding program has no `main`, no `Io` and no unwinding: its panic goes to `fly_os_panic` (§8.3). Its tests are built for the machine `fly` runs on instead, with the hosted runtime, which the same code compiles for unchanged. Code that needs the hardware — an `extern "C"` that only the firmware links — is `@only(target.os == "none")`, so the host's test build leaves it out, and the tests of what is left run there.
- **A site.** The tests of an app's modules run natively. A module that declares the page's host functions (`extern "C"`, which `web/flynext.js` gives a page) is `@!only(page)`, so a native test build leaves it out, and its tests with it; how to test it is left to the open questions below.

A build for a target has the tests that target's facts allow: `@test @only(target.family == "unix")` is in `target/tests/unit` and not in the WebAssembly build, and `fly test` counts what a target left out (`3 tests not on wasm`), so a test that never runs anywhere it is asked to is seen.

## Whole-program tests stay

`tests/*.fly` with a `main` is a program, built and run as now, its output held to its `// expect:` lines. Two things change:

- It reads the header lines of §6.4 — `request`, `peer`, `profile`, `quota`, `faults`, `seed` — and runs against that world if it has any, as the spec has always said a test does and the repository's own suite (`selfhost/corpus.sh`) does; `fly test` today does not.
- It runs from the package's directory, and on every core: the programs are built and run in parallel, each still apart.

A file in `tests/` with no `main` is a **module of tests**: its `@test`s join the one program, and it reaches the package only as a dependent would, through what the package exports. That is Rust's integration test, without a link of its own.

## Where it would be built

For the reviewer's sense of size, not as a plan to follow:

- **Attributes and `@only`** are the attribute design's to build (its sections 3, 9 and 12): parsing every attribute, groups, evaluating conditions before the import graph, and the check that a reference's condition implies its gate. Tests need only `test` among its facts.
- **Loading** (the compiler's module loader, both implementations): a `--test` mode, given the package's modules, which makes `test` hold, collects the tests, and makes the entry module.
- **`std/test`**: `assert`, `assertEq`, `assertNe`, `World`, `withTempDir`, `Case` and `runTests`, in Flyscript.
- **The runtimes** (`selfhost/runtime.c`, `runtime.js`, and the WebAssembly host): a place each task's output goes, inherited, and a panic a task reports counted against the place.
- **`fly test`** (`selfhost/fly.fly`): build the program once, ask it for its tests (`--list`), run it and the worlds' runs, read what each says, run again after a run that ended early, and the programs in `tests/` as now, with their headers.

It is a roadmap step of its own, after the import change, whose module paths it names tests by.

## Open questions

1. **Where a panic was.** A panic's message says what, not where; `assertEq(a, b)`'s panic is in `std/test`. Rust's answer is `#[track_caller]`; Flyscript's could be an attribute, `@caller`, by which a function's panics say its caller's line. Until then the report names the test, and `assertEq` takes an optional label.
2. **A world in the program**, as above, so a world test needs no run of its own and `seeds = 1000` costs a thousand tasks, not a thousand processes.
3. **Tests of a page's modules**, which need the page's host: a host for tests that answers the DOM's functions in memory, as `std/world` answers a database.
4. **Compile-time tests.** A module-level `comptime assert` is already a test the compiler runs. A `@test` on a `comptime function`, run in every test build by the compiler's interpreter, would test the code that derivations are made of.
5. **Benchmarks.** `@bench`, in the same program, timed by the runner: the same finding, the same table, a different runner.

---

# Proposed text

What follows is written to drop into the documents as they are. Each part says where it goes. It assumes the attribute design's text has gone into the spec first: its grammar of attributes in §2.3, and its conditional compilation in a section of its own, written §C below until it has a number.

## `docs/spec.md`

### Version and §0.1

Version 0.137; at the head of §0.1's list:

> - **Tests beside the code** (0.137): a function marked `@test` is a test, which may reach its module's private items; `@only(test)` keeps a declaration, an import or a group of them to test builds; and a test build compiles every test of a package into one program, each test a task of it, so a panic ends its test alone and tests run on every core. A test given a simulated world runs against it alone (§6.4, §8.4, §C).

### §2.3 Grammar, §3.3

Nothing more than the attribute design's: its grammar has `@test`'s arguments (`name = e`, flags), its groups, and attributes before `export`, and it rewrites §3.3's sentence on `@layout`.

### §6.4, after the header lines

> A test of a module asks for a world in its attribute, `@test(world = W)`, and runs against it alone (§8.4).

### §8.4 Tests (new)

> ### 8.4 Tests
>
> A **test** is a module's function marked `@test`. It takes nothing, returns `void`, and performs at most `Io` and failures: what a task may perform (§6.1), for each test runs as one. It is in the module, so it reaches what the module does, private functions and private fields included. It is not exported; the program that runs it calls it, and no one else may.
>
> ```ts
> @only(test) import { assertEq } from "std/test";
>
> function digits(raw: str): u32 uses Fail<#NotANumber> { … }
>
> @test function digitsReadsDecimal(): void uses Fail<#NotANumber> { assertEq(digits("8080"), 8080); }
> @test(panics = "overflow") function digitsPastU32(): void { const _ = Fail.capture(() => digits("99999999999")); }
> ```
>
> **Test-only code.** In a *test build* of a package the fact `test` holds (§C), so `@only(test)` keeps a declaration, an import or a group of them to test builds, and `@!only(test)` a module. `@test` implies `test`: `@test @only(target.os == "linux")` is a test only Linux builds have. A dependency is never built as a test, so a test build of a package leaves out its dependencies' tests and test-only code, and a test-only export is the package's test-only code's alone.
>
> **One program.** A test build compiles every module of the package and an entry module the compiler makes, the one module that may name another's private functions, which gives every test to `std/test`'s runner. A test's name is its module's path in the package, its separators `.` and its `.fly` left off, and the function's: `lexer/token.fly`'s `numbers` is `lexer.token.numbers`. The runner spawns each test in one scope, so tests run at once, on every core, and a pure test, which can observe nothing (law 2), cannot be changed by another. A test:
>
> - **passes** if it returns;
> - **fails** if a failure escapes it, shown as `main` shows one (§8.1); if it panics, the panic ending its task alone (§5.7); or if a task it started panics and no `wait` gives the panic;
> - with **`panics = "text"`**, passes only if it panics with a message containing `text`;
> - with **`ignore = "why"`**, is compiled and checked but run only when asked.
>
> What a test writes to standard output and error, and what the tasks it started write, is kept apart from every other test's and shown with its failure. A test that ends the program (§5.7) — a panic in cleanup a panic is running, a deadlock, `exit`, the heap exhausted, a WebAssembly trap — is reported as having ended it, and the tests that had not finished run again.
>
> **Against a world.** `@test(world = W)` runs the test against the simulated world `W` (§6.4), a compile-time value of `std/test`'s `World`, alone: a seeded schedule is reproducible only if nothing else is in it. `seeds = n` runs it under `n` seeds from `W`'s, and a failure names its seed, under which it runs the same way again, in every implementation. `@test(world)` is the empty world.
>
> How a package's tests are built and run, and its programs in `tests/`, is `fly test`'s ([fly.md](fly.md)).

### §8.3, at the end of the WebAssembly item

> A test build's program runs the same way; with no threads, its tests run as tasks on one, and a trap ends the instance with the test that caused it (§8.4).

### §12.2 Rejected alternatives, two more

(Gating by `comptime if` is the attribute design's to reject, with §C.)


> - **Tests found by the build tool**, reading the files for them: it would have to parse Flyscript to find them, and could call only what a module exports, so tests would be part of a package's face. The compiler finds them as it parses (§8.4).
> - **A program for each test**: a link each, and a test of a private function impossible. A test of a whole program is still one (`tests/`, [fly.md](fly.md)); a test of a function is a task of one program.

## `docs/fly.md`

### The opening commands

```sh
fly test                      # every test in the package, in one program, and every program in tests/
fly test parse                # the tests whose names have `parse` in them
```

and in the paragraph under it, nothing else changes.

### The manifest

After `[dependencies]` in the example:

```toml
[test-dependencies]
quickcheck = { git = "https://github.com/example/fly-quickcheck", version = "0.4" }
```

and a sentence after the paragraph on dependencies:

> A test dependency is a dependency only of the package's tests: its modules may be imported only by code under `test` (`@only(test)`, spec §8.4 and §C) and by the programs in `tests/`. It is locked, and held to its lock, as any other, and a dependent of the package does not have it.

### The lockfile, in the item on effects

> … from the modules of the package the program uses: `parse size:` is pure, `parse report: Io` performs `Io`. A function that is test-only is not among them. …

### Testing (new, before "Where things are")

> ## Testing
>
> A package has two kinds of test, and `fly test` runs both.
>
> **Tests beside the code.** A function marked `@test` in any of the package's modules is a test (spec §8.4): it may call the module's private functions, and code marked `@only(test)` is there for it and in no other build. `fly test` compiles the package's every module, its tests and its test-only code, into one program, `target/tests/unit`, linked once, and runs it: each test a task, at once, on every core.
>
> ```ts
> @only(test) import { assertEq } from "std/test";
>
> function digits(raw: str): u32 uses Fail<#NotANumber> { … }
>
> @test function digitsReadsDecimal(): void uses Fail<#NotANumber> { assertEq(digits("8080"), 8080); }
> ```
>
> A test is named by its module's path and its own name, `parse.digitsReadsDecimal`. It passes if it returns. It fails if a failure escapes it, if it panics, or if a task it started panics with no one waiting to be told; what it printed is shown with it. A test given a simulated world, `@test(world = W)`, runs against it in a run of the program of its own, under each seed `seeds = n` asks for, and a failure says how to run it again: `fly test name --seed 31`.
>
> **Programs in `tests/`.** Each `.fly` file in `tests/` with a `main` is a program, built and run alone, from the package's directory, and held to its `// expect:` lines; its header lines (spec §6.4) are the world it runs against, if it has any. A file in `tests/` with no `main` is a module of tests, which joins the one program and reaches the package only through what it exports.
>
> ```
> $ fly test
> built 23 tests in 5 modules, and 3 programs: target/tests/unit
> ok   lexer.numbers
> FAIL parse.deepNesting: it panicked: stack overflow
> FAIL config.rejectsEmpty: it failed: #Empty
>   it printed:
>     reading fly.toml
> ok   profile.retriesThroughFaults (50 seeds)
> skip db.roundTrip: needs a Postgres server
> ok   tests/hello
> 23/25 passed, 1 skipped
> error: 2 failed
> ```
>
> - `fly test name` runs the tests whose names have `name` in them, and `--exact` the one that is named so; `--list` names every test and runs none; `--ignored` runs those marked `ignore` too.
> - `--jobs n` runs at most `n` tests at once, the number of cores unless it says otherwise; a world's run counts as one.
> - `--seed n` runs each test that has a world under seed `n`, and `--seeds n` under `n` seeds.
> - `--show-output` shows what every test printed, not only a failing one's.
> - `--timeout s` stops a test that has run for `s` seconds and reports it; a test runs as long as it takes unless it says so, though one running a minute is said to be slow.
> - `--target js` and `--target wasm` build the program for JavaScript or WebAssembly instead and run it under Node, as many runs as cores, each with a share of the tests, since each runs on one thread. A test under a condition the target does not meet, `@test @only(target.family == "unix")`, is not in that build, and `fly test` says how many were left out.
>
> A test that ends the program — a deadlock, `exit`, a panic in cleanup a panic is running — is reported as having ended it, and `fly test` runs the tests that had not finished again. `fly test` ends with a failure status if any test failed.

## `docs/std.md`

### `std/test` (new, after `std/world`)

> ## 17a. `std/test`
>
> For tests (spec §8.4), imported by test-only code.
>
> | Function | Contract |
> | :--- | :--- |
> | `assert(c)`, `assert(c, label)` | Panics if `c` is false, with `label` if it is given. |
> | `assertEq(got, want)`, `assertEq(got, want, label)` | Panics if `got != want`, showing both: `assertEq: got 3, want 4`. `T extends Eq & Show`. |
> | `assertNe(got, other)` | Panics if they are equal. |
> | `withTempDir(body)` | Makes a directory no other test has, lends its path to `body`, and removes it and what is in it after, however `body` ends. Performs `Io`. |
> | `World.empty()` | The simulated world with nothing in it and the default seed, a value made at compile time; `.request(text)`, `.peer(addr, text)`, `.profile(user, name)`, `.quota(token, allowed)`, `.faults(n)` and `.seed(n)` add what the header lines of spec §6.4 say. |
> | `runTests(args, cases)` | The runner a test build's `main` calls: each `Case` a task in one scope, what it prints kept, what it ends with reported. A package does not call it. |
>
> The assertions panic rather than fail, so a pure test uses them and stays pure, and a test that expects a failure catches it and compares: `assertEq(Fail.capture(() => parsePort("")), #Err(#Empty))`.
