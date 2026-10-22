# Flyscript

**The TypeScript you already know, with the performance and safety of a systems language.**

*Affine values, one row calculus, handlers for everything, and `comptime`: Church on the outside, Turing on the inside.*

Flyscript compiles ahead of time to native code and WebAssembly. It has no garbage collector, no lifetime annotations and no `async`/`await`, and it is memory-safe and free of data races by construction. If you can read TypeScript, you can read Flyscript today.

```ts
import { Listener } from "std/net";
import { Db } from "std/world";

// A server that cannot be taken down by a bad connection — and the compiler proves it.
export function serve(listener: mut Listener, db: readonly Db): void uses Io, Fail<IoErr> {
  Io.scope((s) => {
    for (const conn of listener.accept()) {
      s.spawn(() => serveOne(conn, db));   // serveOne handles its own errors; its type says so
    }
  });
}
```

## The idea in one line

*Church on the outside, Turing on the inside*: programs compose like the lambda calculus — values, functions and types that fit together cleanly — while the compiler lays them out for the machine as a C programmer would, in place and unboxed. Four ideas carry the whole language:

- **Affine values.** Every value has exactly one owner, and a borrow can be passed down but never stored where it could outlive its owner. That alone gives memory safety without a collector and without lifetime annotations.
- **One row calculus.** Records (`{ x: f64; ...R }`), tag unions (`#Ok(T) | #Err(E)`) and lists of effects (`uses Io, Fail<E>`) are the same kind of thing, checked by one mechanism. It is why functions accept any record with the fields they need, and why error types combine by union with no conversion code.
- **Handlers for everything.** Failure, I/O, generators and memory regions are all *effects* handled by ordinary handlers. `throw`/`catch`, `yield`/`for…of`, structured concurrency and deterministic simulation are library code on one primitive.
- **`comptime`.** Generics, derived interfaces and data layout are ordinary Flyscript run by the compiler, not a second language of macros or templates.

## Why Flyscript

**It reads like TypeScript.** `const`, `let`, arrow functions, object literals, unions, generics with `extends`, `interface`, `import`/`export`, `for…of`, `throw`/`try`/`catch`, template strings. The syntax is the one millions of developers already use; what changes is what the compiler can promise about it.

**Fast by default.** Values are unboxed and laid out like C. Generics are monomorphized. There is no hidden allocation and no collector, so there are no pauses. Data-oriented layouts such as struct-of-arrays are a library type, not a rewrite.

**Safe without the ceremony.** Every value has one owner. Borrows are checked by the compiler but never written as lifetime parameters, so your types stay readable. Data races are impossible because shared mutation has to say so in the type.

**Errors you can see.** A function's failures are part of its type, as a union of tags. Calling two functions that fail in different ways gives you the union of both — no wrapper types, no conversion boilerplate. A `catch` knows exactly what it can catch, and the compiler checks you handled it.

```ts
function parsePort(raw: str): u16 uses Fail<#Empty | #NotANumber | #OutOfRange(u32)> { … }

const port = try { parsePort(raw) } catch (e) {
  match (e) { #Empty => 80, #NotANumber | #OutOfRange(_) => throw #BadConfig }
};
```

**No `async`, no colored functions.** I/O, errors, generators and memory regions are all *effects*: ordinary features of the type system rather than separate language modes. A function that reads from the network is written in plain direct style and calls anything.

**Deterministic simulation testing, built in.** Because I/O is an effect, any program can run under a simulated network and clock with a fixed seed. Concurrency bugs become reproducible, single-threaded test failures.

```ts
test("degrades gracefully under packet loss", () => {
  SimIo.run({ seed: 0x5eed, loss: 0.25 }, () => { … });
});
```

**Arenas without the footguns.** Build a parse tree or a per-request graph — cycles and all — in a region, and free it in one step when the block ends. The compiler guarantees nothing escapes.

**One small core.** Five rules underpin the whole language, and most features — generators, structured concurrency, parallel loops, data layout — are library code built on them. Read the [specification](docs/spec.md) to see how they fit together.

## Status

Flyscript is an early-stage language under active design, developed in the open.

- **Language specification:** version 0.70, with every earlier version and the reasoning behind each change in [docs/history](docs/history/).
- **Proofs:** two fragments of the core calculus are proved in Lean, in [proof/](proof/): a program that moves, drops and lends boxes never touches a moved or freed cell and ends having freed everything but its result, failures and all, and a program with effect handlers never performs an operation nothing handles. What the proofs do not yet cover is listed in the specification (§9.5).
- **Library specification:** [docs/std.md](docs/std.md), every function the standard library exports: what it performs, when it fails, what it costs.
- **Compiler (`flyc`):** a complete prototype front end and evaluator. `flyc check` type-, effect- and ownership-checks programs, rejecting use after move, conflicting borrows, borrows that escape through closures and generators, undeclared effects and non-exhaustive matches with precise errors. `flyc run` executes them, with effect handlers, generators and structured concurrency, against a deterministic simulated world. `comptime` runs too: templates specialize per type, and the standard library's JSON codec is derived over reflection in plain Flyscript, with no compiler support.

- **Flyscript in Flyscript:** a compiler written in Flyscript, in [selfhost/](selfhost/), parses, elaborates and checks the whole language — types, effects and ownership — reaching the same verdict as `flyc` on every program in the test suite, `comptime` and all. Its back end is typed: it specializes every generic function for the types it is used at, so method calls are direct, integers keep their widths, derived interfaces are compiled from their `comptime` definitions, effect handlers, generators and tasks run as JavaScript generators, and destructors run where the ownership checker says values die. Every program in the test suite runs compiled exactly as it runs in `flyc`, down to how its tasks interleave. It compiles itself: built by `flyc`, then run on its own output, it reproduces itself byte for byte, in about three seconds.

- **Native code:** the same compiler compiles to C and on to a native executable, with no garbage collector and no runtime to speak of. Ownership decides where every value is freed; failures, `break` and `return` leave through a single exit that drops exactly what is still owned; a handler whose arms only resume costs a call per operation, and other handlers, continuations and tasks run on lightweight fibers; regions are bump arenas released in one step. Every program in the test suite runs natively exactly as it runs in `flyc`, down to how its tasks interleave, with address and undefined-behavior sanitizers watching. The compiler builds itself this way too: natively compiled, it reproduces its own C byte for byte, in under four seconds.

- **LLVM:** the compiler also writes a program's code as LLVM IR, links it with the runtime's C, and optimizes the two as one program, so a call into the runtime inlines like any other. Integer arithmetic is LLVM's own, checked by its overflow intrinsics. Debug information maps every instruction to its line and every variable to its value: a debugger stops at a line of a `.fly` file and shows strings, lists, structs and tagged unions as Flyscript writes them. Every program in the test suite runs this way under the sanitizers, the compiler built through LLVM reproduces itself byte for byte, and the kernel boots built through LLVM too, cross-compiled for AArch64.

- **The web:** [FlyNext](web/), what Next.js and React are for a JavaScript site, in library code and an app compiler written in Flyscript, and a [site](examples/todo/) built with it. Pages are files, `todos/[id].fly` answering `/todos/7`, with layouts around them and data loaded on the server; views are functions that perform `Ui`, which the server, compiled natively, handles by writing HTML, and one WebAssembly program for the whole site by taking over what the server rendered and patching the DOM by a keyed diff of flat operation lists, with no virtual DOM. Links are followed without loading a page — the next page's data fetched, prefetched as the pointer nears the link, and rendered in place, its layout kept — and back and forward work the same way. Server functions are an effect, handled against the store on the server and by calls the app compiler writes in the page, with typed failures raised where they were made. `web/flynext dev` rebuilds as the app changes and reloads open pages. The server is Flyscript's own HTTP/1.1 over real sockets, a task per connection on every core.

- **Every core:** native tasks run on a worker thread for each core, an idle worker stealing tasks not yet begun from a busy one, and `par` and `parReduce` split their work across all of them with a work-stealing `join`. On a 30-core machine, `par` over twenty million elements runs 24 times faster than on one core. Against a simulated world the same program runs its tasks one at a time, in the order its seed decides, which is how the test suite runs; on threads, the thread sanitizer checks the runtime.

The compiler is written in Flyscript and compiles itself — to JavaScript, to native code through C or LLVM, and to WebAssembly — through one core IR; a small kernel written in Flyscript boots on QEMU. What comes next is in the [roadmap](docs/roadmap.md). Flyscript is not yet ready for production programs; it is ready for your ideas, and issues and discussion about the design are very welcome.

## Explore

- [The specification](docs/spec.md) — the five laws, the type system, effects, ownership, concurrency.
- [A site](examples/todo/) — a list of things to do: a native server rendering pages, and a WebAssembly program for each page that takes it over, both from the same views.
- [A kernel](examples/kernel/) — Flyscript with no operating system under it, booting on QEMU: page tables, a UART driven through its registers, its own memory allocator, effect handlers on fibers.
- [Example programs](examples/) — a JSON parser, derived JSON encoding and decoding, an inventory service, a web server, a key–value actor, a browser UI, generators, parallel physics.
- [The roadmap](docs/roadmap.md) — what comes next, and why in that order.
- [The self-hosted compiler](selfhost/) — a lexer, parser, type and effect checker, `comptime` interpreter, and JavaScript, C and LLVM back ends, in Flyscript.

## Build from source

Requires a recent stable Rust toolchain.

```sh
git clone https://github.com/rogersnm/flyscript && cd flyscript
cargo test                          # run the test suite
cargo run -- check examples/*.fly   # type-, effect- and ownership-check Flyscript files
cargo run -- run tests/run/http_server.fly   # run a program against the simulated world
```

To compile a program natively with the self-hosted compiler (needs Node.js and a C compiler):

```sh
node --stack-size=65500 selfhost/seed.js examples/word_count.fly word_count.c .
cc -std=gnu11 -O2 -o word_count word_count.c -lm
```

Or through LLVM (needs clang and llvm-link of one version, such as Homebrew's `llvm`), with debug information for lldb or gdb:

```sh
sh selfhost/llvm.sh selfhost/seed.js examples/word_count.fly word_count
```

The compiler compiles itself the same way: `selfhost/main.fly` in place of the example.

## License

Copyright © 2026 Fieldwork AI Inc.

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
