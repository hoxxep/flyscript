# Flyscript

**The TypeScript you already know, with the performance and safety of a systems language.**

*Affine values, one row calculus, handlers for everything, and `comptime`: Church on the outside, Turing on the inside.*

Flyscript compiles ahead of time to native code and WebAssembly. It has no garbage collector, no lifetime annotations and no `async`/`await`, and it is memory-safe and free of data races by construction. If you can read TypeScript, you can read Flyscript today.

```ts
import { Listener, Db } from "std/net";

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

- **Language specification:** version 0.49, with every earlier version and the reasoning behind each change in [docs/history](docs/history/).
- **Compiler (`flyc`):** a complete prototype front end and evaluator. `flyc check` type-, effect- and ownership-checks programs, rejecting use after move, conflicting borrows, borrows that escape through closures and generators, undeclared effects and non-exhaustive matches with precise errors. `flyc run` executes them, with effect handlers, generators and structured concurrency, against a deterministic simulated world. `comptime` runs too: templates specialize per type, and the standard library's JSON codec is derived over reflection in plain Flyscript, with no compiler support.

Next comes code generation. Flyscript is not yet ready for production programs; it is ready for your ideas, and issues and discussion about the design are very welcome.

## Explore

- [The specification](docs/spec.md) — the five laws, the type system, effects, ownership, concurrency.
- [Example programs](examples/) — a JSON parser, derived JSON encoding and decoding, an inventory service, a web server, a key–value actor, a browser UI, generators, parallel physics.

## Build from source

Requires a recent stable Rust toolchain.

```sh
git clone https://github.com/rogersnm/flyscript && cd flyscript
cargo test                          # run the test suite
cargo run -- check examples/*.fly   # type-, effect- and ownership-check Flyscript files
cargo run -- run tests/run/http_server.fly   # run a program against the simulated world
```

## License

Copyright © 2026 Fieldwork AI Inc.

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
