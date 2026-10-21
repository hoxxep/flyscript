# Flyscript

**The TypeScript you already know, with the performance and safety of a systems language.**

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

- **Language specification:** version 1.7, with every earlier version and the reasoning behind each change in [docs/history](docs/history/).
- **Compiler (`flyc`):** the parser handles the full grammar; the type and effect checker is in progress, followed by ownership checking and an evaluator.

It is not yet ready for real programs. It is ready for your ideas: issues and discussion about the design are very welcome.

## Explore

- [The specification](docs/spec.md) — the five laws, the type system, effects, ownership, concurrency.
- [Example programs](examples/) — a JSON parser, a web server, a key–value actor, a browser UI, generators, parallel physics.

## Build from source

Requires a recent stable Rust toolchain.

```sh
git clone https://github.com/rogersnm/flyscript && cd flyscript
cargo test                          # run the test suite
cargo run -- parse examples/*.fly   # parse Flyscript files
```

## License

Copyright © 2026 Fieldwork AI Inc.

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
