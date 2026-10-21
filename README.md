# Flyscript

*Affine values, one row calculus, handlers for everything, and `comptime`: Church on the outside, Turing on the inside.*

Flyscript is a systems language with TypeScript's surface. It compiles ahead of time to native code and WebAssembly, has no garbage collector, and is memory- and data-race-safe without lifetime annotations. Errors, I/O, iteration and region memory are algebraic effects, so every program can run under a deterministic simulator.

```ts
export function serve(listener: mut Listener, db: readonly Db): void uses Io, Fail<IoErr> {
  Io.scope((s) => {
    for (const conn of listener.accept()) {
      s.spawn(() => serveOne(conn, db));   // serveOne cannot fail, so neither can the server
    }
  });
}
```

- **[docs/spec.md](docs/spec.md)**: the language specification (currently 1.7).
- **[examples/](examples/)**: the spec's programs, kept identical to it by a test.
- **[docs/history/](docs/history/)**: earlier spec versions and the review rounds that shaped them.
- **[docs/reviews/](docs/reviews/)**: independent design reviews by Gemini 4 Argon, made with `tools/second_opinion.py`.

## Second opinions

```sh
gcloud auth application-default login       # once
python3 tools/second_opinion.py ask --topic "short name" question.md [--context src/file.rs …]
python3 tools/second_opinion.py list
```

The reviewer is instructed (tools/reviewer.md) to give verdicts, back every objection with a program, and never simply agree. It sees the whole spec and earlier reviews; answers are saved to docs/reviews/ and reused when the same question is asked against the same spec.

## Status

This repository holds a prototype compiler, `flyc`, built milestone by milestone:

1. **Syntax** (done): lexer and parser for the whole grammar; every spec program parses.
2. **Types and effects**: nominal and structural types, one row unifier for records, tags and effects, bidirectional inference.
3. **Ownership**: moves, the borrow ledger, second-class propagation, tied returns, region non-escape.
4. **Evaluation**: an abstract machine with handlers and one-shot continuations, running the examples and the deterministic simulator.

```sh
cargo test                          # unit tests, and every example parses and matches the spec
cargo run -- parse examples/*.fly   # parse files
cargo run -- ast examples/zip.fly   # print a syntax tree
```
