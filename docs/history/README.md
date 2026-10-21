# Specification history

Every earlier version of the specification, and the review rounds that shaped them.

Versions are pre-1.0 while the language is being designed. The specification was briefly numbered 1.x; those versions were renumbered 0.1x (1.0 became 0.10, 1.7 became 0.17), so file names follow the new numbers while the documents keep the numbers they were written with.

| Version | What changed |
| :--- | :--- |
| 0.2–0.4 | TypeScript syntax; affine ownership with second-class borrows; one-shot effects; structural records with row polymorphism |
| 0.10 | Consolidated draft: Sync, user-handleable Io for deterministic simulation |
| 0.11 | The four-pillar core: one row calculus, handlers for everything, comptime layout |
| 0.12 | Shared mutation is an effect; implicitly open failure rows |
| 0.13 | Second-classness propagates; type-directed region inference |
| 0.14 | Append-only regions; first-class continuations; four standard effects |
| 0.15 | Universal class propagation; transparent borrows; scope-owned fibers |
| 0.16 | Tag unions without brackets; throw/try/catch and yield as effect syntax; nursery semantics |
| 0.17 | The rules a type checker needs: spawn and fork, effect rows as sets, catch closes its row |
| 0.18 | Complete ownership rules: results carry their arguments' borrows, reborrowing, tasks perform only Io and failures |
| 0.19 | `view struct`, `from` defaults, escaping closures capture by move, region handles, iteration chains, private fields |
| 0.20 | Scope bodies perform only Io and failures; containers hold owned values; no borrow stored through a borrow; first-class closures are Send |
| 0.21 | comptime templates, reflection and generated code; derivations requested with `impl I for T;`; JSON in Flyscript |
| 0.22 | Super-interfaces bind impls; derivations for primitives; exhaustiveness over nested patterns; `if (const pat = e)`; tuple indexing |
| 0.23 | Derived interfaces in the prelude and the operators through them; closure modes enforced; total floats; `iterMut` |
| 0.24 | Template structs; associated types in impls; `ParSplit` over a `Slice` view; `Soa`, `par` and `parReduce` in Flyscript |
| 0.25 | Calls through borrows follow closure modes; associated types and template instances checked for borrows; `if (let …)` |
| 0.26 | Contextual `match`/`handle`/`region`/`effect`; lists default to arrays; diverging branches; failures named for what failed |
| 0.27 | Channels close; tasks share strings; TypeScript's string methods |
| 0.28 | Continuations called as functions; several `with` clauses; expression arm bodies; `min`/`max` |
| 0.29 | `Cont<A, B, E>` again, not `Send`; escaping continuations borrow the arms' bindings; `defer` and `Drop` cannot fail |
| 0.30 | Borrows cannot outlive their scope; operation arguments lent to the arm; `Cont`'s row is the `handle`'s own; assignment drops; `while (const …)` |
| 0.31 | Copy parts bind by copy; `Box` borrows lend; literal parts lent into borrow slots; recursive aliases rejected |
| 0.32 | A yielded value is a result; `generate` written in Flyscript with one `unsafe` arm; open unions never enums |
| 0.33 | TypeScript's array and generator methods; strings interpolate raw in generic code; borrows of borrows collapse |
| 0.34 | Tasks move in scope-locals; closures own what they move in; `Mutex`; cloneable senders; `drain`; `Fail.capture` passes effects on |
| 0.35 | No result borrows an owned parameter; `Gen` items borrow what it holds; helper-started tasks cannot borrow |
| 0.36 | Escaping closures cannot capture region data; tasks cannot change what they borrow; drop order |

`review-round-*.md` are the design review rounds that produced 0.2–0.15; `programs-against-v0.13.md` is the program-writing exercise against what is now 0.13.
