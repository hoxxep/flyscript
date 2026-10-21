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

`review-round-*.md` are the design review rounds that produced 0.2–0.15; `programs-against-v0.13.md` is the program-writing exercise against what is now 0.13.
