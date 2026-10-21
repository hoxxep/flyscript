v0.2 is a big step up: the decisions are mostly right (affine-by-default, second-class borrows, one-shot continuations, Pod-only regions, bidirectional inference after comptime). Keep all of those. But a close reading finds contradictions and gaps. Produce **v0.3** as one complete, self-contained document (not a diff), fixing each of these with a decision:

**Contradictions**
1. §2.4 lets a region struct hold `readonly T` borrows that outlive `R`, but §5.1 rule 2 forbids borrows in struct fields. Pick one (I'd keep the ban).
2. The grammar doesn't match the prose: `CapabilityMod` lists only `iso`/`val`; return types may be borrows "tied to a single input borrow" but the grammar has no way to express which one; `r: region R` is used as a parameter but `region R` isn't a type; `R.allocSlice(len, init)` vs `r.allocSlice(raw[0..8])`; handler arms are typed `ParamList` but the examples are untyped. Make grammar and examples agree exactly.
3. Effect names: `Io`, `AsyncIo` and `Async` all appear for overlapping things, and the example re-declares `Fail` instead of importing it. Define one standard set (e.g. `Io`, `Fail<E>`, and where `scope`/`spawn` live) in a "standard effects" subsection.
4. Refinement solving is "Presburger" in one place and "Fourier-Motzkin / Simplex" in another. Say precisely what the decision procedure is.
5. `val T` vs `Arc<val T>`: the table, the lattice and `freeze` use them inconsistently. Define both precisely: which is a borrow, which is an owned handle, and whether `val` can appear inside an owned struct field. Drop "marks its heap pages read-only" unless you really mean `mprotect`.

**Gaps that must be specified**
6. **Creating `iso` values.** "Within an `iso` block" refers to a construct that doesn't exist. Specify how an `iso T` is constructed and proved isolated (e.g. a Pony-style `recover { ... }` block whose free variables must be `iso`/`val`/Send-able), and how to mutate it and move it on.
7. **Tier 3 / IsoHeap GC is undefined.** With affine `Box` as the only owning pointer, nothing can make a cycle outside a region, so there is nothing for a mark-compact pass to collect. Either define a GC'd pointer type (e.g. `Gc<T>` confined to one actor's heap, not Send, with its rules) or cut actor-heap GC from the core and say long-lived cyclic state uses index-based pools (`Pool<T>` + `Handle<T>`). I lean towards cutting it for simplicity, but decide and justify.
8. **Regions × fibers.** Regions live on "the current thread's region stack", but fibers suspend and interleave on a thread, so LIFO region order breaks as soon as two fibers each open a region. Regions must belong to the fiber (or be segment-allocated). Also state whether child fibers may allocate into a parent's region (I'd say no: read-only access only).
9. **Handlers × borrows.** In the example, the `Fail` arm uses `conn` while the body still holds a `mut` borrow of `conn`. State the rule: a handler arm may use a value the body has borrowed only if the arm cannot resume (abortive arm), or the borrow must be passed explicitly. Also add return/`finally` clauses to handlers if you need them.
10. **Closures.** With second-class borrows, a closure that captures a borrow must itself be second-class (it can't escape, be stored or be returned). Specify closure kinds (consume-once / mutate / shared, like FnOnce/FnMut/Fn, but inferred), which ones `spawn` and `par for` accept, and how escaping closures capture (move only).
11. **Allocation and purity.** v0.1 had an `Alloc` effect; v0.2 silently dropped it. Decide: is heap allocation an effect? Can a `par for` body or a pure function allocate? What about OOM, integer overflow, divide-by-zero and out-of-bounds when refinements aren't used: panic (abort or unwind?), or `Fail`?
12. **Methods and impls.** Where do methods live, how is `self` written (`self: readonly Self`?), and how do call sites mark borrows (you used `conn.read(mut rawBuf)`; make that the rule, or not)? `impl I for T` isn't TypeScript; choose a TS-feeling form and keep the orphan rule.
13. **Strings.** Add `str` (borrowed UTF-8) vs `String` (owned), and type string literals. `Log.info("...")` currently can't typecheck against `readonly u8[]`.
14. **Errors.** Say when to use `Result<T, E>` vs `Fail<E>`, and give the conversion in both directions (a `try`-style operator or std functions).

**Syntax: make it more TypeScript**
15. No Rust-isms: `[0u8; 512]`, `3.14159f32`, `400u16`, `Shape.Circle(r)`-style paths are fine, but numeric literal suffixes are not; literals should be typed from context by bidirectional checking, with `as` for explicit conversion. Pick a TS-like fixed-array initializer.
16. Struct literals: §4.2 claims TS object-literal syntax `{ x, y }` but the example uses `ParsedReq { ... }`. Pick one rule (e.g. `{ ... }` when the expected type is known, `ParsedReq { ... }` otherwise).
17. Resolve the `<` generic-call ambiguity (`a < b > (c)`): state the disambiguation rule as TS does.
18. Settle `const` vs `let`: `const` is a non-reassignable, non-mutable owned binding and `let` is mutable? Say so.

**Open questions**: decide #2 now (interfaces carry an effect row parameter defaulting to empty, or something better) and #3 (no nonlinear refinements; provide 2-D slice/stride types so indexing never needs multiplication proofs). Keep the open-questions list to genuinely undecidable items.

Finally, re-check the full example against every rule in the spec and fix anything it violates; add a short "Rationale" line under each major decision.
