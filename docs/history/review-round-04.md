v0.4's decisions are right: keep all of them. Produce **v1.0-draft**, the consolidated spec, with these fixes:

1. **Restore what v0.4 dropped.** v0.4 is not self-contained: it lost v0.3's sections on closures and capture kinds (shared / `mut` / `once`, second-class closures), effects and handlers (with examples), `Result` vs `Fail` guidance, structured concurrency semantics, `par for` + `@layout(soa)` with its typing rule, `comptime` (with phase separation and the `Type` example), modules (ES modules, no cycles), FFI (`extern "C"`, `@layout(c)`, raw pointers, `unsafe`), panics, and the purity/allocation rule. The draft must contain everything from v0.3 and v0.4, reconciled with v0.4's decisions (no `iso`; `val` as a constraint; `extends`; `from`).

2. **`Pod` bug.** §6.1 says structural records/tuples are `Pod`; they're only `Pod` when every field is `Pod` (a record holding a `String` is not). Same for `val` and `Send`: state that all three are derived structurally for records and tuples.

3. **Define `Io` properly.** `effect Io {}` has no operations, so nothing explains how `Socket.read` suspends or who handles `Io`. Decide: either `Io` has primitive operations (submit/await completion, clock, spawn) that the runtime's root handler implements and **users may re-handle** (which enables v0.1's deterministic-simulation testing, which I want kept as a headline feature: a test harness handles `Io` with a seeded in-memory scheduler and virtual clock), or explain why not. Show a short deterministic-test example.

4. **Example ergonomics.** The example has to read like code people would write, not a typing exercise:
   - Remove the explicit `Async.scope<{...}, [Fail<HttpError>]>` and `Fiber<...>` annotations: bidirectional inference must infer `T` and the effect row from the closure body. If something genuinely can't be inferred, say which rule prevents it.
   - Every fallible call is `try x.mapErr((_) => HttpError.BackendError)`. Add a principled conversion so `try` maps errors automatically: e.g. `try` converts `Err(e)` through a `From<E>` interface implemented by the target error type, or a `try expr else HttpError.BackendError` form. Pick one.
   - `const _ = conn.writeStatus(...)` silently discards a `Result`. Decide whether `Result` is must-use, and give the idiom for deliberately ignoring it.

5. **Small precision fixes.** In T-Handle, `conn` is a `mut` parameter (a borrow in Γ), not an owned binding in Θ; state the rule for re-borrowing a borrowed parameter inside an abortive arm. Define `Θ_out` in T-Region. Say whether `Drop` can be implemented for structural records (it shouldn't: only nominal types).

6. **Close with** (a) a one-paragraph summary of the language's thesis and the five laws restated in final form, (b) a short "Rejected alternatives" list (GC, `iso`/`recover`, width subtyping, multi-shot continuations, Hindley-Milner, `async`/`await`, lifetime parameters) with one sentence each on why, and (c) open questions: only SIMD unless you find another that is genuinely undecidable now.
