v0.3 is close. Produce **v0.4** as one complete, self-contained document, with these changes. Treat it as a release candidate: every example must typecheck against the rules as written.

**1. New typing decision: structural records with row polymorphism; nominal declarations for abstraction.** This replaces "all types are nominal".
- `type` aliases of record and tuple types are **structural**, exactly as in TypeScript: `type Point = { x: f64; y: f64 }` is identified by its field names and types, laid out like the equivalent struct. Anonymous object literals and tuples are the same (this also makes the `{ profile, quota }` return in the v0.3 example legal; today it contradicts "all nominal").
- Functions over records are **row-polymorphic, with no width subtyping**: `function norm<R extends row>(p: readonly { x: f64; y: f64; ...R }): f64`. Monomorphization gives each concrete shape fixed offsets, so there is no runtime cost. Use the same row machinery as effect rows and say so; pick the syntax for row variables.
- `struct` and `enum` are **nominal and generative**: the way to declare an abstract type with invariants, `Drop`, `@layout`, or capability bounds (in type-theory terms, the existential pack, the same split SML makes between structural records and nominal datatypes).
- `interface` stays nominal with explicit `implements` and the orphan rule.
- Rationale to include: width subtyping would need runtime offset lookups, defeating unboxed layouts; row polymorphism gives the same flexibility statically.

**2. Remove `iso`, `recover` and `IsoArena`.** With affine ownership, second-class borrows and no shared-mutable pointer type (no `Rc<RefCell>`), every owned value is already isolated: nothing outside can alias its subgraph, so moving a `Box`/`Vec`/`Pool` root across tasks is already an O(1) pointer move. `iso` adds a capability, a block form and an allocator without adding safety. Define `Send` simply (owned, no `In<R, _>`, no non-`Send` fields), and freezing as `Arc.new(value)` with `T extends val`. If you disagree, show a concrete program that is unsafe without `iso`.

**3. Make `val` a constraint only.** It's currently both a type former (`val T`) and a constraint (`T: val`). Keep only the auto-trait bound (`T extends val`: transitively immutable, no interior mutability).

**4. TypeScript generics syntax.** Constraints use `extends`, not `:` and `+`: `<T extends Ord & Hash>`, `<effect E = []>`, `<region R>`.

**5. Fix the inconsistencies I found in v0.3:**
- `r.alloc` requires `T: Pod`, but `ParsedReq<R>` contains `In<R, str>`. State explicitly that `In<R, T>` and `In<R, T[]>`/`In<R, str>` are `Pod` (they are plain pointers with no `Drop`), so region structs can contain them.
- `-> paramName` for tied borrow returns clashes visually with arrows and isn't TypeScript. Pick a TS-reading form (e.g. `): readonly u8[] from buf`), and keep the "exactly one borrowed input ties automatically" default.
- The example applies `try` to `conn.read(...)` and `conn.writeStatus(...)`, which produce I/O errors, yet the handler only handles `Fail<HttpError>`, so `handleConnection` should fail to typecheck. Decide the std I/O error convention (`Result<T, IoError>`, or `uses Fail<IoError>`), give the signatures of every std function the example calls (`Socket.read`, `Socket.writeStatus`, `DbClient.fetchProfile`, `Region.copyUtf8`, `Async.scope`, `Scope.spawn`, `Fiber.join`), and make the example handle or declare every effect it performs.
- Static reuse "consume `Box<T>`, construct `Box<U>`" must require equal size *and* alignment. Say so.
- Define precisely when a `finally` arm runs relative to the abortive arm, the `return` arm, and a resumptive arm that drops its continuation without resuming.
- Specify cancellation of a fiber in `Async.scope` that is mid-way through a resumptive handler.

**6. Decide open question 1** (FFI stacks): `extern "C"` calls switch to the worker thread's native stack, as Go's cgo does, unless you have a better answer. Keep SIMD (`Simd<T, Lanes>`) open.

**7. Add two short sections:** (a) a one-page "Flyscript for TypeScript developers" table (what carries over unchanged, what means something different such as `const`, object literals, `interface`, and what is new); (b) a "Core calculus" sketch: the small set of typing judgments (ownership/borrow context, region context, effect row) that the whole language elaborates into, so a reader can see the design fits together.

Drop performance numbers that aren't guaranteed by the semantics (e.g. "<1 ms per function", "4 KB stacklets" belong in an implementation notes section, if anywhere).
