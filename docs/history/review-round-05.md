This is converged. One last round: produce **v1.0**, identical to v1.0-draft except for the changes below. Keep every section; don't shorten or drop anything.

1. **Missing `Sync` rule (soundness).** Fibers spawned in `Async.scope` and `par for` iterations may run on different worker threads while sharing `readonly` borrows. If `T` has interior mutability that isn't thread-safe, sharing `readonly T` across threads is a data race. The example already relies on this: `DbClient.fetchProfile(self: readonly Self)` performs I/O, so `DbClient` must contain a mutable connection pool behind `readonly`. Decide:
   - Which interior mutability exists (I suggest only `Atomic*`, `Mutex<T>` and runtime-provided handles like `DbClient`'s pool, with no non-atomic `Cell`), and
   - Add a derived marker trait (call it `Share`, or `Sync` if you prefer the familiar name) with the rule: `readonly T` may be captured by `s.spawn` closures and `par for` bodies only if `T extends Share`. Add it to §6.1, the `Async.scope` and `par for` typing rules, the core calculus, and the `Send` relationship (`T extends Share` iff `readonly T` is `Send`).
   - Reconcile `val` with it: does `val` imply `Share`? (It should.)
2. **`Async.scope` vs `Io.runScope`** duplicate each other. Make `Async.scope` the std wrapper over one `Io` operation and say so, or remove one.
3. **`Io` operations and borrows.** `submitRead(fd, buf: mut u8[])` lends a buffer to the kernel across a suspension. State that the fiber's `mut` borrow stays locked until completion, and that cancelling the fiber must cancel or wait for the in-flight operation before the buffer's owner can be dropped (the io_uring cancellation hazard).
4. Mark the document **v1.0** and add a one-line changelog at the top summarizing v0.1 → v1.0.
