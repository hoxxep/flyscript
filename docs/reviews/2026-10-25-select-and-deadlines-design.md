# Waiting for one of several things: `select`, deadlines and bounded channels — a design

A proposal, for review, for the three ways a task cannot wait today. It cannot wait for the first of several things to happen: a message on either of two channels, or a message or a timer. It cannot put a limit on how long something may take. And it cannot be made to slow down when it sends faster than its receiver takes, because every channel is unbounded. Erlang has the first two as `receive … after`, and lacks the third: an unbounded mailbox is how an Erlang node runs out of memory. Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

This is the first of five designs that carry what Erlang and OTP do well over to Flyscript. The others are `2026-10-25-actors-design.md` (`std/actor`: typed addresses, `ask` and `tell`, mailboxes that outlive a restart), `2026-10-25-observability-design.md` (task names, a running program's tasks listed, stalls reported), `2026-10-25-simulated-cluster-design.md` (many nodes in one deterministic simulation) and `2026-10-25-distribution-design.md` (`std/node`: actors on other machines, with typed failures). Every one of them needs what this one adds. The actors design needs deadlines and bounded mailboxes, and distribution needs `select` and split sockets.

Examples use today's imports. Wherever a feature already exists, the code parses today. Everything new is a sketch.

## The design in brief

1. **`Io.select(sources)`** waits until one of several sources is ready and takes exactly one event from it. The sources are written as a record, `{ cmd: inbox, tick: Io.at(next) }`. The result is the union of tags with the same names, `#cmd(Option<Command>) | #tick`, so a `match` says what to do with each. A record is unordered, so `select` has no order either: when several sources are ready, natively it picks one at random, and against a simulated world the seed picks.
2. **The sources** are a `Receiver<T>`, which gives the message taken, or `#None` once the channel has ended. A `Task` gives how it ended. A `Pending<T>` or a `Fiber<T>` gives nothing, which means its `wait()` or `join()` will now return at once. A `Deadline` from `Io.at(instant)` or `Io.after(d)` gives nothing too. Each source is lent to `select`, so a source that isn't chosen loses nothing.
3. **`rx.tryRecv()`** takes a message only if one is already there. It is for a source that must be served first when it is ready, since `select` has no priority.
4. **`Io.within(d, body)`** runs `body` and stops it if it is still running after `d`. It cancels the body where it stands, at its next `Io` operation, and fails with `#TimedOut`. A scope inside the body has its tasks cancelled with it. A deadline nests, and the nearest one wins.
5. **`bounded<T>(n)`** makes a channel that holds at most `n` messages. On it, `send` waits while the channel is full, and `trySend` gives the message back instead of waiting. `channel<T>()` keeps its meaning, unbounded.
6. **`socket.split()`** gives a read half and a write half, which two tasks can own. A connection that is read and written at once, the commonest case of waiting for two things, then needs no `select` on a socket.

---

## 1. What a task can wait for today

A task waits in exactly one place at a time. It can call `rx.recv()`, `pending.wait()`, `fiber.join()`, `task.wait()`, `Io.sleep(d)`, or `Task.any(tasks)`. The last is the only wait for several things, and it waits only for tasks (§6.1). The simulated scheduler shows this directly: a task record has one `waitKind` and one `waitId` (`selfhost/rt/sched.fly`, `type Task`). `WAIT_ANY` is the one exception, a list of tasks.

That leaves three common programs that cannot be written directly:

- **An actor that also keeps time.** A server that sends a heartbeat every second while it serves requests has to wait for a request or the next second. Today a second task must sleep and send `#Tick` into the same channel. That forces the ticks into the actor's message type, and the actor can no longer tell a tick that was due from one that waited behind a hundred requests.
- **Two channels.** An actor with a control channel (`#Stop`, `#Reload`) beside its work channel can't wait on both. So it merges them by making one type of both, with a forwarding task per channel.
- **A limit on a wait.** `pending.wait()` waits until the actor answers. If the actor is stuck in a loop, or waiting on something that never comes, the caller waits forever, and so does everything waiting on the caller. Erlang's `gen_server:call` waits five seconds by default and then fails, and that one default prevents a whole class of outages. Flyscript has no way to say "five seconds".

The third problem is different. `tx.send(v)` "never waits for the receiver" (std.md §3). A producer faster than its consumer fills memory until the process is killed. The overload never shows up as slowness the producer could react to. This is the commonest way Erlang systems fail in production. A mailbox's length is the first thing `recon` users look at, and Flyscript should not copy it.

## 2. `Io.select`

```ts
// The prelude, sketch.

// Something a task can wait for among others; what waiting for it gives once it is ready.
// Only the runtime's types are sources, as only `i64` and `bool` are `AtomicWord`s.
export interface Source {
  type Event;
}
impl<T> Source for readonly Receiver<T> { type Event = Option<T>; }   // the message, taken; `#None`: ended
impl Source for readonly Task { type Event = TaskEnd; }
impl<T> Source for readonly Pending<T> { type Event = void; }          // `wait()` now returns at once
impl<T> Source for readonly Fiber<T> { type Event = void; }            // `join()` now returns at once
impl Source for Deadline { type Event = void; }

// A point on the monotonic clock that `select` can wait for: `Copy`, as an `Instant` is.
export struct Deadline { private at: Instant }

impl Io {
  export function at(t: Instant): Deadline;
  export function after(d: Duration): Deadline uses Io;   // `Io.now()` plus `d`

  // Waits until one of `sources` is ready, takes one event from it, and says which it was.
  // A scheduling point, and a place a cancellation is delivered, as any wait is.
  export function select<comptime R: Type>(sources: R): Ready<R> uses Io;
}

// For `{ a: A; b: B }` where each is a `Source`: `#a(A.Event) | #b(B.Event)`, a tag with no
// payload for a `void` event.
export comptime function Ready(R: Type): Type;
```

An actor that keeps time, written with it:

```ts
export function kv(inbox: readonly Receiver<Command>, peers: readonly Peers): void uses Io {
  let store = HashMap.new<String, String>();
  let next = Io.after(Duration.secs(1));
  while (true) {
    match (Io.select({ cmd: inbox, beat: next })) {
      #cmd(#Some(#Get { key, reply })) => reply.send(store.get(key).cloned()),
      #cmd(#Some(#Put { key, val }))   => store.insert(key, val),
      #cmd(#Some(#Stop)) | #cmd(#None) => break,
      #beat => {
        peers.heartbeat();
        next = Io.after(Duration.secs(1));
      },
    }
  }
}
```

**Why a record.** A `select` names its sources, and the names go with the events. The row calculus already has both halves: a record type whose fields are sources, and a tag union whose tags are events. `Ready` turns one into the other field for field, so `Io.select({ cmd: inbox, beat: next })` has type `#cmd(Option<Command>) | #beat`. The `match` on it is checked for exhaustiveness like any other. Leaving out `#beat` is the usual error, and so is a misspelled tag.

`Ready` needs one thing `comptime` doesn't do yet. It must generate the tags of a union type, as `comptime for` already generates the fields of a record type (§7.2):

```ts
export comptime function Ready(R: Type): Type {
  type { comptime for (const f of fieldsOf(R)) { | eventTag(f.name, f.type.Event) } }
}
```

where `eventTag` gives `#[name]` for a `void` event and `#[name](E)` otherwise. The tags of a union are a row, as a record's fields are, so this adds a place `comptime for` may generate items, not a new idea. If it is not wanted, section 9 gives the alternative.

**The sources are lent.** `select` borrows each source for as long as it waits and takes the event only from the one it chooses. A message on a channel that wasn't chosen stays there, and the next `select` or `recv` finds it. This is why `Pending` and `Fiber` give `void`, not their value. Taking the value would consume the handle, so a handle lent to a `select` that chose something else would have to be either consumed or not, and the type couldn't say which. Instead the event says the handle is ready, and the following `wait()` or `join()` returns at once, with no scheduling point.

**Exactly one event.** When `select` returns `#cmd(#Some(m))`, `m` was taken from `inbox` and nothing was taken from any other source. On many cores this needs care. `Receiver.recv` takes `readonly Self`, so tasks of one scope may share a receiver, and a message seen on a channel may be taken by another task before this one claims it. Section 6 says how the runtime keeps the guarantee. The proof states it as a theorem (section 7).

**No order.** A record has no order: `Type.info` gives a record's fields, and the codec design notes that a record "has no order". So `select` cannot prefer its first source, as Rust's `biased;` select does. When more than one source is ready, the native runtime picks one uniformly at random, as Go does, so a busy channel cannot starve a quiet one. Against a simulated world the seed picks, so a schedule in which the tick always loses to a message is one of the schedules tested. A source that must win when it is ready is checked first, without waiting:

```ts
while (true) {
  if (const #Some(c) = control.tryRecv()) { … continue; }
  match (Io.select({ control, work })) { … }
}
```

`tryRecv` gives `#Got(T) | #Empty | #Ended`. Like every channel operation it is a scheduling point. That keeps a loop of `tryRecv`s inside the simulator's control, but it does not make polling a way to wait. In a simulated world the clock moves only when no task can run (§6.4), so a task that polls a channel and never waits keeps the clock still, and a peer sleeping until a time that never comes never runs. That run is reported as a stall, not hidden (observability design, section 5).

**What a deadline is.** `Io.after(d)` is a value, a point on the monotonic clock. Making one waits for nothing. A `Deadline` is `Copy`, and one that has already passed is ready at once. In a simulated world it is a point on the virtual clock, and a task that waits for one is a sleeper the clock can jump to. A loop that remakes its deadline each time round, as `kv` does above, keeps a steady beat. `Io.sleep(d)` is `Io.select({ d: Io.after(d) })`, though it stays its own operation.

## 3. `Io.within`: a limit on how long

```ts
impl Io {
  // Runs `body`. If it is still running once `d` has passed, it is cancelled where it stands, at
  // its next `Io` operation, as a task is (§6.1), and `within` fails with `#TimedOut` once it has
  // unwound. A deadline already set around it that comes sooner wins.
  export function within<T, row E>(d: Duration, body: once () => T uses Io, ...E): T uses Io, Fail<#TimedOut>, ...E;
  export function until<T, row E>(t: Deadline, body: once () => T uses Io, ...E): T uses Io, Fail<#TimedOut>, ...E;
}

const name = Io.within(Duration.secs(5), () => {
  const [reply, answer] = Reply.new<Option<String>>();
  kv.send(#Get { key: user.toString(), reply });
  answer.wait()
});
```

**It is a cancellation, scoped.** A task's cancellation is delivered at its next `Io` operation and unwinds it to its root (§6.1). Here a cancellation is delivered the same way and unwinds only to the `within` that set it, which turns it into the failure `#TimedOut`. Everything between the two runs its cleanup, with the guarantees of §5.6. A `defer` or destructor running at the deadline finishes, its own `Io` included, so a deadline never interrupts cleanup. In Trio's terms this is a cancel scope, and in Go's it is a context with a deadline that every blocking call obeys. The difference is that nothing has to pass the context around, because the runtime knows the deadline of the code it is running.

**Deadlines nest.** A task keeps a stack of the deadlines its code is inside. An `Io` operation checks the nearest one, the soonest, which is one comparison with the clock when the stack is not empty and none when it is. If the nearest has passed, the operation unwinds to the `within` that set it, even if an outer one has passed too. That `within` fails with `#TimedOut`, and the code around it decides what to do, because it is inside the outer deadline, which is now delivered at its next `Io` operation.

**A scope inside it is cancelled with it.** If the body opens a scope, the scope's tasks run on other fibers, possibly other cores. They have no stack of their own deadlines from the body. They don't need one. When the deadline unwinds the body out of `Io.scope`, the scope's tasks are cancelled, as step 13 made every scope do when its body unwinds, and `Io.scope` waits for them to finish their cleanup before the body goes on unwinding. A scope's tasks therefore stop at their next `Io` operation after the deadline, which is what Go's derived contexts give, without passing anything.

**What it does not do.** It cannot stop pure code, for the reasons that rule out stopping a task in a loop that never waits (§6.1; roadmap step 13). A body stuck in `while (true) {}` is never cancelled, and `within` never returns. The observability design reports such a task as a stall. Its type says so too: a body that performs nothing but pure code needs no `within`.

**Its type.** The body may perform any effect, `...E`, and `within` performs it too, since the body is just code of the same task, not a task of its own (§6.1 rule 4 is about tasks). The one effect `within` adds is `Fail<#TimedOut>`, joined to the body's failures by union, so `Fail<#NotFound>` from the body and the deadline's failure together are `Fail<#NotFound | #TimedOut>` with no conversion (§5.4).

## 4. Bounded channels

```ts
// std/sync, sketch.

// A channel that holds at most `capacity` messages: on it, `send` waits while it is full.
export function bounded<T extends Send>(capacity: usize): [Sender<T>, Receiver<T>];

impl<T> Sender<T> {
  // Unchanged on an unbounded channel. On a bounded one: waits while the channel is full, then
  // puts `v` in it; `false`, dropping `v`, once the receiver is gone, before or while it waits.
  export function send(self: readonly Self, v: T): bool uses Io;
  // Puts `v` in the channel if there is room now; else gives it back.
  export function trySend(self: readonly Self, v: T): #Sent | #Full(T) | #Gone(T) uses Io;
}
```

A bounded channel is the same `Sender<T>` and `Receiver<T>`, with a capacity in its state. Code that takes a `Sender<T>` doesn't need to know which kind it has. A send that waits is still `Io`, as every send already is, so no type changes.

**What waiting for room gives.** A producer faster than its consumer slows to the consumer's pace, because its `send` waits. If the producer is a connection's task, the connection stops being read, the kernel's buffers fill, and the client slows down. That is TCP's backpressure carried through the program. A producer that would rather shed load than wait uses `trySend` and decides what to do with a `#Full(v)`: drop it and count it, answer `503`, or send it elsewhere.

**Deadlocks it can cause, and how they are found.** Two actors that send to each other over full bounded channels both wait forever. That bug cannot happen with unbounded channels, which trade it for running out of memory. In a simulated world it is found as any deadlock is: nothing can run and nothing sleeps, so the scheduler reports it (`deliverDeadlock`, `selfhost/rt/sched.fly`). A waiting send is one more kind of wait it knows. The actors design says how to avoid it: an actor replies through `Reply`, which never waits, and sends with `trySend` to an actor that may be sending to it.

**The default.** `channel<T>()` stays unbounded. Every program in the repository uses it, and an unbounded channel is the right tool between two tasks of one scope whose pace is already tied, such as a reader and a writer of one file. The actors design gives mailboxes a bound by default. Whether `channel()` should eventually require one is an open question.

## 5. A socket in two halves

```ts
// std/net, sketch.
export struct ReadHalf;
export struct WriteHalf;
impl Socket {
  // The socket's two directions, each owned on its own; the connection closes once both are gone.
  export function split(self: Self): [ReadHalf, WriteHalf];
}
impl ReadHalf {
  export function read(self: mut Self, buf: mut u8[]): usize uses Io, Fail<IoErr>;
}
impl WriteHalf {
  export function write(self: mut Self, bytes: readonly u8[]): void uses Io, Fail<IoErr>;
  // Sends the end of the stream: the other side reads `0`. The read half keeps reading.
  export function shutdown(self: mut Self): void uses Io;
}
```

A connection between two nodes, or a WebSocket, is read and written at once. Bytes arrive from the peer, and messages arrive from the program to be written. With only `select`, one task would wait for "a message, or the socket readable", which needs readiness as a source. The runtime does wait for readiness underneath (`epoll` and `kqueue`, in `selfhost/runtime.c`), so it could offer one. But `std/net`'s API is operations, each of which completes: `read` gives bytes. A "readable" event followed by a `read` would be the one source whose event takes two steps, with the socket's state free to change between them. Instead the socket splits, and two tasks own the halves. One reads and dispatches, and the other receives from a channel and writes. This is how tokio and Go are used in practice. It fits ownership exactly: each half is `mut` to its task alone, and neither is shared. In a simulated world a split socket is two views of one simulated connection.

## 6. How it is built

**The simulated scheduler** (`selfhost/rt/sched.fly`, `src/eval/sched.rs`, `selfhost/runtime.js`). A task's wait becomes a set instead of one `waitKind`/`waitId` pair: the channels it would take from, the tasks it would see end, and the soonest deadline. `WAIT_ANY` becomes the case of a set of tasks only. `wake` already scans the blocked tasks, and it now tests membership in the set. As the scheduler runs one task at a time, the task it wakes takes its event in the same step, so the guarantee of one event is immediate. The deadline joins the sleepers that `pass` searches for the earliest wake time. `Io.within`'s stack of deadlines is the task's own, in its record, so it needs nothing from the scheduler except the clock. The seed chooses among ready sources with the same generator that chooses among ready tasks, on every back end, so a seed gives the same schedule in the interpreter, JavaScript and native code.

**On many cores** (`selfhost/rt/mt.fly`, the monitors in `selfhost/runtime.c`). A channel today is a monitor: a lock held for a few instructions and a queue of the tasks waiting under it. `select` does what Go's `selectgo` does. It takes the locks of every channel among its sources in address order, so two `select`s cannot deadlock on each other. Then it takes the first ready event it finds, starting at a random source. If none is ready, it puts a *waiter* for itself on each channel's queue and parks. The waiter is one record shared by all the queues, with a word that the first waker claims by compare-and-swap. A waker that loses the race skips the waiter, and the task removes its waiter from the other queues as it resumes. A `Task`, `Pending` or `Fiber` source is a waiter on that record's wait list, and a deadline is a timer in the wheel that already serves `sleep` (`wheel_link`), claiming the same word. A bounded channel's monitor has a second queue, of senders waiting for room.

**What it costs.** A `select` with none of its sources ready costs a lock and a waiter per source. A `recv` and `send` that use no `select` stay as they are, measured by `bench/tasks.sh`'s round trips. `bench/tasks.sh` gains a `select` of two channels and a timer, measured against `tokio::select!`. The bar is the one the channel round trips already meet (docs/performance.md): no slower than tokio.

**`Io.within`** keeps its stack of deadlines in the task's record. A `within` pushes a deadline and its catch point. Every `Io` operation compares the stack's top with the clock when the stack is not empty. A task parked past its deadline is woken by the deadline's timer, as a `select` is. Unwinding uses the catch points step 13 built (`fly_try`, landing pads, JavaScript's `finally`), and the cancellation stops at the `within`, as a failure stops at its `try`.

## 7. The proof

λ-fly's channels are handlers that own the messages not yet received (§6.2, §9.5). A receive is one operation, which moves a value from that handler to the task. `select` is an operation over several handlers at once, which moves a value from exactly one of them. The theorem has two parts. The first is the ownership invariant as it stands, since a message is still owned by one channel or one task at every step. The second is new: a `select` step removes a message from one channel only, and the others are unchanged. The choice is nondeterministic, like the scheduler's, and the theorem already holds under every schedule, so it holds under every choice. `Io.within` adds no rule. Its cancellation is a failure, raised at an operation and caught at the `within`, which λ-fly already has (`throw` and `catch` over `Fail`). A bounded channel's `send` is a receive's mirror: an operation that waits while the handler's queue is full.

## 8. What changes, and in what order

Each step leaves every test green on every back end.

1. **`Io.within`, `Deadline`, `Io.at` and `Io.after`**, which need nothing from channels: a stack of deadlines in the task record and the catch points step 13 built. Tests: a call that times out, nested deadlines, a scope cancelled by its body's deadline, cleanup that finishes after the deadline.
2. **Bounded channels and `trySend`, `tryRecv`**: a capacity in `Chan`, a queue of waiting senders, and the deadlock report naming a waiting send.
3. **`socket.split`.**
4. **`Io.select`**: the union types `comptime` builds, `Source`, the wait set in the three simulated schedulers, and waiters in the native monitors. Tests: each kind of source, two `select`s sharing a channel on many cores under the thread sanitizer, and a seed under which the deadline loses to a message every time.
5. **The proof**: `select` in λ-fly, and the theorem that it takes one event.
6. **The spec and std.md**: §6.1, §6.2, §6.3 and std.md §3 and §11.

## 9. What was weighed

- **Arms as closures**, `select((s) => { s.recv(rx, (m) => …); s.after(d, () => …) })`, as Rust's `futures::select` builders do. Every arm would capture what the actor changes, `store` in `kv`, as `mut`, and two closures may not both hold a `mut` borrow of one value. That is the ownership rule this language exists for. A `select` that returns a value to `match` on has no such problem: the arms are the `match`'s, and only one runs.
- **Positional sources**, `Io.select2(a, b)` giving `#First(A) | #Second(B)`, and `select3`. They need nothing new from `comptime`, but the names are lost and arity is capped. This is the fallback if `comptime` should not generate union tags.
- **A `select` statement in the syntax**, as Go's is. A library function over the row calculus does the same job and keeps the language's core small, which is law 5's point.
- **Erlang's selective receive**, `receive` with patterns, which scans the mailbox for the first message that matches. It is untyped, and with a long mailbox it is quadratic, because every receive scans the messages it skipped before. The Erlang compiler special-cases the commonest pattern, a reply matched by a fresh reference, to avoid the scan. Separate channels, each with its own message type, give the same choice of which message to take next, typed and at constant cost.
- **Readiness as a source**, so a socket could be selected. The runtime's `epoll` and `kqueue` loop could report it, but `std/net` exposes operations that complete, and a readiness event would be the one source whose event is not the thing itself (section 5). It would also tie the API to readiness, where §6.3 is written so that a completion-based runtime such as `io_uring` remains possible. Splitting the socket covers the case that needs it.
- **Deadlines as an argument to every wait**, `recv(timeout)`, `wait(timeout)`, as Java does. Each API would grow, and a function that waits twice would have to divide its time by hand. `Io.within` puts one deadline around any code, the waits inside it included.
- **Bounded by default.** It would be safer, but it breaks every program that uses `channel()` between tasks whose pace is already tied, and it makes deadlocks out of programs that are correct today. The actors design bounds mailboxes, where an unbounded queue does the harm.

## Open questions

1. **Sending in a `select`**, as Go's `select` can: wait until there is room on a bounded channel, or until a message comes. The value would move into the `select` and, if another source were chosen, would have to come back in the event. A `#[name](T)` event could carry it back. Is the case common enough? `trySend` and a second task cover it.
2. **Should `channel()` take a bound?** Once the actors library has a bound, every remaining `channel()` can be checked for whether it needs one.
3. **A deadline across nodes.** An `ask` to another node inside `Io.within` could send its deadline with the request, so the remote actor's work is cancelled when the caller has given up. That is gRPC's deadline propagation. The distribution design leaves it open. It needs clocks that agree, or durations measured from receipt.
4. **`Ready` in `comptime`.** Are tags of a union type the right first case of `comptime` generating union types, or should `comptime` be able to build every kind of type? And a tag takes its field's name as written, so `{ cmd: inbox }` gives `#cmd`, a lowercase tag where the library's are capitalized: should `Ready` capitalize it, or should the fields be written `{ Cmd: inbox }`?
