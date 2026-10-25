# Actors: `std/actor`, typed addresses and calls that fail by type — a design

A proposal, for review, for what OTP's `gen_server` is to Erlang: one way to write a task that owns state and serves requests, and one way to call it. The call has a deadline, fails by type when the server is gone, and works the same whether the server is local or on another node. Flyscript already has the parts: a channel as a mailbox, `Reply<T>` for the answer (§A.6), `std/supervise` for restarts. What it lacks is the shape around them. Each call is three lines, a call to an actor that has crashed panics the caller, and no call can be given a limit. Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

It builds on `2026-10-25-select-and-deadlines-design.md`, which gives bounded channels, `Io.select` and `Io.within`. `2026-10-25-observability-design.md` reads the names and statistics this design gives an actor, and `2026-10-25-distribution-design.md` gives remote addresses the same face as local ones (section 7). Examples use today's imports, and everything in `std/actor` is a sketch.

## The design in brief

1. **A mailbox is made apart from the actor that serves it.** `mailbox<M>(name, capacity)` gives an `Addr<M>`, which is `Clone` and `Send`, and a `Mailbox<M>`. Whoever holds the mailbox can serve it. The mailbox outlives the task that serves it, so messages sent while a supervisor restarts the actor wait for the new one. Erlang loses them.
2. **`addr.ask(make)`** sends a request and waits for its answer. `make` builds the message around a `Reply<R>` it is given: `kv.ask((reply) => #Get { key, reply })`. The call fails with `#Stopped` if the mailbox is gone, or if the request was dropped unanswered, as it is when the actor panics while handling it. It never panics the caller. `addr.tell(m)` sends without waiting for an answer.
3. **No deadline is built into `ask`**: `Io.within(d, () => kv.ask(…))` gives one, and the two failures join as `Fail<#Stopped | #TimedOut>`.
4. **`serve(state, mailbox)`** runs the loop every actor writes, over an `Actor` impl's `handle`. It also answers what the observability design asks every actor: its name, its queue, how many messages it has handled, and its state if the state can be shown.
5. **Mailboxes are bounded by default.** `tell` waits while the mailbox is full, which gives backpressure, and `tryTell` gives the message back instead.
6. **Calls are typed both ways.** The reply's type is the `R` of the `Reply<R>` in the message, so `ask` gives exactly what the actor answers, with no casts and no pattern match on an untyped reply.

---

## 1. Actors today

§A.6 is a whole actor, and it is short:

```ts
export function kv(inbox: readonly Receiver<Command>): void uses Io {
  let store = HashMap.new<String, String>();
  for (const cmd of inbox) {
    match (cmd) {
      #Get { key, reply } => reply.send(store.get(key).cloned()),
      #Put { key, val }   => store.insert(key, val),
      #Stop               => break,
    }
  }
}
```

Calling it is where things go wrong (`tests/run/kv_actor.fly`):

```ts
const [r1, a1] = Reply.new<Option<String>>();
tx.send(#Get { key: "a".toString(), reply: r1 });
println(`${a1.wait()}`);
```

- **Three lines a call**, and two names to make up for each.
- **A crashed actor panics its callers.** If `kv` panics while handling the `#Get`, the `Reply` it held is dropped unsent, and `wait` panics (std.md §3, "Replies"). If the actor has ended, its `Receiver` is dropped, `send` drops the message and the `Reply` in it, and `wait` panics again. Either way a bug in one actor becomes a panic in every task that calls it, and those may be tasks the bug never touched: connections whose handlers did nothing wrong. Erlang's `gen_server:call` exits the caller too, but the caller can catch the exit, and a supervisor expects it. Here nothing can catch a panic (§5.7), so the caller has no way to say "the cache is down, answer without it".
- **No limit.** A `kv` stuck behind a slow request keeps every caller waiting with it.
- **Restarting it loses the mailbox.** The natural supervised form makes the channel inside the child, so a restart makes a new channel that no caller has an address for. The working form keeps the receiver outside the supervisor and lends it to each start (`std/supervise`'s `ctx`), and nothing in the library says to.

## 2. Mailboxes and addresses

```ts
// std/actor.fly, sketch.

// Where an actor's messages go: `Clone` and `Send`, so any task may hold one; copies are one
// mailbox. Dropping every `Addr` ends the mailbox, as dropping every `Sender` ends a channel.
export struct Addr<M>;
// The receiving end: one actor serves it at a time, and it outlives the actor that does.
export struct Mailbox<M>;

// A mailbox for at most `capacity` messages, named for what the runtime reports of it.
export function mailbox<M extends Send>(name: str, capacity: usize): [Addr<M>, Mailbox<M>];

impl<M extends Send> Addr<M> {
  // Sends `m`: waits while the mailbox is full; `false`, dropping `m`, if the mailbox is gone.
  export function tell(self: readonly Self, m: M): bool uses Io;
  // Sends `m` if there is room now; else gives it back.
  export function tryTell(self: readonly Self, m: M): #Sent | #Full(M) | #Gone(M) uses Io;
  // Sends the request `make` builds around a reply, and waits for the answer.
  export function ask<R extends Send>(self: readonly Self, make: once (r: Reply<R>) => M): R uses Io, Fail<#Stopped>;
}
```

A `Mailbox` is a bounded `Receiver` with a name, and an `Addr` is a `Sender` with `ask`. They are separate types because the observability design counts what flows through a mailbox and reads its name. They also give remote addresses something to match (section 7).

**`ask` in full.** It makes a `Reply<R>` and its `Pending<R>`, calls `make` with the reply, `tell`s the message, and waits on the pending half. It fails with `#Stopped` in two cases: the `tell` found the mailbox gone, or the reply was dropped unsent. That needs one addition to `std/sync`, a `Pending` that reports a dropped reply instead of panicking:

```ts
impl<T> Pending<T> {
  export function wait(self: Self): T uses Io;              // unchanged: panics if the reply is dropped unsent
  export function take(self: Self): Option<T> uses Io;       // `#None` if it was
}
```

A dropped reply covers every way a request can be lost without an answer. The actor panicked while holding it, and the unwinding dropped it. The actor ended with the request still queued, and dropping the mailbox dropped it. Or the actor's code dropped it by mistake, in a `match` arm that forgot to answer. In the first case the caller wakes the moment the actor's unwinding reaches the reply, which is what Erlang's call gets by monitoring the server for the length of the call. Here ownership gives it for free.

**What `make` may do.** It is a `once` closure, so the message can move what the caller owns into it: `kv.ask((reply) => #Put { key, val, reply })` moves `key` and `val`. It performs no effects, so a request is built completely before anything is sent.

**A deadline is code around the call.**

```ts
const name = try {
  Io.within(Duration.secs(5), () => profiles.ask((reply) => #Lookup { user, reply }))
} catch (e) {
  match (e) { #Stopped | #TimedOut => user.toString() }   // the cache is down or slow: answer without it
};
```

A request that times out stays in the mailbox, and when the actor answers it, the answer is dropped, because the `Pending` went with the cancelled call. That matches gen_server, whose late replies are discarded. An actor that should not do work nobody is waiting for can check, before it starts, whether the asker has given up: `reply.wanted()`, true until the `Pending` is dropped. That costs a load of the reply's state.

## 3. `serve` and `Actor`

The loop of §A.6 is the same in every actor, and the parts that differ are the state and what each message does to it:

```ts
// std/actor.fly, sketch.

// What an actor does with each message: goes on, or stops. `serve` gives back the state it ends with.
export type Next = #Continue | #Stop;

export interface Actor {
  type Msg extends Send;
  function handle(self: mut Self, m: Self.Msg): Next uses Io;
}

// Serves `inbox` with `state` until `handle` says stop or every address is gone, and gives the
// state back. One actor serves a mailbox at a time: a second `serve` of it panics.
export function serve<A extends Actor>(state: A, inbox: readonly Mailbox<A.Msg>): A uses Io;
// The same, also calling `tick` each `every`, at a steady beat.
export function serveTicking<A extends Actor & Tick>(state: A, inbox: readonly Mailbox<A.Msg>, every: Duration): A uses Io;
export interface Tick { function tick(self: mut Self): Next uses Io; }
```

The key–value store, as an `Actor`:

```ts
export type Command =
  | #Get { key: String; reply: Reply<Option<String>> }
  | #Put { key: String; val: String };

export struct Kv { store: HashMap<String, String> }

impl Actor for Kv {
  type Msg = Command;
  function handle(self: mut Self, m: Command): Next uses Io {
    match (m) {
      #Get { key, reply } => reply.send(self.store.get(key).cloned()),
      #Put { key, val }   => { self.store.insert(key, val); },
    }
    #Continue
  }
}
```

`#Stop` is gone from the message type. An actor stops when every address to it is dropped, as a channel ends, and a supervisor stops it with `Task.cancel`, so a message that only means "stop" is needed only by an actor that must stop itself.

**What `serve` adds over a `for…of`.** It selects over the mailbox and a second, internal mailbox for the runtime's questions, using the select design's `Io.select`. The observability design's `fly inspect` asks an actor for its name, queue length, handled count, the time since it last finished a message, and, if `A` is `Show`, its state, rendered between messages and never during one. In Erlang these are the `sys` messages every OTP process answers, and they are why `observer` can show any gen_server's state. An actor written by hand with `for…of` still works. It is just invisible to those questions, as a hand-written Erlang process is.

**What it does not add.** There is no `handle_call`/`handle_cast`/`handle_info` split. A request is a message that holds a `Reply`, and a notification is one that doesn't, so one `match` covers both. There is no `init` callback either: the state is built before `serve` is called, by ordinary code.

## 4. Under a supervisor

The mailbox is made outside the supervisor and lent to each start of the child, so it outlives every restart:

```ts
export function main(): void uses Io {
  const [kv, inbox] = mailbox<Command>("kv", 1024);
  Io.scope((s) => {
    s.spawn(() => supervise(inbox, #OneForOne, [
      { name: "kv".toString(), restart: #Permanent, start: (inbox) => {
        serve(Kv { store: HashMap.new() }, inbox);
      } },
    ], { restarts: 5, within: Duration.secs(10) }));
    serveHttp(kv.clone());   // handlers call `kv.ask(…)`; a restart is invisible to them
  });
}
```

When `kv` panics:

1. the message it was handling is dropped with its reply, so that one caller gets `#Stopped` at once;
2. its state is dropped, and with it whatever the state owned;
3. the messages behind it stay in the mailbox, and their senders keep waiting;
4. the supervisor starts it again with a fresh state, serving the same mailbox, and the waiting requests are answered.

Erlang does the first two the same way and loses the third: a restarted gen_server is a new process with an empty mailbox, and its registered name points to it only once it has started. Everything sent between the crash and the restart goes to a dead process and is lost. Here callers see one failed call, not a gap.

**A message that crashes the actor every time** is a poison message. Since the mailbox is kept, the restart limit is what stops the cycle: the actor panics, restarts, panics on the next message, and so on until the limit, and then the supervisor panics to its own supervisor. That is right when the state was the problem. It is wrong when the message was. `serve` can therefore be given `poison = n`: a message that was being handled when the actor panicked `n` times in a row is set aside, its reply dropped, and the panic logged with the message if it is `Show`. Whether that belongs in `serve` or in a policy of the supervisor's is an open question.

## 5. Backpressure and deadlocks

A mailbox's bound is required: `mailbox(name, capacity)`. The capacity is the most requests the actor may fall behind by. When it is reached, `tell` and `ask` wait, which slows callers down to the actor's pace. A caller that would rather fail fast puts its call inside `Io.within`, or uses `tryTell`.

Two actors that each `ask` the other can deadlock. That is a deadlock with any bound, and with none, because each waits for an answer only the other can give. Two actors that `tell` each other can deadlock only once both mailboxes are full. Both are found in a simulated world, which reports a deadlock when nothing can run and nothing sleeps. The rules that avoid both are the ones Erlang users learn:

- an actor answers through `Reply`, which never waits;
- an actor that must ask another from inside `handle` gives the call a deadline;
- an actor that tells an actor that may tell it back uses `tryTell`.

## 6. Many actors, found by key

Erlang's `Registry` and `via` tuples find a process by a key: one actor per user session, per room, per shard. There is no registry here. The typed form is a map, which a program already has:

```ts
const rooms: Mutex<HashMap<RoomId, Addr<RoomMsg>>> = Mutex.new(HashMap.new());
```

with `std/actor` giving one helper, `Directory<K, M>`. It starts an actor for a key the first time the key is used, under a supervisor the directory owns, and forgets the key when the actor ends. A global registry by name, as Erlang's `register/2` is, would hand out addresses whose message type nothing checks. The distribution design names services on a node, with a type fingerprint, because across machines a name is needed. Within a program, an address is passed like any other value.

## 7. Local and remote, one interface

The distribution design gives `RemoteAddr<M>`, an address of an actor on another node. Code that calls an actor should not care which it has, but the failures differ: a remote call can also fail because the node can't be reached, and the caller must handle that. The row calculus states both at once:

```ts
// std/actor.fly, sketch: anything an actor can be called through, failing with `#Stopped` and
// whatever else `X` holds.
export interface Address<M, row X = []> {
  function tell(self: readonly Self, m: M): bool uses Io;
  function ask<R extends Send>(self: readonly Self, make: once (r: Reply<R>) => M): R uses Io, Fail<#Stopped | ...X>;
}
impl<M extends Send> Address<M> for Addr<M>;
// In std/node:  impl<M extends Portable> Address<M, #Unreachable> for RemoteAddr<M>;

function fetchName<row X, A extends Address<Command, X>>(kv: readonly A, user: str): Option<String> uses Io, Fail<#Stopped | ...X> {
  kv.ask((reply) => #Get { key: user.toString(), reply })
}
```

Code written against `Address` fails with `#Stopped` when given a local `Addr`, and with `#Stopped | #Unreachable` when given a remote one. Its caller, which knows which it passed, handles exactly that. This is Erlang's location transparency with the difference made visible: the same code serves both, and the type says which failures each can have. (Catching `#Stopped` inside generic code while passing `X` on is not possible: a `catch` closes its row (§5.4). Generic code passes its failures on, and the caller that knows the type handles them.)

## 8. How it is built

All of `std/actor` is library code over `std/sync`, the select design's `select`, `within` and bounded channels, and `std/supervise`. Its only runtime support is what the observability design asks of every mailbox (a name and two counters) and `Pending.take`, which is `wait` with a flag instead of a panic. `examples/kv_actor.fly` and `tests/run/kv_actor.fly` become the `Actor` form. New tests: a caller of an actor that panics gets `#Stopped`, the messages behind it are answered after the restart, a timed-out call's late answer is dropped, a `Show` state is rendered between messages, and two actors that `ask` each other are reported as a deadlock in a simulated world. A message through `ask` costs one `Reply` beyond §A.6, with no extra allocation if `Reply`'s state is inline in the message. `bench/tasks.sh`'s round trips gain an `ask` row.

## 9. What was weighed

- **Untyped calls**, Erlang's `call(Pid, Request)` and `{reply, Reply, State}`. A tagged union of messages, each holding a `Reply<R>` of its own `R`, gives every request its own reply type with no casts. It is the shape Akka Typed and `ractor` arrived at.
- **A method per request**, generated: `kv.get(key)` instead of `kv.ask((reply) => #Get { key, reply })`. `comptime` computes names of fields and tags but not of functions (§7.2), and a `Command` union says nothing about which fields are arguments. The `make` closure is one line, and its types are inferred.
- **`ask` with a timeout argument**, as gen_server's does. `Io.within` gives the same limit around any code, and a call made inside a request handler already within a deadline inherits it, which a fixed argument would not.
- **A panic in the caller when the actor dies**, as now. It turns one actor's bug into a panic in every caller, and nothing can catch it. `#Stopped` is a failure the caller can handle, and the type makes it handle it or pass it on.
- **Restarting with the last state**, as some actor libraries offer. A panic may leave the state half changed, which is why a `Mutex` is poisoned (§6.2). A restart begins from a fresh state, as Erlang's do.
- **Selective receive.** See the select design, section 9. An actor that must take one kind of message first is given two mailboxes.

## Open questions

1. **Poison messages:** a policy of `serve`'s, of the supervisor's, or neither?
2. **`reply.wanted()`:** is it worth one more state in `Reply`? The alternative is to put a deadline in requests whose work is expensive.
3. **Should a call made inside `handle` get a default deadline**, a lint short of one, or neither?
4. **`hibernate`**, Erlang's way to shrink an idle process to its state. A parked task is already only its live frame (step 15), so the question is whether an idle actor's state should be compacted, which only the actor knows how to do.
