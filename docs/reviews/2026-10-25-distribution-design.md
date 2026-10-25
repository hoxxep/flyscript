# Actors on other machines: `std/node` — a design

A proposal, for review, for Erlang's distribution in Flyscript's terms. A program becomes a *node*. It publishes actors under names, and other nodes call them through typed addresses that work like local ones. The things Erlang hides are made visible. A message must be data that can cross a network, and the compiler checks that. A remote call can fail because the network did, and the type says so. Two nodes agree on a protocol before they exchange messages. Nodes authenticate each other with certificates, not a shared cookie, and a peer can reach only what was published to it. Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

This is the last of five designs that carry Erlang's strengths over, and it rests on the others. `2026-10-25-select-and-deadlines-design.md` gives `select`, `Io.within`, bounded channels and split sockets. `2026-10-25-actors-design.md` gives `Addr`, `Mailbox`, `ask` and the `Address` interface that local and remote addresses share. `2026-10-25-simulated-cluster-design.md` is how this design is tested, and `2026-10-25-observability-design.md` is how its connections are seen. It also uses two designs from other work. The codec design (`2026-10-25-codec-design.md`) gives `Encode`, `Decode` and CBOR, which messages are encoded with. The attributes design (`2026-10-25-attributes-design.md`) gives `@protocol`, which names a message type and its version. Examples use today's imports, and everything in `std/node` is a sketch.

## The design in brief

1. **A node is a scope.** `Node.start(config, body)` listens for peers, runs `body`, and stops the node when `body` returns, like any `Io.scope`. A node has a name that its certificate proves.
2. **Actors are published by name, and found by name and protocol.** `node.publish("kv", addr)` makes a local actor reachable. `node.lookup<Command>("b", "kv")` gives a `RemoteAddr<Command>`, once both nodes agree that the name speaks the protocol `Command` declares with `@protocol`.
3. **A message that crosses is `Portable`**, a derived interface. Its plain data is encoded by the codec, and a `Reply<R>` or `RemoteAddr<M>` inside it becomes a reference the other node can answer or call. Anything else (a `Mutex`, a `Socket`, a `Task`, a borrow, a closure) is a compile-time error that names the field.
4. **Remote calls fail by type.** `RemoteAddr<M>` implements the actors design's `Address<M, #Unreachable>`, so `ask` fails with `#Stopped | #Unreachable`. `#Unreachable` means the request may or may not have been handled, and the caller decides what that means.
5. **The guarantees are Erlang's, stated plainly:** at most once, in order between one node and one published actor, and no duplicates. A peer that doesn't answer heartbeats is down within `downAfter`, and every call waiting on it fails at that moment.
6. **No head-of-line blocking.** Each published actor gets credit from its node equal to the room in its mailbox, so a full mailbox slows its own callers and nobody else's. A large message is sent in fragments, so it doesn't hold up small ones.
7. **No remote code.** A peer cannot spawn, evaluate, or call anything but what was published to it. There is no hot code loading. Versions change with rolling restarts, and `@protocol(version, oldest)` says which versions can talk to each other.

---

## 1. What Erlang's distribution gets right, and wrong

**Right.** A process on another node is addressed like a local one: `Pid ! Msg`, `gen_server:call(Pid, Req)`, `monitor(process, Pid)`. Code written for one node runs across many. A node that goes down is a message (`nodedown`, or `'DOWN'` with `noconnection`), so failure is handled by the code that handles every other failure. Two messages from one process to another arrive in the order sent. The cost of all this is close to zero for the programmer.

**Wrong, or wrong for Flyscript.**

- **Any term can be sent**, so a message's type is checked by nothing, and a node on another version can send a shape that crashes the receiver.
- **Failure is hidden.** `Pid ! Msg` to a node that is down succeeds and the message vanishes. A `call` to it waits for its timeout. Waldo et al.'s *A Note on Distributed Computing* (1994) is about exactly this: the latency, partial failure and lack of shared memory that make remote calls different from local ones can't be hidden, only ignored.
- **The cookie.** Nodes share one secret, and a node that knows it can run any code on any other (`rpc:call(Node, os, cmd, [...])`). TLS distribution exists, but it is opt-in and rarely configured.
- **Full mesh.** Every node connects to every other by default, which limits clusters to a few hundred nodes.
- **One connection per pair of nodes**, and before OTP 22 a large message blocked every small one behind it. The mailbox a message lands in is unbounded, so a slow receiver fills memory instead of slowing its senders.
- **`global`**, the cluster-wide registry, is known to behave badly under partitions.

## 2. Nodes

```ts
// std/node.fly, sketch.

export type NodeConfig = {
  name: String;                   // what its certificate proves; how peers address it
  listen: u16;
  identity: Identity;
  peers: Discovery;               // where to find a peer by its name
  heartbeat: Duration;            // 1s unless set
  downAfter: Duration;            // 5s unless set: a peer silent this long is down
};
// How a node proves its name and checks its peers': TLS 1.3 both ways, each certificate naming
// its node and signed by `ca`. `#Insecure` is refused outside a simulated world unless the
// program is run with FLY_INSECURE_NODES set.
export type Identity = #Tls { cert: String; key: String; ca: String } | #Insecure;
// Where peers are: a fixed table, or a function asked each time a name is looked up.
export type Discovery = #Static(Vec<{ name: String; host: String; port: u16 }>) | #Dns { suffix: String };

export struct Node;
export type NodeErr = #BadIdentity(String) | IoErr;

impl Node {
  // Starts the node, runs `body`, and stops the node once `body` returns: its connections closed,
  // the calls waiting on them failed with `#Unreachable`.
  export function start<T, row E>(config: NodeConfig, body: once (node: readonly Node) => T uses Io, ...E): T uses Io, Fail<NodeErr>, ...E;
  export function name(self: readonly Self): str;
}
```

A node is structured, as everything else that runs tasks is. `Node.start` opens a scope. In it are the listener, a task per connection (split into a reader and a writer, using the select design's `socket.split`), and the heartbeat. `body` runs beside them. A node that ends ends its connections, and a panic in a connection's task ends that connection alone (§5.7): a peer that sends a message which trips a bug in the decoder loses its connection, not the node.

**Connections are made on demand.** A node connects to a peer the first time it looks something up there, and keeps the connection while it is used. There is no full mesh. A node of a thousand-node cluster has connections only to the peers it talks to.

**A peer's name is checked against its certificate**, both ways. A node that claims to be `b` but holds `c`'s certificate is refused. That needs server-side TLS and client certificates in `std/net`, which today has only `Socket.connectTls` (std.md §11): `Listener.bindTls(port, identity)` and `Socket.connectTlsAs(host, port, identity)`, through the libssl `connectTls` already uses.

## 3. Publishing and finding actors

```ts
// std/node.fly, sketch.

impl Node {
  // Makes `addr` reachable from peers as `name`, speaking `M`'s protocol, until the node stops or
  // `withdraw` is called. A name is published once.
  export function publish<M extends Portable>(self: readonly Self, name: str, addr: Addr<M>): void uses Io;
  export function withdraw(self: readonly Self, name: str): void uses Io;
  // The actor `peer` publishes as `name`, once both agree it speaks `M`'s protocol.
  export function lookup<M extends Portable>(self: readonly Self, peer: str, name: str): RemoteAddr<M> uses Io, Fail<#Unreachable | #NoSuchName | #Mismatch(Mismatch)>;
}

// Why two nodes did not agree on a protocol: different names, versions with nothing in common, or
// one version of different shapes.
export type Mismatch = #Protocol { ours: String; theirs: String } | #Versions { ours: [u32, u32]; theirs: [u32, u32] } | #Shape { version: u32; at: String };
```

**A protocol is a message type with a name and a version**, declared with an attribute of the attributes design:

```ts
import { protocol } from "std/node";

@protocol("kv", version = 3, oldest = 2)
export enum Command {
  #Get { key: String; reply: Reply<Option<String>> },
  #Put { key: String; val: String; @wire(default) ttl: Option<Duration> },   // new in version 3
}
```

`@protocol` goes on an `enum` or a `struct`, which are the declarations that carry attributes. A structural union like §A.6's `type Command = …` can't, because two equal structural types would then differ by an attribute (the attributes design, section 2). A program that turns an actor's message type into a protocol therefore declares it as an `enum`.

**Agreeing.** `lookup` sends the protocol's name, its range of versions (`oldest` to `version`) and a *shape*: a hash, computed at compile time over reflection, of each version's tags, fields and their types, by their names on the wire. The peer answers with its own. The two nodes then speak the newest version both support. If the names differ, or the ranges don't overlap, `lookup` fails with `#Mismatch`. If the same version has different shapes, which happens when someone changed a message and forgot to raise the version, it fails with `#Mismatch(#Shape { version, at })`, naming the first tag or field that differs. That catches at connect time the bug that takes an Erlang cluster down mid-upgrade.

**How versions coexist** is the codec's business. A field added in version 3 is `@wire(default)` and an `Option`, so version 2's encoding decodes with it empty. Version 2 ignores the field when version 3 sends it, because unknown keys are skipped unless `denyUnknown` is set. The protocol says which version is spoken. `@wire` says how one version reads another.

**There is no global registry.** Names belong to a node: `lookup("b", "kv")` asks `b`. Which node holds what (a shard's owner, a session's home) is the application's to decide, or a library's, over `lookup`. Erlang's `global` shows what goes wrong when the runtime decides it.

## 4. What a message may hold: `Portable`

```ts
// std/node.fly, sketch.

// What can go to another node. Derived for every type whose parts can: plain data by the codec,
// and the handles below as references the other node answers through.
export interface Portable extends Send {
  function put(self: Self, out: mut Outgoing): void;
  function take(input: mut Incoming): Self uses Fail<#BadMessage(String)>;
}
impl<comptime T: Type> Portable for T { … }                       // by reflection, below
impl<R extends Portable> Portable for Reply<R> { … }               // a reply owed across the connection
impl<M extends Portable> Portable for RemoteAddr<M> { … }          // an address that works from anywhere
```

The derivation walks the message's type, as the codec's does. A part that has `Encode` and `Decode` and holds no handle is encoded by the codec, in CBOR, the codec design's binary format, with that design's limits on size and depth. A `Reply<R>` or a `RemoteAddr<M>` is replaced by a reference to it (next paragraphs). Every other part stops the derivation with an error at the field, through the attributes design's `attrs.fail`:

```
error: `Job` cannot go to another node: its field `log` is a `Sender<String>`, which only reaches tasks of this program.
  Send a `RemoteAddr<M>` of an actor that receives the lines instead.
```

`put` takes `self` by move because a message is moved into the connection, as a local message is moved into a channel. A `Reply` can't be copied, so moving the message is what lets its reply become the other node's to answer.

**A `Reply` across a connection.** When node `a` puts a `Reply<R>` into a message for `b`, the reply stays in `a`, in a table of the connection, under a number, and the number is what is sent. On `b`, `take` makes a `Reply<R>` whose `send` encodes the answer and sends it back with that number. Dropping it unsent sends a note that it was dropped. On `a`, the answer goes to the real `Reply`, and the note drops it. So the actors design's rule, that a request dropped unanswered fails its caller with `#Stopped`, holds across machines. If the connection is lost, `a` drops every reply in its table, and the `ask`s waiting on them fail with `#Unreachable`, because the address knows its connection is gone (section 5). `Reply` gains a third kind of state for this, owed over a connection, beside sent and unsent. Its type doesn't change.

**A `RemoteAddr` across a connection** is its node's name and its actor's name, so a node can pass the address of an actor on a third node, and its receiver can call it, connecting to the third node if it needs to. A node passes the address of one of its own actors with `node.share(name)`, which gives a `RemoteAddr` of something it published. A `RemoteAddr` that points to the node it is used on works locally, without a connection.

**What doesn't cross, and why.** A `Mutex`, an `Atomic` or a channel is shared memory or a queue inside one program. A `Task` or `Fiber` is a handle to a task of this program. A `Socket` or a file is a descriptor of this process. A borrow can't be stored, let alone sent. A closure is code. Erlang can send a fun, which runs only if the other node has the same module loaded at the same version. Here a node can call only what another node published.

## 5. Remote addresses

```ts
// std/node.fly, sketch.

// An actor on some node, maybe this one: `Clone` and `Send`.
export struct RemoteAddr<M>;

impl<M extends Portable> RemoteAddr<M> {
  // Sends `m`, waiting while the actor's node has given no credit for it (section 6); `false` once
  // its peer is known to be down or the actor is gone. Delivery is not confirmed: `true` means sent.
  export function tell(self: readonly Self, m: M): bool uses Io;
  export function ask<R extends Send>(self: readonly Self, make: once (r: Reply<R>) => M): R uses Io, Fail<#Stopped | #Unreachable>;
  // Ends once the actor is gone (`#Stopped`) or its node is down (`#Unreachable`).
  export function watch(self: readonly Self): Watch;
}
impl<M extends Portable> Address<M, #Unreachable> for RemoteAddr<M>;

export struct Watch;
impl Watch { export function wait(self: readonly Self): #Stopped | #Unreachable uses Io; }
impl Source for readonly Watch { type Event = #Stopped | #Unreachable; }   // for `Io.select`
```

**`#Unreachable` is honest.** It means the node couldn't be reached, or stopped answering, or the connection was lost after the request was sent. In the last case the request may have been handled. A caller that retries must make the request safe to repeat. This is true of every remote call in every system, and the type says so where the call is made, not in a footnote.

**A deadline is `Io.within`**, as for a local call. When it passes, the waiting `ask` unwinds, its `Pending` is dropped, and the answer, if it arrives, is dropped too. The deadline is not sent with the request. That is an open question.

**`watch` is Erlang's monitor.** It ends when the actor's mailbox ends (its node sends a note when it does) or when its node is down. It is a `Source`, so an actor can wait for its next message or for the peer it depends on to fail, in one `select`.

**Delivery guarantees.**

- *At most once.* A message is sent once and never resent. If the connection is lost, what was in flight may be lost. There are no duplicates, because nothing is retried below the application.
- *In order between a node and an actor.* Messages that one node sends to one published actor of another arrive in the order they were sent, if they arrive. This is Erlang's ordering between two processes, widened to a node, because a node's messages to one actor go over one connection.
- *A peer is down within `downAfter`.* Every node sends a heartbeat each `heartbeat` on each connection it has. A peer not heard from for `downAfter` is down. Its connection is closed, every call waiting on it fails with `#Unreachable`, every `Watch` on its actors ends, and the next use of one of its addresses tries to connect again, with backoff.

## 6. Flow control

A connection carries the messages for every actor its peer publishes. If the reader of a connection waited for room in one actor's full mailbox, every other actor's messages would wait behind it. That is head-of-line blocking, the problem an unbounded mailbox hides by growing. Instead, as HTTP/2 does for its streams, each node grants its peers *credit* per published actor, in messages, equal to the room in the actor's mailbox. A `tell` or `ask` spends one and waits while there is none. The receiving node returns credit as the actor takes messages. The reader never waits, and a slow actor slows its own callers, across the network, as a bounded local mailbox does.

**Large messages are fragmented.** A message whose encoding is larger than 64 KB is sent in fragments, between which the writer sends other messages' fragments in turn. A large reply doesn't hold up a heartbeat, so a node sending a megabyte isn't declared down. Erlang added the same in OTP 22.

## 7. An example

```ts
import { Node, NodeConfig, NodeErr, Mismatch } from "std/node";
import { mailbox, serve } from "std/actor";
import { Command, Kv } from "./kv";

// Node `store` serves the key–value actor; node `web` calls it.
export function store(config: NodeConfig): void uses Io, Fail<NodeErr> {
  Node.start(config, (node) => {
    const [kv, inbox] = mailbox<Command>("kv", 1024);
    node.publish("kv", kv);
    serve(Kv { store: HashMap.new() }, inbox);
  });
}

export function web(config: NodeConfig, listener: mut Listener): void uses Io, Fail<NodeErr | #Unreachable | #NoSuchName | #Mismatch(Mismatch)> {
  Node.start(config, (node) => {
    const kv = node.lookup<Command>("store", "kv");
    serveHttp(listener, (req) => {
      const name = try {
        Io.within(Duration.ms(200), () => kv.ask((reply) => #Get { key: req.query("user").toString(), reply }))
      } catch (e) {
        match (e) { #Stopped | #Unreachable | #TimedOut => #None }   // degrade: answer without the store
      };
      …
    });
  });
}
```

The web node's handler doesn't know whether `kv` is local or remote except by its failures, and it handles every one. In the simulated cluster design's test, `store` and `web` are two nodes of one world. A partition between them makes the handler answer without the store, and the test checks that it does, under thousands of seeds.

## 8. Supervision across nodes

A supervisor restarts children it can run: functions in its own program (std/supervise). It can't run a child on another machine, so there are no remote children. Each node supervises its own actors, and a node that depends on a remote actor watches it and decides what its loss means. That might be degrading, as above, or failing over to another node's copy, or panicking so its own supervisor restarts it once the peer is back. Erlang can link processes across nodes, so that a crash on one kills its partner on another. In practice that is used to tie a client's lifetime to a server's, and a `Watch` in a `select` does the same.

Where actors should run, and moving them when a node is lost, is cluster management: consistent hashing, leases, a membership protocol. It is the application's or a library's, built on `lookup`, `watch` and the simulated cluster to test it.

## 9. The wire

A connection is TLS 1.3 over TCP. After the handshake, each side sends a hello with its node's name, the design's wire version and its heartbeat. Then frames follow: a length, a kind, a number (an actor's, a reply's or a lookup's) and a payload. The kinds are `lookup` and its answer, `tell`, `ask` (which carries a reply's number), `answer` and `dropped` (for a reply), `credit`, `gone` (an actor's mailbox ended), `heartbeat` and `fragment`. Payloads are CBOR, as the codec design writes it. A frame that doesn't decode, a message that doesn't decode as its protocol's type, or a frame larger than the limit (16 MB unless set) closes the connection and is logged with the peer's name. Calls waiting on it fail with `#Unreachable`.

## 10. How it is built

1. **Server TLS and client certificates in `std/net`**: `Listener.bindTls`, `Socket.connectTlsAs`, through libssl, natively. In a simulated world, `#Insecure`, with names checked by the world's network instead of certificates.
2. **`@protocol` and `Portable`**: after the attributes and codec designs. The derivation, its error for each kind of part that can't cross, and the shape hash.
3. **Replies owed over a connection**: the third kind of state in `Reply`, in each runtime.
4. **`std/node`**, in Flyscript: the connection's reader and writer tasks, framing, lookup and agreement, `tell`, `ask`, `watch`, heartbeats and backoff.
5. **Credit and fragments.**
6. **Tests**, in the simulated cluster: an `ask` across a partition fails with `#Unreachable` within `downAfter`; one across a crash fails at once once the connection is reset; a slow actor slows only its own callers; two versions agree on the newer they share; a changed message without a new version is refused with the field named; a malformed frame closes only its connection.
7. **Benchmarks**, added to `bench/`: the round trip of an `ask` between two nodes on one machine, and the rate of `tell`s, against Erlang's distribution and against gRPC (`tonic`), each over TLS.

## 11. What was weighed

- **Location transparency in the types**, one `Addr<M>` for local and remote, whose `ask` always fails with `#Unreachable` too. Every local call would then handle a failure that can't happen. The actors design's `Address<M, X>` lets code be written once for both and still lets local code skip `#Unreachable`.
- **gRPC.** A node could be a gRPC server and a `RemoteAddr` a client stub. gRPC has no references in messages, so no replies to pass along and no addresses of third parties, and no monitors. Its schemas live in `.proto` files outside the language. A program that must talk to gRPC services uses the codec design's protobuf format and `std/http`. Between Flyscript nodes, a protocol is a Flyscript type.
- **Sending closures**, as Erlang sends funs. That needs both nodes to have the same code at the same version, and it makes every node able to run whatever a peer sends it. Publishing named actors gives the same reach with a list of what may be called.
- **Hot code loading.** Erlang keeps two versions of a module and moves each process's state with `code_change`. Without a garbage collector, a process's state has no runtime shape that a new version could reinterpret, and the language would have to keep old and new code side by side with their types. Rolling restarts, protocol versions and the simulated cluster's mixed versions (its open question 2) cover what upgrades need. A node that must hand its state to its successor can send it, since state that is `Portable` is a message like any other.
- **A global registry.** See section 3.
- **Exactly-once delivery.** It can't be had without the application's help: idempotent requests, or a log both sides keep. At most once is what the network gives, and it is what is promised.

## Open questions

1. **Deadlines across nodes.** Should an `ask` inside `Io.within` send the time remaining, so the remote actor can stop working on a request nobody is waiting for? gRPC does this, measuring from receipt so clocks needn't agree.
2. **Streams.** A `Sender<T>` can't cross, but a stream of results is common: a query's rows, a log tail. A `Portable` remote sender, with credit as in section 6, would be the remote counterpart of a channel. Is it worth a type of its own, or is it a `RemoteAddr` of an actor that takes `#Item(T) | #End`?
3. **More than one connection per pair**, for throughput across many cores. Order is then kept per actor, not per node.
4. **Encryption inside a trusted network.** TLS costs a little on every byte. Should a cluster be able to choose authentication without encryption, or is that a choice nobody should have to make correctly?
5. **Inspection across nodes**: whether `fly inspect` should reach a node's peers through its connections (the observability design's open question 2).
