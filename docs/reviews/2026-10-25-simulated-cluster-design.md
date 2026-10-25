# Many nodes in one simulation: partitions, crashes and clocks, by seed — a design

A proposal, for review, to let one test run a whole cluster: several nodes, each running real Flyscript code, on a simulated network that delays, splits and partitions, with crashes that lose what was not synced, clocks that drift, and every choice made by a seed. A failing seed fails the same way every time it is run, on every back end. FoundationDB was built this way, and TigerBeetle and others since. It is how distributed systems get past the bugs Jepsen finds in everything else. Erlang has nothing like it: its tools (Concuerror, PropEr's state machines, Jepsen against a running cluster) explore some interleavings or test the real thing slowly. Flyscript is in an unusually good position to have it, because every interaction with the outside world is already the `Io` effect (law 2), and one handler of `Io`, the simulated world, already answers all of them (§6.4). Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

It builds on the unit tests design (`2026-10-25-unit-tests-design.md`), whose `@test(world = W, seeds = n)` runs a test against a world under many seeds. It answers that design's second open question, a world in the program, because a cluster needs one. It is one of five designs that carry Erlang's strengths over: `2026-10-25-select-and-deadlines-design.md`, `2026-10-25-actors-design.md`, `2026-10-25-observability-design.md`, whose traces explain a failing seed, and `2026-10-25-distribution-design.md`, whose nodes this design tests. Examples use today's imports, and everything in `std/sim` is a sketch.

## The design in brief

1. **A world in the program.** `Sim.world(w, body)` runs `body` against a simulated world of its own, with its own scheduler, clock, seed and network, on one thread. Many worlds run at once in one process, on every core, so `seeds = 1000` costs a thousand worlds, not a thousand processes.
2. **Nodes are code.** `c.node(name, env, start)` starts a node in the world: `start` is an ordinary function that `uses Io`, the same one the program runs in production, given `env`, which is data. A node has an address on the simulated network, a file system of its own, and a clock of its own, and every task it spawns belongs to it.
3. **A network that misbehaves the way networks do.** Connections are TCP's: reliable and ordered within one connection. Each delivery is delayed by the seed, reads return what has arrived split at the seed's choice of places, and what crosses different connections arrives in the seed's order. A partition holds what is in flight, and a connection held past its timeout is reset on both sides.
4. **A crash is power lost.** `c.crash(n)` ends each of a node's tasks as a dropped continuation. Its memory is freed exactly once, as §9.5 proves, but no cleanup's `Io` happens, so there is no last message and no flush. What it wrote and didn't `sync` is lost. `c.restart(n)` runs `start` again over the disk as it survived.
5. **Faults come from a test's script and from the seed.** A test can partition, crash, heal and skew at chosen moments. The world can also do all of these at random, at rates the seed draws, so each seed is a different mix of faults ("swarm testing").
6. **What a cluster did can be checked.** The test is a client of the cluster, and it records its operations as a history. `std/test`'s `linearizable(history, model)` checks the history against a sequential model, as Jepsen's Knossos and Porcupine do.

---

## 1. The world today

A simulated world (§6.4) is the runtime's root handler of `Io`, chosen when a program starts from `FLY_WORLD` or a test's header lines. It holds files, incoming requests, a database of profiles and quotas, and *peers*: each `host:port` the program may connect to, with the bytes it sends back (`src/eval/world.rs`, `peers: HashMap<String, Vec<u8>>`). Faults are one number, the percentage of I/O operations that time out (`fault_percent`). The scheduler runs every task on one thread, chosen at each scheduling point by the seed, and the clock jumps to the next sleeper's wake time when nothing can run. A run is reproducible exactly, in every implementation.

That is enough to test one program against scripted services. It is not enough to test a distributed system, for three reasons:

- **A peer is a canned reply.** It cannot be the other half of a protocol: a Raft follower, a replica that streams a log, a node that answers differently after a partition.
- **The only fault is a timeout, uniformly at random.** The bugs distributed systems actually have come from structured faults: one link down and the rest up, a node that is slow but not dead, a crash between a write and its `fsync`, a clock that runs fast, a partition that heals with messages still in flight.
- **One world per process.** The unit tests design runs each world test in a run of its own because a world is a property of a process. That works, but it makes a thousand seeds a thousand processes, and it makes a cluster impossible, because a cluster is several programs in one world.

## 2. A world in the program

```ts
// std/sim.fly, sketch.

// What a world holds at its start, and how it misbehaves: the unit tests design's `World`, from
// `std/test`, with the network's and the disks' behavior added (section 4 and section 5).
import { World } from "std/test";

impl Sim {
  // Runs `body` in a new simulated world on this thread: its own scheduler, clock and network,
  // seeded by `w`. The tasks `body` starts are the world's; nothing in it reaches the machine.
  // Returns once `body` has and every task in the world has ended.
  export function world<T extends Send>(w: World, body: once () => T uses Io): T uses Io;
  // The seed of the world this code runs in, if it runs in one.
  export function seed(): Option<u64> uses Io;
}
```

**How it runs.** `Sim.world` runs a simulated scheduler (`selfhost/rt/sched.fly`'s `Sched`, which today runs a whole program) inside the task that called it. The task drives the world's tasks one at a time, as the program-wide simulator does now, and doesn't give its worker back to the machine's runtime until the world ends. A world's tasks are state machines like any others, so a world is only its scheduler's state and its tasks' frames. Two worlds share nothing, so the machine's runtime can run one per worker, and the unit test runner's `seeds = n` becomes `n` tasks, each calling `Sim.world` with its seed.

**What a world contains.** Everything its tasks perform goes to the world. Its `Io` handler is the world, not the machine, and that is where the guarantee comes from. §6.1 rule 4 already says a task performs only what is handled where it runs. A task started inside a world runs where the world is the handler, so it can no more reach the machine's file system than a task can reach its parent's region. Data parallelism inside a world (`par`, `join`) runs on the world's thread, as it does in today's simulator: it is pure, so its result doesn't depend on where it runs.

**What it leaves to the program-wide world.** `FLY_WORLD` and the header lines stay, for whole-program tests in `tests/`, and they become `Sim.world` around `main`.

## 3. Nodes

```ts
// std/sim.fly, sketch.

// A node of the simulated cluster: `Copy`, a name for it in the controls below.
export struct Node { private n: u32 }

// The world's cluster: the nodes in it, and the controls a test has over them and their network.
export struct Cluster;

impl Sim {
  // The cluster of the world this runs in: panics outside a world, saying a cluster is simulated.
  export function cluster(): Cluster uses Io;
}

impl Cluster {
  // Starts a node called `name`, its address on the network, running `start(env)`. `env` is data,
  // what a configuration file would hold: it can be encoded, so it can share nothing with the test
  // or another node. `start` runs again, over the same `env` and what its disk kept, on `restart`.
  export function node<C extends Encode & Decode>(self: readonly Self, name: str, env: C, start: (env: readonly C) => void uses Io): Node uses Io;

  // Ends the node at once, as power lost (section 5).
  export function crash(self: readonly Self, n: Node): void uses Io;
  // Cancels the node's tasks, as `Task.cancel` does: they run their cleanup, with its `Io`.
  export function stop(self: readonly Self, n: Node): void uses Io;
  // Starts a crashed or stopped node again: `start(env)`, over its disk as it survived.
  export function restart(self: readonly Self, n: Node): void uses Io;
  // Waits until the node's tasks have all ended, and says how its root task ended.
  export function wait(self: readonly Self, n: Node): TaskEnd uses Io;

  // Cuts every link between `side` and the rest; `cut` one link, both ways; `heal` every cut.
  export function partition(self: readonly Self, side: readonly Node[]): void uses Io;
  export function cut(self: readonly Self, a: Node, b: Node): void uses Io;
  export function heal(self: readonly Self): void uses Io;
  // Ends the chaos of section 6: heals every cut, restarts every crashed node, and draws no more faults.
  export function calm(self: readonly Self): void uses Io;
  // Each delivery on links to and from `n` takes between `min` and `max`, by the seed.
  export function slow(self: readonly Self, n: Node, min: Duration, max: Duration): void uses Io;
  // Moves the node's wall clock by `by`, and sets the rate its clocks run at, in parts per million.
  export function skew(self: readonly Self, n: Node, by: Duration): void uses Io;
  export function drift(self: readonly Self, n: Node, ppm: i32): void uses Io;
}
```

**A node's tasks.** `start(env)` runs as the node's root task. Every task it spawns, and every task they spawn, belongs to the node. Each task's record carries its node, copied from its spawner's, as the observability design's parent is. When a node's task performs `Io`, the world answers as that node: its files, its listeners, its clock, its side of a partition.

**A node shares nothing.** Two nodes are different machines, so they must not share memory. `env` is `Encode & Decode` (the codec design's interfaces), which are exactly the types that could have come from a file or across a network: no `Mutex`, `Atomic`, channel, `Task`, `Arc` or borrow of the test's state. `start` is a closure, and could still capture a `Mutex` declared in the test. So inside a world, every channel, mutex and atomic records the node it was made on, and an operation on one from another node's task panics, naming both nodes. That check costs a comparison, made only in simulated worlds. A static rule would be better, and the open questions ask for one.

**The test is a node too.** The test's own body, and every task it spawns, belongs to a node called `test`, with an address on the network like the others. A test drives the cluster as a client would: it connects to nodes, sends them requests and reads their answers, through the same `std/net` or `std/node` code a real client uses.

**The same code in production.** `start` is the function the program's `main` calls with its configuration read from a file. Nothing in a node knows it is simulated. Nothing is mocked: the node's sockets, files and timers are the world's because the world is the handler of its `Io`.

```ts
import { Config, run, leadersByTerm } from "../examples/raft";

@test(world = World.empty(), seeds = 2000)
function oneLeaderPerTerm(): void uses Io {
  const c = Sim.cluster();
  const peers = ["a", "b", "c"];
  let nodes: Vec<Node> = Vec.new();
  for (const p of peers.iter()) { nodes.push(c.node(p, Config.local(p, peers), run)); }
  Io.sleep(Duration.secs(2));
  c.partition([nodes[0]]);
  Io.sleep(Duration.secs(5));
  c.heal();
  Io.sleep(Duration.secs(5));
  // Asked as a client would ask, from the test's own node; each entry a term and its leaders.
  const terms = Io.within(Duration.secs(1), () => leadersByTerm(peers));
  for (const t of terms.iter()) {
    assert(t.leaders.len() <= 1, `term ${t.term} had ${t.leaders.len()} leaders`);
  }
}
```

## 4. The network

Every node's `Socket.connect` and `Listener.bind` (and the distribution design's connections, which are built on them) reach the world's network, where addresses are node names: `Socket.connect("b", 7000)` from node `a`.

- **A connection is TCP's**: what is written arrives, in order, or the connection is reset. That is all TCP promises, so it is all the simulation promises.
- **Delivery takes time.** Each write becomes a delivery, delayed by an amount the seed draws between the link's bounds (1 to 5 ms unless the world or `slow` says otherwise). The clock moves to the next delivery when nothing can run, as it moves to the next sleeper now, so a minute of network chatter costs no wall-clock time.
- **Reads are split.** A read returns what has arrived so far, cut at a point the seed chooses. A protocol that assumes one read is one message is the commonest framing bug, and this finds it on the first run.
- **Different connections are not ordered.** What `a` sends `b` and then `c`, and `c` then sends `b`, may arrive at `b` in either order. The seed decides. This is where most distributed-algorithm bugs come from.
- **A partition holds what is in flight.** A cut link delivers nothing. A connection across it that has data unacknowledged for longer than its timeout (30 s of virtual time, TCP's user timeout, unless the world says otherwise) is reset on both sides, and `read` and `write` fail with `#Reset`. A connection whose link heals sooner delivers what it held. `connect` across a cut link fails after the connect timeout with `#TimedOut`.
- **The world's scripted peers stay**, for services outside the cluster: `peer(addr, text)` in the unit tests design's `World`.

UDP is not simulated. `std/net` has none yet.

## 5. Crashes and disks

**A crash** is what happens when a machine loses power. It is not a panic and not a cancellation. `c.crash(n)` takes every task of the node off the scheduler and drops each one's continuation. §9.5 proves, as of 0.105, what dropping a continuation does: every value it owns is dropped exactly once, its `defer`s run, and *every operation a `defer` performs is cancelled*. So memory is freed and the leak checker stays meaningful, but the node sends no last message, flushes no buffer and writes no file. Its connections are reset at their other ends after the network's timeout, as a real peer's would be once its machine is gone. Its listeners are gone, so a `connect` to it is refused.

**A disk** has two layers per file: what is *durable* and what is *written*. A write changes the written layer. `file.sync()` makes the written layer durable. That is a new operation of `std/io`, `Io.sync(fd)`, which a real program needs anyway and which today's `std/io` lacks. A read sees the written layer. A crash throws the written layer away, so after `restart` a file is what was last synced. With the world's `torn` fault on, a crash instead keeps a prefix of each unsynced write, in units of 4 KB pages chosen by the seed, as a real disk may. A `rename` is durable once the directory is synced (`Io.sync` of the directory), as POSIX requires and most bugs in real storage engines forget.

**`restart`** runs `start(env)` again as the node's new root task, over the durable disk. A test can therefore check what every storage engine must survive: a crash at any point, then recovery.

## 6. Faults by the seed

A test can script its faults, as `oneLeaderPerTerm` does. It can also leave them to the world:

```ts
const CHAOS: World = World.empty()
  .partitions({ every: Duration.secs(10), heal: Duration.secs(3) })   // on average
  .crashes({ every: Duration.secs(30) })
  .latency(Duration.ms(1), Duration.ms(200))
  .drift(500)                                                         // up to ±500 ppm per node
  .torn();

@test(world = CHAOS, seeds = 5000)
function survivesChaos(): void uses Io { … }
```

Each rate is a bound, and each seed draws its own value within it: one seed partitions often and never crashes, another crashes twice and keeps its links. That is swarm testing (Groce et al., 2012). A fault mix that would be rare under fixed rates is the main event of some seed. A random crash restarts its node after a delay the seed draws, so a cluster under chaos keeps all its nodes in the long run. A test checks its properties once the chaos has stopped (`c.calm()`, which heals every cut and restarts every crashed node) and the cluster has had time to settle.

## 7. Checking a history

A distributed system's correctness is a property of what its clients saw: each operation's call and return, and what it returned. `std/test` records and checks that:

```ts
// std/test.fly, sketch.

export interface Model {
  type State extends Clone;
  type Op extends Clone & Eq & Show;
  type Out extends Eq & Show;
  function init(): Self.State;
  function step(s: readonly Self.State, op: readonly Self.Op): [Self.State, Self.Out];
}

// Operations as clients saw them: each call's time, its return's time (none if it never returned:
// timed out, or its node crashed), and what it returned.
export struct History<M extends Model>;
impl<M extends Model> History<M> {
  export function new(): History<M>;
  // Records the call, runs `body`, and records what it returned and when; a failure is recorded
  // as no return, and passed on.
  export function record<row E>(self: readonly Self, client: u32, op: M.Op, body: once () => M.Out uses Io, ...E): M.Out uses Io, ...E;
}

// Whether some order of the operations, each taking effect between its call and its return, gives
// what each returned: Wing and Gong's search, with Porcupine's partitioning by key when `M` has one.
export function linearizable<M extends Model>(h: readonly History<M>): #Ok | #Violation { ops: Vec<String> };
```

An operation that never returned may or may not have taken effect, and the checker tries both, as Knossos does. The search is exponential in the worst case. It is meant for the few hundred operations of one seed, and a failure shows the shortest set of operations it found that can't be ordered.

## 8. A failing seed

```
FAIL kv.linearizableUnderChaos (seed 4211): not linearizable:
  client 2: put("x", 1)  0.82s – 0.95s  → ok
  client 0: get("x")     1.10s – 1.12s  → None
  fly test kv.linearizableUnderChaos --seed 4211 --trace runs it again, with what every node did
```

The observability design's trace, of a seed, is the cluster's history at the level of the runtime: every delivery, every partition and crash, every scheduling point, by node and task. A trace of a failing seed shows the order of events that broke the property, and it is the same trace every time the seed is run, on every back end.

## 9. How it is built

1. **A world in the program** (`selfhost/rt/sched.fly`, `src/eval/sched.rs`, `selfhost/runtime.js`, `selfhost/runtime.c`). `Sched` becomes a value that can be made more than once. `fly_rt_tasks`'s program-wide world becomes `Sim.world` around `main`. The native runtime runs a world inside one task, as a nested scheduler that never yields its worker until its world ends. The world, not a process global, becomes the root handler of its tasks' `Io`. This is the largest step, and the unit tests design benefits from it alone.
2. **Nodes**: a node in each task's record, and per-node file systems, listeners, clocks and addresses in the world (`src/eval/world.rs` and its C and JavaScript counterparts). The rule that objects stay on their node.
3. **The network**: connections as pairs of queues of timed deliveries, split reads, cuts and timeouts. Deliveries join the sleepers as things the clock can jump to.
4. **Crashes and disks**: `Io.sync`, two layers per file, a crash as dropping each task's continuation, and `restart`.
5. **Faults by the seed**: `World`'s builders, and the world drawing its faults from the seed.
6. **`History` and `linearizable`** in `std/test`, which are library code.
7. **Examples**: a replicated key–value store under `examples/`, tested under chaos, and a deliberately broken one whose failing seed the test suite expects.

**What it costs.** A simulated cluster runs on one core at the speed of its code plus the scheduler's choices. A seed of five nodes simulating a minute of virtual time should take well under a second of CPU, so five thousand seeds take minutes across the machine's cores. That is the bar this design sets, measured with the replicated store.

**Determinism.** Everything a world's tasks can observe must come from the world: its clock, its seed and its network. The hazards are the ones the simulator already avoids: `Io.random` is seeded, iteration over a `HashMap` must not depend on addresses, and a world's `par` runs on its own thread. Each new part of the world is tested by running the same seed on every back end and comparing traces, which is how the suite already checks schedules.

## 10. The proof

λ-fly has no network and no nodes. What this design asks of it is what it already proves. A crash is a set of dropped continuations, each of which frees what it owns exactly once and performs nothing, as 0.105 proved. The rule that a node's objects stay on their node is what makes nodes independent programs, which the theorem then covers one by one: each node is a set of tasks sharing channels, mutexes and atomics among themselves only. The world's choices (deliveries, faults, the seed) are answers of the `Io` handler, which the theorem already treats as arbitrary. So it holds under every fault as it holds under every schedule.

## 11. What was weighed

- **Real processes in containers**, as Jepsen and Maelstrom run them. They test any binary, but slowly, in real time, and a failure seldom reproduces. Simulation tests the code, not the binary, at thousands of times the speed, and every failure reproduces.
- **A deterministic hypervisor**, as Antithesis provides. It needs no help from the language and reproduces everything. It is a service, not a test, and a Flyscript program already does all its I/O through one handler, which gives the same determinism for nothing.
- **Mocking the network in each library**, as many Rust and Go projects do with traits for their transports. Every library needs its own mock, and the mocks never misbehave the way real networks do. Here the network is the world's, under every library at once.
- **Nodes as separate programs in one world.** A world could run several programs, each its own `main` from its own build. That is closer to production. But a node's code and the test's are then compiled apart, and the test can't hand a node its configuration as a value. A node as a function in the same program covers the common case. Different builds talking to each other are the open question on rolling upgrades.

## Open questions

1. **A static rule for nodes sharing nothing.** `env` is data, but `start`'s captures are checked only at run time. A bound on closures, "captures only what is `Encode`", would make it static. Is that a bound the language should have?
2. **Rolling upgrades.** A test that runs version 1 on two nodes and version 2 on a third would catch protocol changes that break mixed clusters. `fly` could let a package depend on an older version of itself under another name (`kv_v1`), and the test would then start nodes from both.
3. **UDP**, once `std/net` has it: loss, duplication and reordering per datagram.
4. **The disk's fidelity.** Two layers and torn pages catch most storage bugs. Real file systems also reorder writes to different files between syncs. Should the simulation model that as well?
5. **Searching for a failure**, not just sampling seeds. Once a seed fails, the world could try smaller fault schedules that still fail, as property-based testing shrinks inputs, so a failure is shown with its fewest faults.
