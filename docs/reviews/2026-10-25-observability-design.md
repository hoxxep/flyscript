# Seeing a running program: task names, `fly inspect`, stalls and traces — a design

A proposal, for review, for what makes an Erlang node easy to operate: you can look inside it while it runs. `observer` lists every process, `process_info` says what one is waiting on and how long its mailbox is, `sys:get_state` shows a server's state, and `recon` finds the process eating a scheduler. A native Flyscript server today shows none of this. A request that hangs, a lock that never comes free, a mailbox that grows, or a task that loops without waiting looks the same from outside: the process is up and does nothing useful. This design gives every task a name for free, lets a running program list its tasks and channels on request, reports a task that holds a core too long, and records a trace of a run that can be replayed. Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document.

It is one of five designs that carry Erlang's strengths over. `2026-10-25-select-and-deadlines-design.md` gives the waits whose targets this design reports. `2026-10-25-actors-design.md` gives mailboxes their names and has every actor answer section 4's questions. `2026-10-25-simulated-cluster-design.md` uses section 6's trace to explain a failing seed. This design depends on none of them, and each of them is better with it.

## The design in brief

1. **Every task has a name, at no cost to write.** By default it is where the task was spawned, `examples/server.fly:14`, a constant the compiler already knows. `s.spawnNamed(name, task)` gives one of the program's own, `conn 10.0.0.7:51234`. A supervisor names its children, and a mailbox its actor. A panic report names its task.
2. **The runtime already knows what each task is doing**, because it has to wake it. Inspection just reads it out: what a task is parked on (a channel, a timer, a socket, a lock, a `select`, another task), since when, its parent, and how often it has run.
3. **`fly inspect`** asks a running program, over a Unix socket it opens only when asked to (`FLY_INSPECT`), for its task tree, its channels and their lengths, its stalls, and an actor's state. The socket is served by a thread of its own, so it answers even when every worker is stuck. It inspects only. There is no shell and no evaluation, unlike Erlang's remote shell, which runs any code.
4. **A stall is reported, not interrupted.** A task that has held a worker for longer than a threshold without reaching a scheduling point is reported once, by name, with where it is running. Flyscript cannot stop such a task, by design (§6.1), so the next best thing is to name it.
5. **A trace** of every scheduling point (`FLY_TRACE`) costs nothing when off and a few nanoseconds per event when on. Against a simulated world it is the story of a seed: what ran, what each task waited for, and what woke it.

---

## 1. What a running program shows today

A native program shows its output and its panics. A spawned task's panic is reported by its message alone (§5.7): `index 3 out of bounds (length 3)`. It doesn't say which of five thousand connections it was, or what code started the task. Nothing can list a program's tasks, nothing can say what a parked task waits for, and nothing reports a task that has stopped waiting at all. The runtime knows all of this. A parked task's `fly_wait` record (`selfhost/runtime.h`) holds what it waits for, because the code that wakes it has to find it. The simulated scheduler keeps a `waitKind` and `waitId` for each task (`selfhost/rt/sched.fly`). None of it is exposed.

Erlang's tools work because every process is a runtime object with a record of what it is doing. Flyscript's tasks are too, as state machines with a record each. What is missing is a name, a way to ask, and a report for the one failure that inspection can't prevent: a task that never waits.

## 2. Names

```ts
// The prelude, sketch.
impl<X> Scope<X> {
  // As `spawn`, the task named `name` for what the runtime reports of it.
  export function spawnNamed(self: mut Self, name: String, task: once () => void uses Io): Task uses Io;
  export function forkNamed<T extends Send>(self: mut Self, name: String, task: once () => T uses Io, Fail<X>): Fiber<T> uses Io;
}
impl Task {
  export function name(self: readonly Self): String;
}
```

**A default name for every task.** A task spawned with `spawn` or `fork` is named after the place it was spawned: its file, line and the function it was spawned in, `serve (examples/server.fly:14)`. The compiler knows these at the call, as it knows a panic's location. They become a pointer to a static descriptor in the task's record, one word, written as the task starts. So every task has a useful name without anyone writing one, and five thousand connection tasks are five thousand `serve (examples/server.fly:14)`s, which is the first thing to know about them.

**Names a program gives.** `spawnNamed` moves a `String` into the task's record, freed with it. `std/supervise` names each child with `Child.name`, and the actors design names each mailbox and the task that serves it. A name is for people. Nothing looks a task up by name, so two tasks may share one.

**A panic report names its task.** The report a spawned task's panic makes (§5.7) becomes:

```
task `conn 10.0.0.7:51234` (spawned in serve, examples/server.fly:14) panicked: index 3 out of bounds (length 3)
```

`TaskEnd.#Panicked` keeps only the message, as now, so tests whose `// expect:` lines read it don't change. The report goes to standard error.

## 3. What the runtime knows of a task

```ts
// std/inspect.fly, sketch: a running program, as its runtime sees it.

export type TaskInfo = {
  id: u64;
  name: String;
  spawnedAt: str;                 // "serve (examples/server.fly:14)"
  parent: Option<u64>;            // the task whose scope started it
  state: TaskState;
  since: Duration;                // how long it has been in that state
  runs: u64;                      // how many times it has been given a worker
  age: Duration;
};
export type TaskState =
  | #Running { worker: u32 }
  | #Ready
  | #Parked(WaitingFor)
  | #Cleaning;                    // unwinding: its `defer`s and drops are running
export type WaitingFor =
  | #Receive { channel: u64 } | #Room { channel: u64 }   // a bounded channel's send
  | #Task(u64) | #AnyTask(Vec<u64>) | #Reply
  | #Timer { at: Instant } | #Select { channels: Vec<u64>; tasks: Vec<u64>; at: Option<Instant> }
  | #Lock | #Io { fd: i32; op: str } | #Scope;
export type ChannelInfo = { id: u64; name: Option<String>; queued: usize; capacity: Option<usize>; senders: u64; received: u64 };

// Each task's record and each channel's, read one at a time under its lock: not one instant of
// the whole program, which no running program can give without stopping, but each true when read.
export function tasks(): Vec<TaskInfo> uses Io;
export function channels(): Vec<ChannelInfo> uses Io;
```

A program can call these itself, for a status page, a health check, or a test asserting that a scope leaves no task behind. `fly inspect` (section 4) calls them from outside.

**What it costs.** One word in every task's record, always: the pointer to its name or its spawn site's descriptor. Everything else in `TaskInfo` is already in the record (state, what it waits for, its scope) or is kept only when inspection is on: `since`, `runs` and `age` go in a side record allocated with the task only if the program was started with `FLY_INSPECT` set. Step 15's bar holds this design to account. A million parked tasks take 248 MB today against tokio's 256 MB (docs/performance.md), and the word costs 8 MB of that margin. If the record has no room for it in its padding, a task's name moves to the side record too, and a task spawned without inspection on is named only by its spawn site, which the frame's resume function already identifies.

**A mailbox's name** comes from the actors design's `mailbox(name, capacity)`. A plain channel has none, and is listed by its id and the task that receives from it, when one is parked there.

## 4. `fly inspect`

A program started with `FLY_INSPECT=path` (or `fly run --inspect`) opens a Unix socket at `path`, readable and writable by its owner only. A thread of the runtime's own serves it. That thread is not a task, so it answers when every worker is busy, stalled or deadlocked, which are exactly the times someone asks.

```
$ fly inspect /run/shop.sock tasks --tree
main (examples/shop/main.fly:9)                          parked 2h13m  scope
├─ http accept (web/server.fly:41)                      parked 0.2s   io accept fd 6
│  ├─ conn 10.0.0.7:51234                               parked 41.3s  reply ← kv
│  ├─ conn 10.0.0.9:40112                               parked 41.1s  reply ← kv
│  └─ … 4,812 more spawned at web/server.fly:58
├─ supervisor (std/supervise.fly:30)                    parked 2h13m  any of 2 tasks
│  ├─ kv                                                RUNNING 41.4s on worker 3   ← stall
│  └─ mailer                                            parked 3.0s   receive mailer (0 queued)

$ fly inspect /run/shop.sock channels --longest
kv          1024 / 1024 queued   3 senders   1,204,331 received
mailer         0 / 256 queued    1 sender       12,019 received

$ fly inspect /run/shop.sock stalls
kv has run 41.4s on worker 3 without waiting, in:
  Kv.handle (examples/shop/kv.fly:52)
  rehash (std/collections/hashmap.fly:310)
```

The commands are `tasks` (with `--tree`, `--parked-longer d`, `--name text`), `channels` (`--longest`), `stalls`, and `actor <name>`, which asks an actor served by `std/actor`'s `serve` for its statistics, and its state if the state is `Show` (actors design, section 3). `actor` is the one command that needs the program's cooperation: the actor answers between messages, so a stalled actor can't. The others read records and need nothing from the program's tasks.

**No shell.** Erlang's remote shell runs any expression on a live node. That is how an Erlang operator fixes a node at 3 a.m. It is also why the node's cookie is a root password. Flyscript programs are compiled ahead of time, with no interpreter to evaluate in. Inspection reads only, and what it may read is listed above. Reaching a program on another machine is `ssh host fly inspect …`, with ssh's authentication, not a network listener of the program's own.

**In a simulated world** the same calls work from inside, and `fly inspect` can be pointed at a run paused at a virtual time (`--pause-at 12.5s`), which is the simulated cluster design's way of looking at a node mid-run.

## 5. Stalls

A task that runs without reaching a scheduling point holds its worker until it does. Cancellation can't stop it (§6.1, and roadmap step 13 says why stopping pure code was rejected). The other workers carry on, and they steal the stalled worker's queued tasks (§8.3), so one stall costs one core, not the program. But a stall that lasts is a bug, Erlang's tools find it in seconds (`recon:proc_window`, the `long_schedule` system monitor), and Flyscript should at least say where it is.

**How it is found.** Each worker writes, when it starts running a task, the time and the task, in two words of its own. A runtime thread, the one serving section 4 or a dedicated one if inspection is off, reads every worker's words every few milliseconds. A worker that has run one task for longer than `FLY_STALL` (100 ms unless set, `off` to disable) is a stall. The thread reports it once, on standard error, with the task's name and where it is running. It gets the location by asking the worker thread for its backtrace with a signal, which the LLVM build's debug information turns into lines (step 3). When the task finally reaches a scheduling point, the thread reports how long the stall lasted. A worker writes two words per task it runs, and the reader takes no lock, so the cost is two stores per scheduling point.

**Why report and not preempt.** A runtime could make every loop's back edge a place a task may give way, as the BEAM's reduction counting does, and then no task could hold a core. Step 13 rejected *cancelling* there. Merely giving way would be invisible to the program's meaning, since pure code cannot observe another task. It is still rejected, for its cost. Every loop would become a point a task can stop at, so the task's frame would have to keep everything live across every loop, which undoes what step 15 measured (a parked task's frame keeps only what lives across its waits). Inner loops would carry a branch that blocks vectorization. A `Mutex`'s body is pure, so a task could give way while holding a lock, which §6.2's design rules out. A report costs two stores, and it says which loop.

**In a simulated world**, pure code is one step and can't stall a run that way. What can stall it is the select design's busy poll: tasks that keep giving way without waiting, so the clock never moves while a task sleeps until a time that never comes. The simulated scheduler counts scheduling points since the clock last moved. Past a limit (ten million unless set), with a sleeper waiting, it reports the run as stalled, names the tasks that ran meanwhile, and ends it as a failure of that seed.

## 6. Traces

`FLY_TRACE=path` records every scheduling point: the time, the task, the operation (`send`, `recv`, `select`, `sleep`, `spawn`, `park`, `wake`, a cancellation, a panic), its object (a channel, a task, a timer, a descriptor), and what came of it. Each worker writes to a ring of its own, which a runtime thread drains to the file. An event is a few words and a store, with no lock, so a traced run is slower by a few nanoseconds per event. An untraced run tests one flag, which is set once as the program starts and never changes, so the branch is always predicted.

`fly trace path` prints a trace, filtered by task, channel or time span. `fly trace path --task kv --around 41s` shows what `kv` did before it stalled.

**Against a simulated world** a trace is deterministic. The same seed gives the same trace on every back end, which the test suite already relies on for output (§6.4). `fly test name --seed 31 --trace` prints the story of the failing seed, and the traces of a passing seed and a failing one can be compared to find where they diverge. This is the simulated cluster design's main debugging tool, and it is why that design's events (a message delivered, a partition, a node crashed) are trace events too.

**Tracing as a handler** stays what §6.4 already allows: a handler of `Io` around code sees that code's operations, which is how a test counts sleeps. It does not see a scope's tasks, which perform the runtime's `Io` (§6.1 rule 4), so it traces one task's code. The runtime's trace sees everything.

## 7. How it is built

- **Names** (`selfhost/lower.fly`, the three runtimes): `spawn` and `fork` pass their call's static descriptor, `spawnNamed` and `forkNamed` a `String`. Records gain the word. Panic reports read it.
- **`std/inspect`**: two functions of the runtime, reading task and channel records under their locks. In the simulated schedulers they read `Sched` directly.
- **`fly inspect`** (`selfhost/fly.fly`) and the socket's thread (`selfhost/runtime.c`): a small line protocol, one request and one reply of JSON lines. WebAssembly and JavaScript have no Unix sockets, so there `std/inspect` works and `fly inspect` does not.
- **Stalls**: two words per worker and the sampling thread. The backtrace uses `backtrace(3)` through the platform's unwinder, which step 13's landing pads already require.
- **Traces**: per-worker rings and a draining thread natively, an array in the simulated schedulers, and one encoding read by `fly trace`.

Tests: a panic report names its task. `tasks()` lists a parked receive, a parked select, a timer and a lock correctly in each runtime. A stall is reported once, with its function. A trace of a seed is the same on every back end. `bench/tasks.sh` is unchanged with inspection off, and is reported with it on.

## 8. What was weighed

- **A remote shell.** It is the most powerful tool an Erlang operator has, and it needs an interpreter and turns a cookie into total control. Inspection that only reads, behind the file system's permissions, gives most of what operators use the shell for (`process_info`, `sys:get_state`, mailbox lengths) at no risk.
- **Preemption.** See section 5. Reporting gets most of its value for operators at none of its cost.
- **Names required on every spawn.** Spawn sites are free and almost always enough. A connection's address is the case for a name, and `spawnNamed` gives it.
- **Metrics in the runtime**, Prometheus counters for every channel. That is library code over `std/inspect`, and which metrics matter is the program's choice.
- **OpenTelemetry spans.** A span is a scope of a request across tasks and nodes, and it belongs in a library, maybe as an effect whose handler propagates a trace id into the requests an actor makes. That is outside this design.

## Open questions

1. **A default for `FLY_STALL`.** 100 ms is long for a request handler and short for a batch job. Should the default be off, with `fly run` turning it on?
2. **Inspecting a cluster.** A node of the distribution design could relay `fly inspect` to its peers over its authenticated connections. Is that the node's job, or ssh's?
3. **Names in `TaskEnd`.** Should `#Panicked` carry the task's name, so a supervisor's log has it, at the cost of changing every test that matches the message alone?
4. **A trace's size.** A busy server makes millions of events a second. Should a trace keep only the last N seconds in its rings and write them out on a panic or a stall, as a flight recorder does?
