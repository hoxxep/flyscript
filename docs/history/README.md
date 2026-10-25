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
| 0.23 | Derived interfaces in the prelude and the operators through them; closure modes enforced; total floats; `iterMut` |
| 0.24 | Template structs; associated types in impls; `ParSplit` over a `Slice` view; `Soa`, `par` and `parReduce` in Flyscript |
| 0.25 | Calls through borrows follow closure modes; associated types and template instances checked for borrows; `if (let …)` |
| 0.26 | Contextual `match`/`handle`/`region`/`effect`; lists default to arrays; diverging branches; failures named for what failed |
| 0.27 | Channels close; tasks share strings; TypeScript's string methods |
| 0.28 | Continuations called as functions; several `with` clauses; expression arm bodies; `min`/`max` |
| 0.29 | `Cont<A, B, E>` again, not `Send`; escaping continuations borrow the arms' bindings; `defer` and `Drop` cannot fail |
| 0.30 | Borrows cannot outlive their scope; operation arguments lent to the arm; `Cont`'s row is the `handle`'s own; assignment drops; `while (const …)` |
| 0.31 | Copy parts bind by copy; `Box` borrows lend; literal parts lent into borrow slots; recursive aliases rejected |
| 0.32 | A yielded value is a result; `generate` written in Flyscript with one `unsafe` arm; open unions never enums |
| 0.33 | TypeScript's array and generator methods; strings interpolate raw in generic code; borrows of borrows collapse |
| 0.34 | Tasks move in scope-locals; closures own what they move in; `Mutex`; cloneable senders; `drain`; `Fail.capture` passes effects on |
| 0.35 | No result borrows an owned parameter; `Gen` items borrow what it holds; helper-started tasks cannot borrow |
| 0.36 | Escaping closures cannot capture region data; tasks cannot change what they borrow; drop order |
| 0.37 | A continuation holds the loans live across every point its body may perform the effect |
| 0.38 | `Io`'s `Fd`, `Instant`, `Duration`; unimported interfaces suggest their import |
| 0.39 | Consistency pass: checked overflow; `panic`; Option/Result methods; grammar and §9 aligned; §0.1 rebuilt |
| 0.40 | Programs from the spec alone: destructuring closure params; bare void tags; `Vec` edits; `Mutex` borrowed by tasks |
| 0.41 | Self-hosting is goal 6; unions include named unions; matches move per arm |
| 0.42 | Mini, a compiler in Flyscript: coinductive type properties; a module's own `Type`; matches through borrows; ranges |
| 0.43 | Mini gets recursion, let-polymorphism, source diagnostics; `{ a, b }` records; reserved method names; `HashMap` is `Clone` |
| 0.44 | Mini's checker in a region; pure generators take any effect row; `allocAll`, `HashSet`, `replace`; per-field borrows stated |
| 0.45 | Mini recovers from errors through a `Diag` effect; `match` narrows unions |
| 0.46 | Mini compiles algebraic data types; `Box` matched through; receiver-decided results; handles are `Clone` |
| 0.47 | Mini as five modules (examples/mini/); no language change needed |
| 0.48 | Mini types records by rows; specialization keys erase regions |
| 0.49 | Patterns match through pointers by borrow; regions may point outward; `Ref` keys maps; `Box.into` |
| 0.50 | Mini infers effect rows; two-phase `mut` arguments; string patterns match owners |
| 0.51 | Mini checks ownership; loop variables release their loans per iteration |
| 0.52 | Mini evaluates `comptime` on its own machine |
| 0.53 | Mini has interfaces with dictionary passing |
| 0.54 | Flyscript compiles itself: a checker and JavaScript back end written in Flyscript |

## 0.55 onward

Each version from 0.55 says in a sentence what it changed, newest first, with the sections of the specification of its day.

- **0.131** adds `std/simd`: `Simd<T, N>` and `Mask<N>`, lowered to the target's vector instructions natively and in WebAssembly, and run a lane at a time elsewhere (§11.3, §12.3).
- **0.130** tells LLVM that a `mut` parameter is `noalias` and a `readonly` one `noalias readonly` (§11.3).
- **0.129** drops what a box, a `Vec` or an `Arc` holds of a type that may hold itself, where such drops nest deeply, after the rest of the value holding it, so a list or a tree of any depth drops in the stack a few nodes take (§4.4).
- **0.128** allocates a closure given to a function that only calls it, `once` or not, in its caller's frame, and instantiates a generic call whose result is only a type parameter as its arguments say where a `str` or a slice is expected (§3.6, §11.3).
- **0.127** adds `trailingZeros`, `leadingZeros` and `countOnes` to every integer type, `readU64Le` to byte slices and `String.fromUtf8Unchecked`, with which `std/io` finds a line's end and whether it is ASCII eight bytes at a time, in one pass ([std.md](../std.md)).
- **0.126** keeps in a frame only what is live across a point it stops at, gives what each point keeps alone room every point shares, and nests the frame of a function called directly in its caller's unless the callee may call it again, so that a million tasks parked two calls deep take what a million parked Rust futures on tokio take (§11.3).
- **0.125** compiles tasks to state machines: a task that waits keeps only what it reads again, in frames of its own, and no stack, and the runtime's waits — the clock, sockets, channels, other tasks, a scope's end — are calls made again to go on, so native code has no fibers left; cleanup that waits runs as a panic unwinds, the machine whose cleanup it is taking the panic up and unwinding on by its flag; every thread that runs tasks has the same stack (§5.7, §8.2, §8.3, §11.3, §12.1).
- **0.124** compiles a handler's body whose arm does more after resuming, and a generator, to state machines: each keeps across a suspension only what it reads again, in a frame of its own, with no stack of its own, and a loop over a generator pulls it item by item; and drops what a generator adapter pulls from once it is done with it, in the reference and JavaScript as natively (§8.3, §11.3).
- **0.123** adds re-exports, `export { a, b as c } from "./m";`, by which a package presents one public face over the files behind it (§8.1); moves this record out of §0.1; has every fragment of code in the specification parsed on every build; puts `generate` and `next` in λ-fly's terms (§9.1); says in §12.3 what remains open beyond λ-fly, all of which is proved; and puts a guard below a native task's stack, against C that runs past it (§8.2).
- **0.122** checks a `defer` where it runs: the block may use what the `defer` uses meanwhile, `mut` included, and what outlives the `defer` as it runs may not hold a borrow it conflicts with, which also rejects a `defer` that replaced what a returned borrow borrows, accepted before (§5.6).
- **0.121** brings λ-fly's terms and rules up to date with panics that unwind: `panic` is a term, a `defer` runs on a panic's exit too, and a spawned task's panic ends it alone (§9.1, §9.3, §9.4).
- **0.120** proves poisoning: a `Mutex` whose holder panics in its body keeps the state as the body left it, never dropped by the task that panicked, and every `lock` after it panics, the panics ending their tasks alone (§6.2, §9.5).
- **0.119** proves that a panic ends a task started by `spawn` alone: the task unwinds, dropping what it owns, and its scope and the scope's other tasks go on, as §5.7 has it (§9.5).
- **0.118** proves panics: a panic is an unwinding to the program's root that nothing catches, so the guarantee that everything is dropped exactly once and nothing is left holds through it, fibers, generators and tasks included; only the end of the program at once, where the language ends it, is outside it (§9.5).
- **0.117** ends the program at a panic that escapes a destructor — a `Drop` impl, or the cleanup of a continuation or a generator that dropping a value unwinds — for dropping a value cannot stop halfway (§5.7).
- **0.116** makes overflowing the stack a panic of its task, as an index out of bounds is, so a recursion with no end on hostile input ends the connection that made it and not the server; in WebAssembly the engine's own call stack is a trap there still (§5.7).
- **0.115** gives a spawned task a `Task`, which cancels it alone and says how it ended — done, cancelled or panicked — and `Task.any`, which waits for the first of several; a spawned task's panic no `wait` gives is reported once nothing can ask for it. Cancelling a task cancels what it started, a cancellation reaching a task as it waits at a scope's end is no longer lost, and a cancellation by `Task` is for good. Cancellation stays at `Io` operations (§5.7, §6.1). Supervision is library code over `Task`, in `std/supervise` (§12.3).
- **0.114** makes a panic end its task rather than the program: it unwinds the task, running its cleanup, as a failure nothing catches would; a spawned task's panic ends that task alone and is reported, a forked task's is its scope's, and a `Mutex` whose holder panics is poisoned until it is reset (§5.7, §6.1, §6.2).
- **0.113** adds `p.with(body)`, which lends the value a raw pointer reaches, `mut`, to a closure, as code that vouches for it may; with it the runtime's scheduler, channels and `Mutex` are Flyscript over a thin core of C (§8.2).
- **0.112** gives packages a home outside the installation: a build names the directory of each package it uses, which `fly` resolves from a manifest and a lockfile that holds each dependency to the commit, the content and the effects it was accepted with (§8.1).
- **0.111** joins the proof to the compiler: a checker for λ-fly, proved sound, certifies on every build the test programs the compiler elaborates into λ-fly, which never get stuck; and λ-fly's integers have the operations of the language's, a division by zero a panic (§9.5).
- **0.110** cuts a page's program into a core and a module for each route, which the host links in the first time the route is shown (§8.3).
- **0.109** writes and reads floats exactly and alike everywhere: shown, the fewest digits that read back as the float, in full and never with an exponent; `toFixed` to the nearest, halfway to the even; and `parseFloat` to the nearest, of text an optional sign, digits around a point and an exponent (std).
- **0.108** compiles WebAssembly through LLVM, as native code is, rather than through C (§8.3).
- **0.107** adds `Atomic<T>`, an `i64` or a `bool` that tasks share, whose operations are `Io` and sequentially consistent, with no weaker orderings (§6.2); defines channels, `Mutex` and atomics as handlers that own their state around a scope whose tasks perform their operations, which the runtime implements natively; and proves them so, under every schedule: a value sent or locked is owned by one task at a time (§9.5).
- **0.106** lets a continuation leave its arm only if it holds no borrow and refers into no region: its operation lends nothing, its arms use nothing of the code around, and its body nothing that refers into a region; it can no longer be written into an outer binding by its arm, which could then change that binding while other code is using it (§5.3). Such a continuation, dropped, is cut off from every handler; one its arm gives up unwinds under the handlers around its `handle`. `generate` is the language's own, not library code over a handler, and `unsafe` vouches for raw pointers and foreign code alone (§5.5, §8.2). With this, the proof covers all of λ-fly (§9.5).
- **0.105** cancels what a dropped continuation's cleanup performs: an operation other than `Io` unwinds the cleanup from it, as a failure would, for the continuation is cut off from every handler (§5.3); and proves continuations kept as values in general: any value of no region passes into and out of the body, which performs what the code around handles — operations that lend it places among them, the body taken with the operation as one frame of the continuation and entered again once answered — and fails, the failure leaving the body for the handler around (§9.5).
- **0.104** proves continuations kept as values: an arm given the rest of its `handle` as a value of its own holds it as any owned value, moves it, passes it to functions and returns it from them, and resumes it once, wherever it is, or drops it, which unwinds the code it holds, each of its scopes dropping what it owns and each of its cleanups running (§9.5).
- **0.103** proves tasks running on many cores at once: a task may be stopped before any of its operations for another to run, so the proof covers every interleaving of their operations, and an operation by which tasks give way is taken by the frame of their tasks alone, never by a `handle` (§9.5).
- **0.102** proves a scope's tasks borrowing what was declared outside the scope: each task is lent, `readonly`, the places the scope names, which the code around the scope only reads until every task has ended, the tasks reading them as the body does (§9.5).
- **0.101** proves scopes that start tasks as they run: a scope's body starts any number of tasks, each a closure called once that moved in what it captured, the body and the tasks giving way to each other in any order a schedule picks, the scope ending once all have, and a failure of any of them dropping the rest where each waits (§9.5).
- **0.100** proves slices of a vector lent `mut`: a slice changes the elements it is of, through borrows of them, but not which run of them it is, so it cannot grow, and the vector is out of reach while it lives (§9.5).
- **0.99** proves generators lent whole bindings `mut`: the producer changes them as it runs, the code that holds the generator cannot reach them until both sides are done, and they are given back as the producer left them, whether it ended, was dropped where it waited, or failed (§9.5).
- **0.98** proves an arm that resumes inside a borrow it holds: the borrow ends where the arm resumes and is taken again in what runs after, which reaches the same place, for the code the arm resumes cannot (§9.5).
- **0.97** proves a region's `RegionList`s: pushed to through the arena, owned or lent `mut`, each element a cell of the region, read by index wherever the region is in reach, and held by reference as data of the region (§9.5).
- **0.96** proves `readonly` slices of a vector: a vector of its own, of some of its elements, the vector only read while it lives, and a range out of bounds a panic (§9.5).
- **0.95** proves taking an element out of a vector: its last, its tree moving out of the vector into the value (§9.5).
- **0.94** proves generators: a continuation kept past its arm and resumed as the code that holds it asks, the producer's values moved to the consumer one by one, either side dropped where it waits when the other ends or fails (§9.5).
- **0.93** proves borrows held for a while of places at any depth in a variable, the fields beside them in use at every step: each a chain of borrows of a field, or of what one holds, of the borrow before (§9.5).
- **0.92** proves vectors: elements pushed, moved to new cells as the vector grows, borrowed by index for a while — a borrow of the whole vector — and dropped with it, and an index out of bounds a panic (§9.5).
- **0.91** proves a function of a region called for any region the calling code is in, its innermost or one around it (§9.5).
- **0.90** proves functions of their callers' regions: lent an arena, `mut` to allocate in it or `readonly` to read through it, given references into it and giving them back (§9.5).
- **0.89** proves a region's `Cell`s: changed through the arena, owned or lent `mut`, read through any reference that reaches them, every reader seeing the change (§9.5).
- **0.88** proves regions: an arena released at once when its block ends, whose cells, allocated as the block runs, may refer to each other and to those of regions around it; a reference into a region read wherever the region is in reach and never outliving it, which its types say without a rule of their own (§9.5).
- **0.87** proves tasks: two tasks, calls that take their owned arguments and are lent places only `readonly`, run as one, each giving way to the other wherever it yields, in whatever order the schedule picks; while one runs, the other's cells, and what both read, are as they were; and if one fails, the other is dropped where it waits, its scopes dropping what they own and its cleanups running, before the failure goes on (§9.5).
- **0.86** proves an arm that decides as it runs whether to resume: it may end without resuming, its value the `handle`'s and the continuation dropped, each of its scopes dropping what it owns and each of its cleanups running; and an arm that resumes in its midst may take places its operation lends it (§9.5).
- **0.85** proves a continuation resumed in the midst of its arm: the arm resumes `k` once and goes on with what the rest of the `handle` gave, what it does after the resumption run as a function given what the arm carried past it and the places its `handle` lends, once the rest of the `handle` ends (§9.5).
- **0.84** proves replacing the field beside one borrowed for a while: `p.b = q` while `const r = mut p.a` lives (§9.5).
- **0.83** proves borrows of one field held for a while: while `const r = mut p.a` lives, `p.b` may be read, changed and lent, the field borrowed a hole in the type of `p` until the borrow ends (§9.5).
- **0.82** proves borrows locked per field across a call: a call may hold two fields of one value at once, both `mut`, or one `mut` and the other `readonly`, as `swap(mut p.a, mut p.b)` does (§9.5).
- **0.81** proves tags and `match`: a tag carries a value in a cell of its own, which a `match` takes apart, its arm owning it, or borrows, `readonly` or `mut`, for its arm (§9.5).
- **0.80** proves records of two fields, each a place of its own, which a borrow reaches past the fields beside it (§9.5).
- **0.79** proves borrows a function picks as it runs among the places it was lent, each of whose roots its caller only reads, or cannot reach, while the borrow lives (§9.5).
- **0.78** proves closures that own closures, and closures passed to functions and returned from them by value (§9.5).
- **0.77** proves closures over a `mut` borrow, lent on `mut` to the functions that take them, what they borrow out of reach while they live; and so that a `mut` borrow of a closure lends the right to call it and nothing more, it may no longer put another closure in its place (§4.3, §9.5).
- **0.76** proves closures over a `readonly` borrow, lent on to the functions that take them, what they borrow only read while they live (§9.5).
- **0.75** proves closures that own what they capture: called once, a closure gives its body what it captured; called through a borrow, it lends it, as a call lends a place (§9.5).
- **0.74** proves borrows a function returns: a function may give back a borrow of a place it was lent, and its caller holds the borrow for the code it is in scope for, what it lent only read, or out of reach, until that code ends (§9.5).
- **0.73** proves handlers as the language runs them: an operation takes the code up to its `handle` as a continuation, which the arm resumes with its value or, if it fails, drops, each scope dropping what it owns and each cleanup running (§9.5).
- **0.72** proves handlers that keep state of their own, a binding lent their arms `mut` that their body cannot reach (§9.5), and runs a handler whose arms end its `handle` as a call, without a fiber (§11.3).
- **0.71** proves ownership and effects in one calculus, with loops, cleanup and local borrows: a handler's arm resumes with what its `handle` lent it, or unwinds dropping what the scopes it leaves own (§9.5).
- **0.70** drops a temporary when the statement it is made in ends, and checks that nothing borrows it after (§5.6); keeps an argument lent to a call borrowed for as long as the result that borrows it, whatever the argument's own type (§4.2); holds an impl to its interface's methods — each there, taking and giving what the interface's does and performing nothing more (§3.4) — and gives floats the arithmetic of `<math.h>` and fixed-point text (std).
- **0.69** adds packages, imported by name rather than by a relative path (§8.1).
- **0.68** makes a panic end the program at once, running no task's cleanup, which could otherwise wait forever on what the panicking task held (§5.7); ends a resumptive arm's borrowed arguments when the continuation is given up in any way, not only when it is called (§5.3); and keeps a match arm that moves a part from taking apart a `Drop` value, or from letting a borrow of what it owns outlive it (§4.1).
- **0.67** extends the proof of ownership to branches and to failures, which unwind through scopes and calls dropping what each owns (§9.5).
- **0.66** proves two fragments of the core calculus mechanically — moves, drops and lending; effects and handlers — and says exactly what the proofs cover and what rests on testing (§9.5).
- **0.65** folds the rules for how code takes hold of a place into one (§4.1), states the guarantees of the core calculus and how each is established (§9), and moves what is a cost rather than a meaning into performance contracts (§11.3).
- **0.64** lets a task go on on any core after it waits (§8.3).
- **0.63** specifies the standard library as carefully as the core, in [std.md](../std.md).
- **0.62** makes cleanup run to its end under cancellation (§5.6, §6.1).
- **0.61** runs programs compiled to WebAssembly in web pages (§8.3), with a web framework in library code built on `Ui`, an effect, and on real sockets.
- **0.60** gave native programs real sockets (§8.3): `std/net` listens and connects on the machine's network when no world is simulated, and `IoErr` says when an address is in use.
- **0.59** made handlers whose arms each end by resuming cost a call per operation (§5.2), the shape dependency injection and rendering take.
- **0.58** ran native tasks on every core (§8.3), and `par` and `parReduce` on all of them through `join`, which runs two pure closures at once (§6.5).
- **0.57** added LLVM as a way to native code (§8.3): a program's functions as LLVM IR, with debug information that maps them to their source, optimized together with the runtime, for any target LLVM has.
- **0.56** built the foreign interface (§8.2): raw pointers as the prelude's `Ptr<T>`, reaching through one an effect, `Unsafe`, that `unsafe { … }` handles, and functions of C's and functions C calls; and one core IR under the self-hosted compiler's back ends.
- **0.55** follows the self-hosted compiler's back ends — typed JavaScript, and C without a garbage collector — which specialize every function for the types it is used at and run tasks on a scheduler of their own, and the port of the ownership pass to Flyscript.

What 0.64 and 0.65 changed, and why:

| Change | Why |
| :--- | :--- |
| Code that takes hold of a place — an arm binding its parts, a closure capturing it, a name bound from a borrow — holds it by use, one rule where there were three (§4.1, §4.3) | the rules for arms, copies and borrowed matches each restated the same principle with its own exceptions |
| §9 states what the rules guarantee — type, memory and effect safety, data-race freedom, deterministic destruction — and how each is established | the calculus was a sketch, and soundness was argued without saying what stood in for a proof |
| How handlers, tasks, `join`, locks and regions perform is a contract of the implementations (§11.3), not a rule of the language | a direct handler and a task's core were described in the rules, which a program cannot observe |
| An operation's argument for a `readonly` or `mut` parameter is lent to the arm, as a call's is (§5.3) | it was moved, so an update could not show a handler a model it did not own |
| The specification no longer promises `Pool<T>` (§4.5) | the library never had it |
| A native task goes on wherever a core is free, not only on the worker it began on (§8.3) | a task began where its scope ran and stayed there, so tasks that woke together could queue on one core while others were idle |

`review-round-*.md` are the design review rounds that produced 0.2–0.15; `programs-against-v0.13.md` is the program-writing exercise against what is now 0.13.
