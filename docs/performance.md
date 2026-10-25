# Performance

Flyscript compiles to C, through LLVM, and to JavaScript, and runs its tasks on a scheduler of its own. This page measures what that costs: five benchmark programs against C, Rust, Go and JavaScript; the compiler compiling itself; and a web app built with [FlyNext](../web/) against the same app built with Next.js and React. Every number comes from the scripts in [bench/](../bench/), which run the same way on any machine.

## The machine

An Apple M5 Ultra with 30 cores and 96 GB, on macOS 27.0.1. Apple clang 21 at `-O2`, rustc 1.98.1 with `-O`, Go 1.27.2, Node 24.21.0. Programs are timed by hyperfine 2.0, the median of five runs after one to warm up, and their peak resident memory recorded; servers are loaded by wrk 4.2; pages are measured in Playwright's Chromium.

## Programs

`bench/run.sh` builds each program each way, checks that every build prints exactly what the C one prints, and times them. Flyscript (C) is the compiler's C through clang; Flyscript (LLVM) is its LLVM IR, linked with the runtime and optimized as one program; Flyscript (JS) is its JavaScript on Node. The other columns are the same programs written by hand in each language.

| Benchmark | Flyscript (C) | Flyscript (LLVM) | Flyscript (JS) | C | Rust | Go | JavaScript |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-trees, depth 18 | 421 ms | 367 ms | 966 ms | 654 ms | 647 ms | 527 ms | 382 ms |
| fannkuch-redux, 11 | 1414 ms | 1329 ms | 2771 ms | 1490 ms | 1512 ms | 1372 ms | 1718 ms |
| n-body, 5 million steps | 135 ms | 126 ms | 489 ms | 130 ms | 133 ms | 144 ms | 219 ms |
| spectral-norm, 3000 | 211 ms | 211 ms | 762 ms | 268 ms | 214 ms | 287 ms | 402 ms |
| word frequencies, 3 million words | 84 ms | 85 ms | 742 ms | 159 ms | 83 ms | 112 ms | 580 ms |

| Peak memory | Flyscript (C) | Flyscript (LLVM) | Flyscript (JS) | C | Rust | Go | JavaScript |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-trees | 18.2 MB | 18.2 MB | 362 MB | 18.2 MB | 18.4 MB | 42.4 MB | 392 MB |
| fannkuch-redux | 2.2 MB | 2.2 MB | 49.5 MB | 2.1 MB | 2.2 MB | 5.0 MB | 46.1 MB |
| n-body | 2.2 MB | 2.2 MB | 50.9 MB | 2.1 MB | 2.3 MB | 5.0 MB | 48.4 MB |
| spectral-norm | 3.5 MB | 3.4 MB | 49.8 MB | 2.2 MB | 2.3 MB | 5.1 MB | 48.2 MB |
| word frequencies | 24.5 MB | 24.4 MB | 532 MB | 24.4 MB | 22.9 MB | 105 MB | 421 MB |

Natively, through C or LLVM, Flyscript runs faster than C on every program, and on spectral-norm and word frequencies, where Rust is fastest, in Rust's time, with no garbage collector: every value is freed where ownership says it dies. Natively a program allocates from the runtime's own allocator, which keeps blocks in classes of sizes and lets each thread allocate again what it freed without a lock; it is why binary-trees, which allocates and frees a node at a time, runs in less time than C's, which calls `malloc` and `free`. It does more than the C does: every integer operation is checked for overflow and every index for its bounds, checks and all at C's speed or better. A check leaves only a branch and one call where it is, so that a function with several stays small enough to inline, and small functions are offered to the C compiler and to LLVM to inline.

On binary-trees Flyscript holds the memory C does. A node is an enum, `#Leaf | #Node(Box<Tree>, Box<Tree>)`, laid out as its two boxes, `#Leaf` the first one null, as Rust lays out `Option<Box<T>>` (§11.3): 16 bytes, as C's node of two pointers is. With a tag of its own beside them it took 24, which the allocator rounds to 32, and twice C's memory.

Compiled to JavaScript, Flyscript runs 1.3 to 2.4 times as long as the hand-written JavaScript, in about the same memory. The difference is again the checks, which JavaScript's own numbers do not make: each integer operation is checked against its type's range, and each index against the list's length, through small functions of the program's own that V8 inlines.

## The compiler

The compiler is 28,813 lines of Flyscript, plus the standard library it compiles with it. Compiled natively it checks and compiles itself in 1.2 seconds through LLVM and 1.45 through C, in 250 MB; compiled to JavaScript, it does so on Node in 5.2 seconds. It was 24,225 lines compiling itself in 0.81 and 0.89 seconds before a panic ended its task rather than the program (step 13): the unwinding its cleanups need, and the stack checks, cost about a sixth, and the rest is the compiler grown by a fifth. It took 4.0 and 11.8 seconds until the changes the roadmap's step 8 describes: the properties of a nominal type that do not depend on its arguments worked out once for the program, a method looked up among the methods of its name, a trial unification undone along a trail rather than by copying every binding, what was copied lent instead, and the runtime's own allocator. With `--watch` it keeps the program between builds, and a change to the body of one of its checker's functions is compiled again in about 100 milliseconds. Built through LLVM on every core, the compiler takes 5.5 seconds from its source to an executable, where one module optimized on one core took 19.

## Tasks

What a task costs, against Rust on tokio (`bench/tasks.sh`): a million tasks parked at once, each on a timer, by the peak resident memory and the time to park and wake them all; and two tasks' messages, and a lock, by time.

| | Flyscript, through LLVM | Rust, tokio |
| :--- | ---: | ---: |
| A million tasks, each parked in its own closure | 248 MB, 2.1 s | 256 MB, 2.4 s |
| A million tasks, each parked two calls deep, in a handler and the helper it waits in | 324 MB, 2.4 s | 501 MB, 2.4 s |
| Half a million round trips between two tasks over channels | 49 ms | 67 ms |
| Twenty million locks of a `Mutex` no other task contends | 110 ms | 90 ms (`std::sync::Mutex`, which never suspends); 340 ms (`tokio::sync::Mutex`, which may) |

A task is a state machine whose frame keeps only what is live across the points it stops at, the frames of the functions it calls directly nested in it, as a Rust future nests the futures it awaits (§11.3); there is no `async`, and nothing to `await`. Its record is 176 bytes, and its timer is the wait record in its frame, as tokio keeps a task's timer in its future. Parked two calls deep, as a connection handler parks, a task takes two thirds of what a tokio task takes. A task woken by the one running runs next on the same core, so two tasks answering each other take turns there without waking another worker. Each lock is also a scheduling point, at which a cancellation would be delivered and other tasks given a turn, which Rust's lock is not: the point with nothing to do, and the lock free, are a test and one atomic operation inline, and the body is inlined where it is called. What is left is that a point a task may stop at keeps the task's values in its frame rather than in registers. Rust's lock that may suspend, as ours may, is tokio's, and it takes three times as long.

## A web app

The todo app in [examples/todo](../examples/todo/) is built twice, with FlyNext and, page for page, with Next.js 16.4.2 and React 19.3.1 in [bench/next](../bench/next/), each in production mode, each with the same middleware — a redirect, and a cookie remembered from the address — and the same titles and descriptions in each page's head. `bench/web.sh` loads each server with wrk for ten seconds at a time, over 64 connections kept alive, from four client threads on the same machine. FlyNext's server runs on one core, then on all 30; Next.js runs as Node does, its JavaScript on one thread.

| Server | Page `/` | Page `/todos/2` | Page `/about`, the same for every request | JSON endpoint `/api/todos` | Memory after |
| :--- | :--- | :--- | :--- | :--- | ---: |
| FlyNext, 1 core | 120,838 req/s, p50 0.52 ms, p99 0.65 ms | 127,724 req/s, p50 0.49 ms, p99 0.60 ms | 190,691 req/s, p50 0.33 ms, p99 0.51 ms | 180,741 req/s, p50 0.34 ms, p99 0.72 ms | 3 MB |
| FlyNext, every core | 115,121 req/s, p50 0.39 ms, p99 0.73 ms | 116,650 req/s, p50 0.38 ms, p99 0.68 ms | 121,615 req/s, p50 0.37 ms, p99 0.64 ms | 117,655 req/s, p50 0.38 ms, p99 0.71 ms | 13 MB |
| Next.js | 2,459 req/s, p50 24.94 ms, p99 110.77 ms | 2,173 req/s, p50 28.81 ms, p99 53.46 ms | 7,080 req/s, p50 8.53 ms, p99 13.00 ms | 7,316 req/s, p50 7.95 ms, p99 53.66 ms | 626 MB |

On one core, FlyNext renders 49 to 59 times as many pages a second as Next.js and answers 25 times as many calls of an endpoint, with a p99 latency under a millisecond where Next.js's pages take 53 to 111, in 3 MB of memory to Next.js's 626 MB. No request failed on either. Middleware costs FlyNext 2 to 4 percent of its pages a second, being a call on the request's own stack; with it, Next.js serves 19 to 43 percent fewer. A page the same for every request — `/about`, whose model is its `initial` — each renders once and serves from then on: Next.js as it builds, FlyNext as its server starts, which answers it 27 times as often. Each FlyNext page renders inside the handlers of the request — its headers, cookies and redirects — and of the view; their arms each resume where they end or end the `handle`, so they run as calls on the request's own stack, with no frame of their own.

On every core FlyNext answers no more requests than on one, because the load generator shares the machine: client and server contend for the same cores and the same loopback interface, and past a few server threads the contention costs more than the threads add. Go's `net/http`, serving the same page on the same machine to the same load, shows the same curve, and FlyNext stays ahead of it at every size:

| Server threads | 2 | 8 | 30 |
| :--- | ---: | ---: | ---: |
| FlyNext | 198,000 req/s | 155,000 req/s | 115,000 req/s |
| Go `net/http` (`GOMAXPROCS`) | 179,000 req/s | 149,000 req/s | 93,000 req/s |

In the browser, each site's first page is loaded with nothing cached, and a link to another page followed:

| Site | Scripts | Downloaded | Gzipped | Interactive after | Link followed in |
| :--- | ---: | ---: | ---: | ---: | ---: |
| FlyNext | 3 | 82 KB | 32 KB | 24 ms | 67 ms |
| Next.js | 7 | 454 KB | 135 KB | 35 ms | 78 ms |

A FlyNext page is interactive once its program has taken over the HTML the server rendered: a core of 50 KB, 20 KB compressed, which every page shares, and the page's own module, 3 to 18 KB, which the page names for the browser to fetch beside the core and which the core links in as it shows the page (the roadmap's step 6). The list page downloads a quarter as much as the Next.js page, and is ready sooner. Built as one program for every page it was 146 KB, 41 KB compressed, and ready in 27 milliseconds: splitting it costs nothing to see. Of the core, the C library is 7 KB: the runtime prints and panics with no `printf`, and allocates from its own allocator rather than `dlmalloc` (step 7). Following a link costs both sites a request for the next page's data and a render in place, and FlyNext the next page's module the first time, which it asks for with the data as soon as the link is pointed at.

A page's program redraws by rendering its view again into a flat record of what it shows and diffing that against the last, in its own memory, and changes only what differs. In [bench/table](../bench/table/), a page of a thousand keyed rows, a click that changes one counter is shown in 2.0 milliseconds, and one that reverses the rows in 2.5, timed from the click to the change in the page (`bench/table/diff.js`, the median of thirty). Before each element's record knew where its children end, keyed rows were matched by one lookup, and text went to the page from where it lies in the program's memory, uncopied, the same changes took 2.7 and 7.8 milliseconds.

## Running them

```sh
sh bench/run.sh                        # the programs; results in target/bench/results.md
sh bench/tasks.sh                      # parked tasks, messages and locks, against Rust on tokio
NODE_PATH=…/node_modules sh bench/web.sh   # the web app, with Playwright where NODE_PATH points
sh web/flynext build bench/table/app /tmp/table && sh web/flynext start /tmp/table 4317 &
NODE_PATH=…/node_modules node bench/table/diff.js 4317   # a thousand rows redrawn
```

`bench/run.sh` needs clang, rustc, Go, Node and hyperfine; `bench/tasks.sh` clang, LLVM's tools and cargo, with tokio; `bench/web.sh` needs Node and npm for the Next.js build, wrk, and Playwright for the browser part. `RUNS`, `SECS` and `CONNS` change the number of runs, the seconds under load and the connections.
