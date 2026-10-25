# Performance

Flyscript compiles to C, through LLVM, and to JavaScript, and runs its tasks on a scheduler of its own. This page measures what that costs: five benchmark programs against C, Rust, Go and JavaScript; the compiler compiling itself; and a web app built with [FlyNext](../web/) against the same app built with Next.js and React. Every number comes from the scripts in [bench/](../bench/), which run the same way on any machine.

## The machine

An Apple M5 Ultra with 30 cores and 96 GB, on macOS 27.0.1. Apple clang 21 at `-O2`, rustc 1.98.1 with `-O`, Go 1.27.2, Node 24.21.0. Programs are timed by hyperfine 2.0, the median of five runs after one to warm up, and their peak resident memory recorded; servers are loaded by wrk 4.2; pages are measured in Playwright's Chromium.

## Programs

`bench/run.sh` builds each program each way, checks that every build prints exactly what the C one prints, and times them. Flyscript (C) is the compiler's C through clang; Flyscript (LLVM) is its LLVM IR, linked with the runtime and optimized as one program; Flyscript (JS) is its JavaScript on Node. The other columns are the same programs written by hand in each language.

| Benchmark | Flyscript (C) | Flyscript (LLVM) | Flyscript (JS) | C | Rust | Go | JavaScript |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-trees, depth 18 | 487 ms | 494 ms | 881 ms | 598 ms | 622 ms | 513 ms | 369 ms |
| fannkuch-redux, 11 | 1396 ms | 1392 ms | 2685 ms | 1448 ms | 1512 ms | 1368 ms | 1678 ms |
| n-body, 5 million steps | 134 ms | 138 ms | 483 ms | 128 ms | 133 ms | 142 ms | 215 ms |
| spectral-norm, 3000 | 321 ms | 320 ms | 733 ms | 263 ms | 209 ms | 285 ms | 394 ms |
| word frequencies, 3 million words | 112 ms | 116 ms | 740 ms | 159 ms | 84 ms | 110 ms | 563 ms |

| Peak memory | Flyscript (C) | Flyscript (LLVM) | Flyscript (JS) | C | Rust | Go | JavaScript |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-trees | 34.2 MB | 34.2 MB | 340 MB | 18.2 MB | 18.4 MB | 42.1 MB | 397 MB |
| fannkuch-redux | 2.2 MB | 2.1 MB | 49.3 MB | 2.1 MB | 2.2 MB | 5.1 MB | 46.1 MB |
| n-body | 2.1 MB | 2.1 MB | 50.8 MB | 2.1 MB | 2.3 MB | 4.9 MB | 48.4 MB |
| spectral-norm | 3.4 MB | 3.4 MB | 49.5 MB | 2.2 MB | 2.3 MB | 5.1 MB | 48.0 MB |
| word frequencies | 24.4 MB | 24.4 MB | 531 MB | 24.4 MB | 22.9 MB | 92.3 MB | 420 MB |

Natively, Flyscript runs faster than C on binary-trees, fannkuch-redux and word frequencies, within 5% of it on n-body, and within 22% of it on spectral-norm, with no garbage collector: every value is freed where ownership says it dies. Natively a program allocates from the runtime's own allocator, which keeps blocks in classes of sizes and lets each thread allocate again what it freed without a lock; it is why binary-trees, which allocates and frees a node at a time, runs in less time than C's, which calls `malloc` and `free`. It does more than the C does. Every integer operation is checked for overflow and every index for its bounds, and the checks are what remains of the gap on spectral-norm, whose inner loop is integer arithmetic and indexing. Rust checks bounds and not overflow, and is fastest there.

On binary-trees Flyscript holds twice the memory C does. A node is an enum, `#Leaf | #Node(Box<Tree>, Box<Tree>)`: its tag and two boxes take 24 bytes, which the allocator rounds to 32, where C's node is two pointers in 16. Keeping the tag in a box's null pointer, as Rust does for `Option<Box<T>>`, would close the gap; Flyscript does not lay enums out that way yet.

Compiled to JavaScript, Flyscript runs 1.3 to 2.4 times as long as the hand-written JavaScript, in about the same memory. The difference is again the checks, which JavaScript's own numbers do not make: each integer operation is checked against its type's range, and each index against the list's length, through small functions of the program's own that V8 inlines.

## The compiler

The compiler is 28,813 lines of Flyscript, plus the standard library it compiles with it. Compiled natively it checks and compiles itself in 1.2 seconds through LLVM and 1.45 through C, in 250 MB; compiled to JavaScript, it does so on Node in 5.2 seconds. It was 24,225 lines compiling itself in 0.81 and 0.89 seconds before a panic ended its task rather than the program (step 13): the unwinding its cleanups need, and the stack checks, cost about a sixth, and the rest is the compiler grown by a fifth. It took 4.0 and 11.8 seconds until the changes the roadmap's step 8 describes: the properties of a nominal type that do not depend on its arguments worked out once for the program, a method looked up among the methods of its name, a trial unification undone along a trail rather than by copying every binding, what was copied lent instead, and the runtime's own allocator. With `--watch` it keeps the program between builds, and a change to the body of one of its checker's functions is compiled again in about 100 milliseconds. Built through LLVM on every core, the compiler takes 5.5 seconds from its source to an executable, where one module optimized on one core took 19.

## Tasks

What a parked task takes, against Rust on tokio (`bench/tasks.sh`): a million tasks parked at once, each on a timer, the peak resident memory and the time to park and wake them all.

| | Flyscript, through LLVM | Rust, tokio |
| :--- | ---: | ---: |
| Each parked in its own closure | 413 MB, 2.7 s | 256 MB, 2.4 s |
| Each parked two calls deep, in a handler and the helper it waits in | 509 MB, 2.5 s | 501 MB, 2.5 s |

A task is a state machine whose frame keeps only what is live across the points it stops at, the frames of the functions it calls directly nested in it, as a Rust future nests the futures it awaits (§11.3); there is no `async`, and nothing to `await`. Parked two calls deep, as a connection handler parks, a task takes what a tokio task takes, within ten bytes. Parked in its own closure, it takes 160 bytes more: its record, kept by its scope and its worker's timer apart from its frame, where a tokio task keeps its timer in its future.

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

## Running them

```sh
sh bench/run.sh                        # the programs; results in target/bench/results.md
sh bench/tasks.sh                      # a million parked tasks, against Rust on tokio
NODE_PATH=…/node_modules sh bench/web.sh   # the web app, with Playwright where NODE_PATH points
```

`bench/run.sh` needs clang, rustc, Go, Node and hyperfine; `bench/tasks.sh` clang, LLVM's tools and cargo, with tokio; `bench/web.sh` needs Node and npm for the Next.js build, wrk, and Playwright for the browser part. `RUNS`, `SECS` and `CONNS` change the number of runs, the seconds under load and the connections.
