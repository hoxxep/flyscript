# Performance

Flyscript compiles to C, through LLVM, and to JavaScript, and runs its tasks on a scheduler of its own. This page measures what that costs: five benchmark programs against C, Rust, Go and JavaScript; the compiler compiling itself; and a web app built with [FlyNext](../web/) against the same app built with Next.js and React. Every number comes from the scripts in [bench/](../bench/), which run the same way on any machine.

## The machine

An Apple M5 Ultra with 30 cores and 96 GB, on macOS 27.0.1. Apple clang 21 at `-O2`, rustc 1.98.1 with `-O`, Go 1.27.2, Node 24.21.0. Programs are timed by hyperfine 2.0, the median of five runs after one to warm up, and their peak resident memory recorded; servers are loaded by wrk 4.2; pages are measured in Playwright's Chromium.

## Programs

`bench/run.sh` builds each program each way, checks that every build prints exactly what the C one prints, and times them. Flyscript (C) is the compiler's C through clang; Flyscript (LLVM) is its LLVM IR, linked with the runtime and optimized as one program; Flyscript (JS) is its JavaScript on Node. The other columns are the same programs written by hand in each language.

| Benchmark | Flyscript (C) | Flyscript (LLVM) | Flyscript (JS) | C | Rust | Go | JavaScript |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-trees, depth 18 | 663 ms | 652 ms | 880 ms | 596 ms | 618 ms | 512 ms | 372 ms |
| fannkuch-redux, 11 | 1399 ms | 1401 ms | 2701 ms | 1456 ms | 1514 ms | 1374 ms | 1702 ms |
| n-body, 5 million steps | 135 ms | 135 ms | 478 ms | 129 ms | 133 ms | 141 ms | 215 ms |
| spectral-norm, 3000 | 327 ms | 321 ms | 762 ms | 265 ms | 217 ms | 285 ms | 390 ms |
| word frequencies, 3 million words | 139 ms | 140 ms | 754 ms | 162 ms | 85 ms | 110 ms | 566 ms |

| Peak memory | Flyscript (C) | Flyscript (LLVM) | Flyscript (JS) | C | Rust | Go | JavaScript |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binary-trees | 34.4 MB | 34.3 MB | 384 MB | 18.2 MB | 18.4 MB | 43.8 MB | 390 MB |
| fannkuch-redux | 2.1 MB | 2.1 MB | 49.2 MB | 2.1 MB | 2.2 MB | 5.0 MB | 46.2 MB |
| n-body | 2.1 MB | 2.1 MB | 50.7 MB | 2.1 MB | 2.3 MB | 5.0 MB | 48.4 MB |
| spectral-norm | 2.3 MB | 2.3 MB | 49.5 MB | 2.2 MB | 2.3 MB | 5.0 MB | 48.2 MB |
| word frequencies | 23.4 MB | 23.5 MB | 531 MB | 24.4 MB | 22.9 MB | 88.0 MB | 421 MB |

Natively, Flyscript runs faster than C on fannkuch-redux and word frequencies, within 5% of it on n-body, and within 11% and 23% of it on binary-trees and spectral-norm, with no garbage collector: every value is freed where ownership says it dies. It does more than the C does. Every integer operation is checked for overflow and every index for its bounds, and the checks are what remains of the gap on spectral-norm, whose inner loop is integer arithmetic and indexing. Rust checks bounds and not overflow, and is fastest there.

On binary-trees Flyscript holds twice the memory C does. A node is an enum, `#Leaf | #Node(Box<Tree>, Box<Tree>)`: its tag and two boxes take 24 bytes, which the allocator rounds to 32, where C's node is two pointers in 16. Keeping the tag in a box's null pointer, as Rust does for `Option<Box<T>>`, would close the gap; Flyscript does not lay enums out that way yet.

Compiled to JavaScript, Flyscript runs 1.3 to 2.4 times as long as the hand-written JavaScript, in about the same memory. The difference is again the checks, which JavaScript's own numbers do not make: each integer operation is checked against its type's range, and each index against the list's length, through small functions of the program's own that V8 inlines.

## The compiler

The compiler is 23,821 lines of Flyscript, plus the standard library it compiles with it. Compiled natively, through C or LLVM, it compiles itself in 4.0 seconds; compiled to JavaScript, it does so on Node in 11.8 seconds. Most of that time goes to allocating and freeing types: the checker represents a type as a tree of boxes and copies it wherever it substitutes one, and interning types would remove most of the work.

## A web app

The todo app in [examples/todo](../examples/todo/) is built twice, with FlyNext and, page for page, with Next.js 16.4.2 and React 19.3.1 in [bench/next](../bench/next/), each in production mode. `bench/web.sh` loads each server with wrk for ten seconds at a time, over 64 connections kept alive, from four client threads on the same machine. FlyNext's server runs on one core, then on all 30; Next.js runs as Node does, its JavaScript on one thread.

| Server | Page `/` | Page `/todos/2` | JSON endpoint `/api/todos` | Memory after |
| :--- | :--- | :--- | :--- | ---: |
| FlyNext, 1 core | 125,976 req/s, p50 0.50 ms, p99 0.63 ms | 128,255 req/s, p50 0.48 ms, p99 0.93 ms | 174,130 req/s, p50 0.36 ms, p99 0.50 ms | 3 MB |
| FlyNext, every core | 115,193 req/s, p50 0.38 ms, p99 0.72 ms | 116,851 req/s, p50 0.40 ms, p99 0.67 ms | 117,587 req/s, p50 0.38 ms, p99 0.69 ms | 17 MB |
| Next.js | 3,088 req/s, p50 20.09 ms, p99 60.03 ms | 2,612 req/s, p50 23.88 ms, p99 43.92 ms | 13,127 req/s, p50 4.48 ms, p99 9.58 ms | 511 MB |

On one core, FlyNext renders 41 to 49 times as many pages a second as Next.js and answers 13 times as many calls of an endpoint, with a p99 latency under a millisecond where Next.js's pages take 44 to 60, in 3 MB of memory to Next.js's 511 MB. No request failed on either. Each FlyNext page renders inside the handlers of the request — its headers, cookies and redirects — and of the view; their arms each resume where they end or end the `handle`, so they run as calls on the request's own stack, with no fiber of their own.

On every core FlyNext answers no more requests than on one, because the load generator shares the machine: client and server contend for the same cores and the same loopback interface, and past a few server threads the contention costs more than the threads add. Go's `net/http`, serving the same page on the same machine to the same load, shows the same curve, and FlyNext stays ahead of it at every size:

| Server threads | 2 | 8 | 30 |
| :--- | ---: | ---: | ---: |
| FlyNext | 198,000 req/s | 155,000 req/s | 115,000 req/s |
| Go `net/http` (`GOMAXPROCS`) | 179,000 req/s | 149,000 req/s | 93,000 req/s |

In the browser, each site's first page is loaded with nothing cached, and a link to another page followed:

| Site | Scripts | Downloaded | Gzipped | Interactive after | Link followed in |
| :--- | ---: | ---: | ---: | ---: | ---: |
| FlyNext | 2 | 142 KB | 46 KB | 22 ms | 74 ms |
| Next.js | 7 | 454 KB | 135 KB | 34 ms | 79 ms |

A FlyNext page is interactive once its one WebAssembly program has taken over the HTML the server rendered: it downloads a third as much as the Next.js page and is ready 12 milliseconds sooner. Following a link costs both sites a request for the next page's data and a render in place, about the same.

## Running them

```sh
sh bench/run.sh                        # the programs; results in target/bench/results.md
NODE_PATH=…/node_modules sh bench/web.sh   # the web app, with Playwright where NODE_PATH points
```

`bench/run.sh` needs clang, rustc, Go, Node and hyperfine; `bench/web.sh` needs Node and npm for the Next.js build, wrk, and Playwright for the browser part. `RUNS`, `SECS` and `CONNS` change the number of runs, the seconds under load and the connections.
