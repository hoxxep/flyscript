# The Flyscript compiler, in Flyscript

This directory is a complete Flyscript compiler written in Flyscript. It parses, elaborates and checks the whole language — types, effects and ownership — and compiles a program to JavaScript, to C, from which `cc` builds a native executable, or to LLVM IR. It compiles itself: `seed.js` is this compiler, compiled by itself to JavaScript, and the C it makes of itself builds a native compiler that makes the same C again, byte for byte; so does the compiler built through LLVM.

## Using it

```sh
# JavaScript
node --stack-size=65500 selfhost/seed.js program.fly program.js .
node program.js

# a native executable
node --stack-size=65500 selfhost/seed.js program.fly program.c .
cc -std=gnu11 -O2 -o program program.c -lm
./program

# a native executable through LLVM, with debug information
sh selfhost/llvm.sh selfhost/seed.js program.fly program
./program
```

The last argument is the directory holding `std/` and `selfhost/`. A program's `main` takes the command line, each parameter as its type reads it, and a last parameter that is a list of strings takes every argument left.

## How it is put together

| File | What it does |
| :--- | :--- |
| `lex.fly`, `parse.fly`, `ast.fly` | Tokens and the syntax tree. `if (const …)` chains, `while (const …)` and other sugar become `match`es here. |
| `env.fly`, `types.fly`, `schemes.fly` | The program: modules, declarations, types and generic schemes, loaded from the entry module and the standard library. |
| `subst.fly`, `traits.fly`, `impls.fly` | Unification over rows and effects, interface resolution, `comptime` specialization of impls. |
| `comptime.fly` | The `comptime` interpreter: reflection, generated fields, arms and items. |
| `check.fly`, `typecheck.fly` | Type and effect inference and checking, recording what code generation needs about every expression. |
| `own.fly` | The ownership pass: moves, borrows, two-phase lending, what each `match` arm binds, and where values die. |
| `ir.fly`, `lower.fly` | The core IR, and the lowering of a checked program into it, below. |
| `c.fly`, `runtime.h`, `runtime.c` | The C back end: a printer of the IR. |
| `llvm.fly` | The LLVM back end: a printer of the IR as LLVM IR, which calls the C back end's library routines through C it prints beside it. |
| `js.fly`, `runtime.js` | The JavaScript back end: a printer of the IR, with effect handlers, generators and tasks as JavaScript generators. |
| `main.fly` | The driver: check, then compile to the back end the output path names. |

## The core IR

Lowering starts at `main` and makes one function for each function and set of generic arguments it reaches, so every type is known. Each is lowered once into structured statements over numbered locals: every expression taken apart in evaluation order, every read a copy or a move, every borrow naming the place it lends, every conversion and every call explicit, with whether the call may fail or suspend. This is where the language's semantics are decided for every back end: evaluation order, what a pattern tests and binds, which cleanups each way out of a block runs.

Ownership is lexical. Each block owns the locals it declares, the `defer`s registered in it and the region arenas it opens, and every way out of it — its end, `break`, `return`, a failure, an unwinding — runs its cleanups, the last registered first. A moved value is dead, and dropping a dead value does nothing.

## The C back end

Values are C's own: integers, floats and structs by value; a tag union is a tag and a union of payloads, its tags numbered across the program so a narrowed union widens by copying. There is no garbage collector: a value that owns memory is dead when it is all zero bits, so a move zeroes what it moves from. A block's cleanups are written out at each jump that leaves it, and failures and unwindings go from block to block through one way out each; as it prints, the back end follows which owned locals may hold a value, so each way out drops only those.

Failures propagate by checked `goto` to the nearest `catch`. A `for` over a generator turns its body into a function the generator calls with each item. Effect handlers, continuations, `generate` and tasks run on fibers, stacks of their own switched by a few instructions of assembly, with the task scheduler mirroring the reference implementation's exactly, so a seed reproduces an interleaving on every implementation. Regions are bump arenas passed to the functions that allocate in them.

`corpus.sh --c --leaks` builds every test program natively with the address and undefined-behavior sanitizers and checks for leaks; each prints what the reference implementation prints.

## The LLVM back end

Writing an output path ending in `.ll` makes the program's code an LLVM module, and beside it a C file with the runtime and what the module calls of it: the C back end's library routines, its drop functions, the program's entry. Every local lives in memory of its own, which LLVM's `mem2reg` makes registers; each structured statement becomes basic blocks, with the C back end's cleanups and its tracking of what may hold a value at each way out. The data are C's: the module lays out every type as the C back end declares it, and the C file checks each layout the module relies on with `_Static_assert`, so the two cannot drift apart.

The two sides pass values their own ways — the module a scalar as it is and anything bigger by pointer, C as C does — and functions in the C file translate between them. `llvm.sh` makes the C file LLVM IR without optimizing it, links the two modules into one, and optimizes that, so the translations inline away. Integer arithmetic uses LLVM's overflow intrinsics, the exact value of what overflowed computed only on the way to the panic that shows it. Debug information maps each instruction to its line, each variable to its place, and each type to how Flyscript writes it, tagged unions showing their tags by name.

`corpus.sh --llvm` builds every test program through LLVM with the sanitizers. `examples/kernel/run.sh --llvm` builds the kernel through LLVM, cross-compiled for AArch64.

## WebAssembly

`wasm.sh` compiles a program's C to WebAssembly for WASI with clang, and `wasm.js` runs it under Node. WebAssembly cannot switch stacks itself, so the host does: each fiber runs as a call of its own, with JavaScript promise integration, on a shadow stack of its own in linear memory. The compiler compiles itself as WebAssembly to the same C as anywhere else.

## The JavaScript back end

Values are JavaScript's: a struct an object, a list an array, a tag `{ $tag, $ }`, a `readonly` borrow the value it lends and a `mut` borrow a reference whose `v` reads and writes the place. A block's cleanups run in a `finally`, and only what a destructor can observe is dropped. A function that may suspend is a generator, and a loop over a generator steps it, passing on what it performs besides its items.

## Building the compiler

`bootstrap.sh` compiles the compiler with the seed, then with the result, and checks the two agree; `--update-seed` makes the result the new seed. `bootstrap.sh --from-flyc` starts instead from `flyc`, the reference implementation in Rust, which runs the compiler's source directly.
