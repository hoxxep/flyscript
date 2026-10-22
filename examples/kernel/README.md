# A kernel in Flyscript

A small kernel for QEMU's AArch64 `virt` board, written in Flyscript, compiled with `--freestanding`: no operating system and no C library under it.

- It turns on address translation with a page table it builds itself, an `@layout(c, align = 4096)` struct.
- It writes to the console through the UART's registers, with volatile writes through raw pointers.
- It is its own memory allocator: a first-fit allocator over raw memory, written in Flyscript, is what the runtime asks for memory.
- Allocation that can fail says so: asking for more memory than there is fails with `#OutOfMemory`, which the kernel catches and goes on.
- A spinlock built from `compareExchange` and `storeRelease` is released by `defer`, however its block is left.
- Scratch memory comes from a region, given back all at once.
- An effect handler resumes work that logs through it: the work runs on a fiber of its own, inside the kernel.

The code an interrupt runs is a function C calls, which performs nothing: the compiler rejects a call to anything that may sleep from it (see `tests/reject/interrupt_cannot_sleep.fly`).

```sh
examples/kernel/run.sh
```

It needs clang, `ld.lld` and `qemu-system-aarch64`. `boot.S` sets up a stack, turns on floating point, and offers three routines: the heap's bounds, turning translation on, and leaving QEMU through semihosting.
