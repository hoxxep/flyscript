#!/bin/sh
# Compiles a Flyscript program to WebAssembly for WASI: `selfhost/wasm.sh compiler.js program.fly
# out.wasm`, then `node selfhost/wasm.js out.wasm args...` runs it. Needs clang with the wasm32
# target, wasm-ld, and a WASI sysroot and compiler runtime: WASI_SYSROOT and WASI_BUILTINS, or
# Homebrew's wasi-libc and wasi-runtimes.
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
sysroot=${WASI_SYSROOT:-$(brew --prefix wasi-libc 2>/dev/null)/share/wasi-sysroot}
builtins=${WASI_BUILTINS:-$(ls "$(brew --prefix wasi-runtimes 2>/dev/null)"/share/wasi-runtimes/lib/wasm32-unknown-wasip1/libclang_rt.builtins.a 2>/dev/null | head -1)}
out=$3
node --stack-size=65500 "$1" "$2" "$out.c" "$root"
clang --target=wasm32-wasip1 --sysroot="$sysroot" -std=gnu11 -O2 -w -c "$out.c" -o "$out.o"
wasm-ld -m wasm32 "$sysroot/lib/wasm32-wasip1/crt1-command.o" "$out.o" -L"$sysroot/lib/wasm32-wasip1" -lc "$builtins" \
  --export=__stack_pointer --export=fly_fiber_run --export=fly_fiber_top -z stack-size=8388608 -o "$out"
rm -f "$out.c" "$out.o"
