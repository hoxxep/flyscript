#!/bin/sh
# Compiles a Flyscript program to WebAssembly for WASI: `selfhost/wasm.sh compiler.js program.fly
# out.wasm [--imports]`, then `node selfhost/wasm.js out.wasm args...` runs it. The program's code
# is made through LLVM, as natively (selfhost/llvm.sh), for 32-bit pointers. With `--imports`, the
# functions of C's the program declares are its host's, as a page's are (web/flynext.js).
# Needs what selfhost/llvm.sh needs, with the wasm32 target, wasm-ld, and a WASI sysroot and
# compiler runtime: WASI_SYSROOT and WASI_BUILTINS, or Homebrew's wasi-libc and wasi-runtimes.
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
sysroot=${WASI_SYSROOT:-$(brew --prefix wasi-libc 2>/dev/null)/share/wasi-sysroot}
builtins=${WASI_BUILTINS:-$(ls "$(brew --prefix wasi-runtimes 2>/dev/null)"/share/wasi-runtimes/lib/wasm32-unknown-wasip1/libclang_rt.builtins.a 2>/dev/null | head -1)}
out=$3
imports=""
opt="-O2"
link=""
# A page's program is downloaded: it is made small, and its names left out.
if [ "$4" = "--imports" ]; then
  imports="--allow-undefined"
  opt="-Os -ffunction-sections -fdata-sections"
  link="--gc-sections --strip-all"
fi
# shellcheck disable=SC2086
sh "$root/selfhost/llvm.sh" "$1" "$2" "$out.o" --target=wasm32-wasip1 --sysroot="$sysroot" $opt
wasm-ld -m wasm32 $imports $link "$sysroot/lib/wasm32-wasip1/crt1-command.o" "$out.o" -L"$sysroot/lib/wasm32-wasip1" -lc "$builtins" \
  --export=__stack_pointer --export=fly_fiber_run --export=fly_fiber_top -z stack-size=8388608 -o "$out"
rm -f "$out.o"
