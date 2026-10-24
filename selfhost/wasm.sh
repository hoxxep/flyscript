#!/bin/sh
# Compiles a Flyscript program to WebAssembly for WASI: `selfhost/wasm.sh compiler.js program.fly
# out.wasm [--imports | --split dir prefix]`, then `node selfhost/wasm.js out.wasm args...` runs
# it. The program's code is made through LLVM, as natively (selfhost/llvm.sh), for 32-bit pointers.
# With `--imports`, the functions of C's the program declares are its host's, as a page's are
# (web/flynext.js). With `--split`, a page's program too, made a core and a module for each of the
# functions whose names start with `prefix` and a number (selfhost/wasm-split.js), in `dir`:
# `route<k>.<hash>.wasm`, and `routes.json`, which says which file and function each is.
# Needs what selfhost/llvm.sh needs, with the wasm32 target, wasm-ld, and a WASI sysroot and
# compiler runtime: WASI_SYSROOT and WASI_BUILTINS, or Homebrew's wasi-libc and wasi-runtimes.
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
bin=${LLVM_BIN:-$(brew --prefix llvm 2>/dev/null)/bin}
sysroot=${WASI_SYSROOT:-$(brew --prefix wasi-libc 2>/dev/null)/share/wasi-sysroot}
builtins=${WASI_BUILTINS:-$(ls "$(brew --prefix wasi-runtimes 2>/dev/null)"/share/wasi-runtimes/lib/wasm32-unknown-wasip1/libclang_rt.builtins.a 2>/dev/null | head -1)}
out=$3
imports=""
# A panic unwinds through landing pads, by WebAssembly's exceptions (runtime.h).
eh="-fwasm-exceptions"
opt="-O2 $eh"
link=""
# A page's program is downloaded: it is made small, and its names left out.
if [ "$4" = "--imports" ] || [ "$4" = "--split" ]; then
  imports="--allow-undefined"
  opt="-Os -ffunction-sections -fdata-sections $eh"
  link="--gc-sections --strip-all"
fi
libc="$sysroot/lib/wasm32-wasip1/crt1-command.o"
exports="--export=__stack_pointer --export=fly_fiber_run --export=fly_fiber_top -z stack-size=8388608"
if [ "$4" != "--split" ]; then
  # shellcheck disable=SC2086
  sh "$root/selfhost/llvm.sh" "$1" "$2" "$out.o" --target=wasm32-wasip1 --sysroot="$sysroot" $opt
  # shellcheck disable=SC2086
  wasm-ld -m wasm32 $imports $link "$libc" "$out.o" -L"$sysroot/lib/wasm32-wasip1" -lc "$builtins" $exports -o "$out"
  rm -f "$out.o"
  exit 0
fi

# Split: the whole program optimized as one, the routes' functions kept whole, then cut apart.
dir=$5
prefix=$6
work="$out.split"
rm -rf "$work"
mkdir -p "$work" "$dir"
# shellcheck disable=SC2086
sh "$root/selfhost/llvm.sh" "$1" "$2" "$work/app.bc" --target=wasm32-wasip1 --sysroot="$sysroot" $opt
"$bin/llvm-dis" "$work/app.bc" -o "$work/app.ll"
routes=$(grep -oE "^define [^@]*@${prefix}[0-9]+_[0-9]+__fly\(" "$work/app.ll" | grep -oE "@[^(]*" | tr -d @ | sort -u | paste -sd, -)
sed -E "s/^(define [^@]*@${prefix}[0-9]+_[0-9]+__fly\(.*\)) (#[0-9]+)/\1 noinline \2/" "$work/app.ll" > "$work/app.kept.ll"
"$bin/opt" -strip-debug -passes='internalize,name-anon-globals,default<O2>' \
  -internalize-public-api-list='_start,__main_void,__main_argc_argv,malloc,free,calloc,realloc,fly_fiber_run,fly_fiber_top' \
  -internalize-public-api-list="$routes" "$work/app.kept.ll" -S -o "$work/app.opt.ll"
node "$root/selfhost/wasm-split.js" "$work/app.opt.ll" "$work" "${prefix}(\\d+)_"
"$bin/llvm-as" "$work/all.ll" -o "$work/all.bc"
"$bin/llvm-extract" --delete $(cat "$work/core.args") "$work/all.bc" -o "$work/core0.bc"
"$bin/llvm-as" "$work/stubs.ll" -o "$work/stubs.bc"
"$bin/llvm-link" "$work/core0.bc" "$work/stubs.bc" -o "$work/core.bc"
"$bin/clang" --target=wasm32-wasip1 -O2 $eh -ffunction-sections -fdata-sections -c "$work/core.bc" -o "$work/core.o"
# The core gives the routes its memory, its table of functions, and what they take of its own.
take=""
for s in $(cat "$work/exports.txt") calloc; do take="$take --export-if-defined=$s"; done
# A route whose landing pads run as a panic passes takes the tag a panic is thrown with, which is
# the core's (runtime.c).
for s in $(cat "$work/undefined.txt") __cpp_exception; do take="$take --undefined=$s --export-if-defined=$s"; done
# shellcheck disable=SC2086
wasm-ld -m wasm32 $imports $link "$libc" "$work/core.o" -L"$sysroot/lib/wasm32-wasip1" -lc "$builtins" $exports \
  --export-table --growable-table $take -o "$out"
manifest="{"
for k in $(cat "$work/routes.txt"); do
  fn=$(grep -oE "^--func=${prefix}${k}_[0-9]+__fly$" "$work/route$k.args" | sed 's/^--func=//')
  "$bin/llvm-extract" $(cat "$work/route$k.args") "$work/all.bc" -o "$work/route$k.0.bc"
  # What is the route's alone is its own: only what is the core's is reached through the loader.
  "$bin/opt" -passes='internalize,globaldce' -internalize-public-api-list="$fn" "$work/route$k.0.bc" -o "$work/route$k.bc"
  "$bin/clang" --target=wasm32-wasip1 -O2 $eh -fPIC -ffunction-sections -fdata-sections -c "$work/route$k.bc" -o "$work/route$k.o"
  wasm-ld -m wasm32 --experimental-pic -shared --unresolved-symbols=import-dynamic --strip-all "$work/route$k.o" -o "$work/route$k.wasm"
  hash=$(shasum -a 256 "$work/route$k.wasm" | cut -c1-12)
  cp "$work/route$k.wasm" "$dir/route$k.$hash.wasm"
  [ "$manifest" = "{" ] || manifest="$manifest,"
  manifest="$manifest\"$k\":{\"file\":\"route$k.$hash.wasm\",\"fn\":\"$fn\"}"
done
echo "$manifest}" > "$dir/routes.json"
rm -rf "$work"
