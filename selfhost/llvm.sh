#!/bin/sh
# Compiles a Flyscript program to a native executable through LLVM: `selfhost/llvm.sh compiler
# program.fly out [--freestanding] [cc flags...]`, the compiler its JavaScript or a native build,
# or to an object file to link, for an `out` ending in `.o`, or to the linked module, not yet
# optimized, for one in `.bc`. The compiler writes the program's code as an LLVM module and the C
# it links with — the runtime, and what the module calls of it — beside it; the two are linked into one module before
# they are optimized together, so the calls between them are inlined. The cc flags choose the
# target, as for C. Needs clang and llvm-link of one LLVM version: LLVM_BIN, or Homebrew's llvm.
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
bin=${LLVM_BIN:-$(brew --prefix llvm 2>/dev/null)/bin}
# What every build of the C adds (selfhost/ccflags.sh), and the same to the linker's code generation.
ccflags=$(sh "$root/selfhost/ccflags.sh" "$bin/clang")
ldflags=$(for f in $ccflags; do printf ' -Wl,%s' "$f"; done)
compiler=$1; program=$2; out=$3
shift 3
mode=""
[ "$1" = "--freestanding" ] && { mode=--freestanding; shift; }
# For WebAssembly the module's pointers are 32 bits, as the target's are.
case " $* " in *--target=wasm32*) mode="$mode --wasm32" ;; esac
# The compiler is its JavaScript, run by Node, or a native build of it.
case "$compiler" in
  *.js) node --stack-size=65500 "$compiler" "$program" "$out.ll" "$root" $mode ;;
  *) "$compiler" "$program" "$out.ll" "$root" $mode ;;
esac
# Native code unwinds a panic by the platform's tables, through landing pads (runtime.h): its C has
# them too. WebAssembly and freestanding programs do not.
eh="-fexceptions -funwind-tables -DFLY_LANDING_PADS"
case " $mode " in *--wasm32*|*--freestanding*) eh="" ;; esac
# The C is made LLVM IR without optimizing it: the two are optimized once, together.
"$bin/clang" -std=gnu11 -w -g -O2 $eh -Xclang -disable-llvm-passes -S -emit-llvm "$@" "$out.c" -o "$out.c.ll"
# The module takes the target the C compiler chose, and its functions the attributes of C's for it,
# without which the two would not inline into each other.
grep -E '^target (datalayout|triple)' "$out.c.ll" > "$out.target.ll"
target=""
for a in frame-pointer target-cpu target-features tune-cpu; do
  target="$target $(grep -m1 -o "\"$a\"=\"[^\"]*\"" "$out.c.ll" || true)"
done
# Made small, the module's functions are, as C's are.
case " $* " in *" -Os "*) target="$target optsize" ;; *" -Oz "*) target="$target optsize minsize" ;; esac
# Under a sanitizer, the module's functions are checked as C's are.
case " $* " in *-fsanitize=*address*) target="$target sanitize_address" ;; esac
case " $* " in *-fsanitize=*thread*) target="$target sanitize_thread" ;; esac
sed -E "s/^attributes #0 = \{ (nounwind|uwtable) \}/attributes #0 = { \1$target }/" "$out.ll" | cat "$out.target.ll" - > "$out.prog.ll"
# For an `out` ending in `.bc`, the linked module, not yet optimized, is what is made.
case "$out" in
  *.bc)
    "$bin/llvm-link" "$out.c.ll" "$out.prog.ll" -o "$out"
    rm -f "$out.ll" "$out.c" "$out.c.ll" "$out.target.ll" "$out.prog.ll"
    exit 0 ;;
esac
"$bin/llvm-link" "$out.c.ll" "$out.prog.ll" -o "$out.bc"
# An executable for the machine is built on every core: the module is split into a part per core,
# each optimized and compiled apart, then optimized again across the parts as they are linked, by
# ThinLTO, which inlines between them as one module would. An object file, a build for another
# target, and a build under a sanitizer are compiled as one module.
jobs=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 1)
split=true
case "$out" in *.o) split=false ;; esac
case " $* " in *--target=*|*-fsanitize=*) split=false ;; esac
lld() { [ -x "$bin/$1" ] || command -v "$1" > /dev/null 2>&1; }
[ "$jobs" -gt 1 ] && [ -x "$bin/llvm-split" ] && { lld ld64.lld || lld ld.lld; } || split=false
if $split; then
  parts="$out.parts"
  mkdir -p "$parts"
  "$bin/llvm-split" -j "$jobs" -o "$parts/p" "$out.bc"
  ls "$parts"/p* | xargs -P "$jobs" -I{} "$bin/clang" -x ir -g -O2 -flto=thin $ccflags "$@" -c {} -o {}.o
  "$bin/clang" -g -O2 -flto=thin -fuse-ld=lld -Wl,--thinlto-jobs="$jobs" $ldflags "$@" "$parts"/p*.o -o "$out" -lm
  rm -f "$parts"/p*
  rmdir "$parts"
else
  case "$out" in
    *.o) "$bin/clang" -g -O2 $ccflags "$@" -c "$out.bc" -o "$out" ;;
    *) "$bin/clang" -g -O2 $ccflags "$@" "$out.bc" -o "$out" -lm ;;
  esac
fi
rm -f "$out.ll" "$out.c" "$out.c.ll" "$out.target.ll" "$out.prog.ll" "$out.bc"
