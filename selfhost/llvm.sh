#!/bin/sh
# Compiles a Flyscript program to a native executable through LLVM: `selfhost/llvm.sh compiler.js
# program.fly out [--freestanding] [cc flags...]`, or to an object file to link, for an `out` ending
# in `.o`. The compiler writes the program's code as an LLVM module and the C it links with — the
# runtime, and what the module calls of it — beside it; the two are linked into one module before
# they are optimized together, so the calls between them are inlined. The cc flags choose the
# target, as for C. Needs clang and llvm-link of one LLVM version: LLVM_BIN, or Homebrew's llvm.
set -e
root=$(cd "$(dirname "$0")/.." && pwd)
bin=${LLVM_BIN:-$(brew --prefix llvm 2>/dev/null)/bin}
compiler=$1; program=$2; out=$3
shift 3
mode=""
[ "$1" = "--freestanding" ] && { mode=--freestanding; shift; }
node --stack-size=65500 "$compiler" "$program" "$out.ll" "$root" $mode
# The C is made LLVM IR without optimizing it: the two are optimized once, together.
"$bin/clang" -std=gnu11 -w -g -O2 -Xclang -disable-llvm-passes -S -emit-llvm "$@" "$out.c" -o "$out.c.ll"
# The module takes the target the C compiler chose, and its functions the attributes of C's for it,
# without which the two would not inline into each other.
grep -E '^target (datalayout|triple)' "$out.c.ll" > "$out.target.ll"
target=""
for a in frame-pointer target-cpu target-features tune-cpu; do
  target="$target $(grep -m1 -o "\"$a\"=\"[^\"]*\"" "$out.c.ll" || true)"
done
# Under the address sanitizer, the module's functions are checked as C's are.
case " $* " in *-fsanitize=*address*) target="$target sanitize_address" ;; esac
sed "s/^attributes #0 = { nounwind }/attributes #0 = { nounwind$target }/" "$out.ll" | cat "$out.target.ll" - > "$out.prog.ll"
"$bin/llvm-link" "$out.c.ll" "$out.prog.ll" -o "$out.bc"
case "$out" in
  *.o) "$bin/clang" -g -O2 "$@" -c "$out.bc" -o "$out" ;;
  *) "$bin/clang" -g -O2 "$@" "$out.bc" -o "$out" -lm ;;
esac
rm -f "$out.ll" "$out.c" "$out.c.ll" "$out.target.ll" "$out.prog.ll" "$out.bc"
