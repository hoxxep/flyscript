#!/bin/sh
# The flags every build of a program's C adds, for the C compiler `$1` (`cc` if none is named):
# -fexceptions, by which a panic runs the cleanups of each function it unwinds (runtime.c's
# FLY_C_UNWIND). With `--codegen` before the compiler, only what changes code generation, for
# llvm.sh, whose C is the runtime's and which unwinds its own way.
# On AArch64, clang's redundant copy elimination is turned off: after a 32-bit comparison of a
# union's tag, it has been seen to reuse the 64-bit register holding the tag, whose upper half
# is the padding of the value a function returned, in place of a 64-bit constant equal to the
# tag (Apple clang 21 and LLVM 23, under the sanitizers, in a function that takes up a panic).
codegen=""
[ "$1" = "--codegen" ] && { codegen=1; shift; }
c=${1:-cc}
[ -n "$codegen" ] || printf '%s ' "-fexceptions"
case "$(uname -m)" in
  arm64|aarch64) "$c" --version 2>/dev/null | grep -q clang && printf '%s' "-mllvm -aarch64-enable-copyelim=false" ;;
esac
echo
exit 0
