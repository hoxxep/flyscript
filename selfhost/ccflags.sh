#!/bin/sh
# The flags every build of the compiler's C adds, for the C compiler `$1` (`cc` if none is named).
# On AArch64, clang's redundant copy elimination is turned off: after a 32-bit comparison of a
# union's tag, it has been seen to reuse the 64-bit register holding the tag, whose upper half
# is the padding of the value a function returned, in place of a 64-bit constant equal to the
# tag (Apple clang 21 and LLVM 23, under the sanitizers, in a function that takes up a panic).
c=${1:-cc}
case "$(uname -m)" in
  arm64|aarch64) "$c" --version 2>/dev/null | grep -q clang && echo "-mllvm -aarch64-enable-copyelim=false" ;;
esac
exit 0
