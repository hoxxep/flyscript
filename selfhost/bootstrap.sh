#!/usr/bin/env bash
# Builds the self-hosted compiler and checks that it reproduces itself.
#   stage 1: the seed (selfhost/seed.js, the compiler compiled by itself) compiles the source
#   stage 2: stage 1 compiles the same source again
# The two must be the same file.
#   --from-flyc     builds stage 1 with the reference implementation, `flyc run`, instead
#   --update-seed   makes stage 2 the seed, after a change to the compiler
# A change to how the runtime represents values needs one step more: the seed's code expects the
# runtime it was built with, so build stage 1 against a root holding that runtime (`git show
# HEAD:selfhost/runtime.js`, with `std/` beside it), then bootstrap from stage 1.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$here/.."
out="$root/target/selfhost"
from_flyc=false
update=false
for arg in "$@"; do
  case "$arg" in
    --from-flyc) from_flyc=true ;;
    --update-seed) update=true ;;
    *) echo "usage: $0 [--from-flyc] [--update-seed]" >&2; exit 2 ;;
  esac
done
mkdir -p "$out"
compile() { node --stack-size=65500 "$1" "$here/main.fly" "$2" "$root"; }
if $from_flyc; then
  cargo build -q --release --manifest-path "$root/Cargo.toml"
  "$root/target/release/flyc" run "$here/main.fly" main "$here/main.fly" "$out/stage1.js" "$root"
else
  compile "$here/seed.js" "$out/stage1.js"
fi
compile "$out/stage1.js" "$out/stage2.js"
cmp "$out/stage1.js" "$out/stage2.js"
echo "fixpoint: $out/stage2.js ($(wc -l < "$out/stage2.js") lines)"
if $update; then
  cp "$out/stage2.js" "$here/seed.js"
  echo "seed updated"
fi
