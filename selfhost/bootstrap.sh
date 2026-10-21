#!/usr/bin/env bash
# Builds the self-hosted compiler and checks that it reproduces itself.
#   stage 1: the compiler, run by flyc, compiles its own source to JavaScript
#   stage 2: stage 1, run by node, compiles the same source again
# The two must be the same file.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/../target/selfhost}"
mkdir -p "$out"
cargo build -q --release --manifest-path "$here/../Cargo.toml"
"$here/../target/release/flyc" run "$here/main.fly" main "$here/main.fly" "$out/stage1.js" "$here/runtime.js"
node "$out/stage1.js" "$here/main.fly" "$out/stage2.js" "$here/runtime.js"
cmp "$out/stage1.js" "$out/stage2.js"
echo "fixpoint: $out/stage2.js ($(wc -l < "$out/stage2.js") lines)"
