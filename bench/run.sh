#!/bin/sh
# Runs the benchmarks: each program in Flyscript — compiled through C, through LLVM, and to
# JavaScript — and in C, Rust, Go and JavaScript, checked to print the same, and timed by
# hyperfine. `bench/run.sh [benchmark...]`; the results go to target/bench/results.md.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
out="$root/target/bench"
mkdir -p "$out"
compiler=${FLY_COMPILER:-$root/selfhost/seed.js}
runs=${RUNS:-5}

# Each benchmark and the size it runs at.
size() {
  case "$1" in
    binary_trees) echo 18 ;;
    fannkuch) echo 11 ;;
    nbody) echo 5000000 ;;
    spectral_norm) echo 3000 ;;
    wordfreq) echo 3000000 ;;
  esac
}

all="binary_trees fannkuch nbody spectral_norm wordfreq"
[ $# -gt 0 ] && all="$*"

results="$out/results.md"
rows=""

for b in $all; do
  n=$(size "$b")
  echo "== $b $n"
  # Built every way.
  node --stack-size=65500 "$compiler" "$here/fly/$b.fly" "$out/$b.fly.c" "$root"
  cc -std=gnu11 -O2 -w -o "$out/$b.fly-c" "$out/$b.fly.c" -lm
  sh "$root/selfhost/llvm.sh" "$compiler" "$here/fly/$b.fly" "$out/$b.fly-llvm" > /dev/null
  node --stack-size=65500 "$compiler" "$here/fly/$b.fly" "$out/$b.fly.js" "$root"
  cc -O2 -w -o "$out/$b.c" "$here/c/$b.c" -lm
  rustc -O --edition 2021 -o "$out/$b.rs" "$here/rust/$b.rs" 2> /dev/null
  (cd "$here/go" && go build -o "$out/$b.go" "$b.go")
  # Each prints the same.
  "$out/$b.c" "$n" > "$out/$b.expected"
  for run in "$out/$b.fly-c $n" "$out/$b.fly-llvm $n" "node $out/$b.fly.js $n" "$out/$b.rs $n" "$out/$b.go $n" "node $here/js/$b.js $n"; do
    # shellcheck disable=SC2086
    if ! $run | cmp -s - "$out/$b.expected"; then echo "$run prints something else" >&2; exit 1; fi
  done
  rows="$rows $b=$n"
  hyperfine -N --warmup 1 --runs "$runs" --export-json "$out/$b.json" \
    -n fly-c "$out/$b.fly-c $n" -n fly-llvm "$out/$b.fly-llvm $n" -n fly-js "node $out/$b.fly.js $n" \
    -n c "$out/$b.c $n" -n rust "$out/$b.rs $n" -n go "$out/$b.go $n" -n js "node $here/js/$b.js $n" > /dev/null
done
# shellcheck disable=SC2086
node "$here/table.js" $rows | tee "$results"
