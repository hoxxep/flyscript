#!/bin/sh
# What a parked task takes: a million tasks parked at once, each on a timer, in Flyscript built
# through LLVM and in Rust on tokio, by peak resident memory and time. `parked` parks each task in
# its own closure; `parked_deep`, two calls deep, in a handler and the helper it waits in, as a
# connection handler parks. Needs clang and llvm-link (as selfhost/llvm.sh does) and cargo, with
# tokio fetched or cached. `bench/tasks.sh`.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
out="$root/target/bench/tasks"
mkdir -p "$out"
compiler=${FLY_COMPILER:-$root/selfhost/seed.js}
(cd "$here/tasks/rust" && cargo build --release -q --target-dir "$out/rust")
peak() {
  if [ "$(uname)" = Darwin ]; then
    /usr/bin/time -l "$@" 2>&1 >/dev/null | awk '/maximum resident/ { printf "%d MB", $1 / 1048576 }'
  else
    /usr/bin/time -v "$@" 2>&1 >/dev/null | awk -F: '/Maximum resident/ { printf "%d MB", $2 / 1024 }'
  fi
}
for b in parked parked_deep; do
  sh "$root/selfhost/llvm.sh" "$compiler" "$here/tasks/$b.fly" "$out/$b" > /dev/null
  echo "$b: Flyscript $(peak "$out/$b"), Rust $(peak "$out/rust/release/$b")"
  "$out/$b"
  "$out/rust/release/$b"
done
