#!/bin/sh
# What the browser's side of FlyNext costs (bench/table): the table app built and served, and timed
# in a browser by Playwright, where FLY_NODE_PATH says its node_modules are. `bench/table.sh`.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
out="$root/target/bench/table"
sh "$root/web/flynext" build "$here/table/app" "$out" > /dev/null
"$out/server" 0 "$out" > "$out/port.txt" &
server=$!
trap 'kill $server' EXIT
while ! grep -q "listening" "$out/port.txt" 2>/dev/null; do sleep 0.1; done
NODE_PATH="${FLY_NODE_PATH:?set FLY_NODE_PATH to Playwright node_modules}" node "$here/table/diff.js" "$(grep -o '[0-9]*' "$out/port.txt")"
