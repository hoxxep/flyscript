#!/bin/sh
# The todo app as FlyNext builds it (examples/todo), against the same app in Next.js and React
# (bench/next): pages rendered per request and a JSON call, under load from oha; each server's
# memory after it; and, with Playwright (NODE_PATH), what a page downloads, how soon it is
# interactive, and how fast a link is followed. `bench/web.sh`; results in target/bench/web.md.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
out="$root/target/bench"
mkdir -p "$out"
secs=${SECS:-10}
conns=${CONNS:-64}

# FlyNext.
sh "$root/web/flynext" build "$root/examples/todo/app" "$out/todo" > /dev/null
# Next.js, in production.
next="$out/next"
mkdir -p "$next"
cp -R "$here/next/." "$next/"
if [ ! -d "$next/node_modules/next" ]; then (cd "$next" && npm install --no-audit --no-fund > /dev/null 2>&1); fi
(cd "$next" && npx next build > /dev/null 2>&1)

wait_for() { for _ in $(seq 1 100); do curl -s -o /dev/null "$1" && return 0; sleep 0.1; done; echo "nothing answers $1" >&2; return 1; }

# `load name url [method body]`: requests a second, and the median and 99th percentile latency.
load() {
  if [ -n "$3" ]; then
    oha -z "${secs}s" -c "$conns" --no-tui --output-format json -m "$3" -d "$4" -H "Content-Type: application/json" "$2" > "$out/$1.json" 2> /dev/null
  else
    oha -z "${secs}s" -c "$conns" --no-tui --output-format json "$2" > "$out/$1.json" 2> /dev/null
  fi
  node -e '
    const d = require(process.argv[1]);
    const ok = d.statusCodeDistribution?.["200"] ?? 0;
    console.log(`${Math.round(d.summary.requestsPerSec)} req/s, p50 ${(d.latencyPercentiles.p50 * 1000).toFixed(2)} ms, p99 ${(d.latencyPercentiles.p99 * 1000).toFixed(2)} ms (${ok} OK)`);
  ' "$out/$1.json"
}

rss() { echo "$(( $(ps -o rss= -p "$1") / 1024 )) MB"; }

results="$out/web.md"
: > "$results"
run() {
  name=$1; base=$2; pid=$3; call_method=$4; call_url=$5; call_body=$6
  wait_for "$base/"
  page=$(load "$name-page" "$base/")
  item=$(load "$name-item" "$base/todos/2")
  call=$(load "$name-call" "$base$call_url" "$call_method" "$call_body")
  mem=$(rss "$pid")
  printf '| %s | %s | %s | %s | %s |\n' "$name" "$page" "$item" "$call" "$mem" >> "$results"
}

printf '| Server | Page `/` | Page `/todos/2` | Call (JSON) | Memory after |\n| :--- | :--- | :--- | :--- | :--- |\n' >> "$results"

# FlyNext on one core, then on every core.
FLY_THREADS=1 "$out/todo/server" 4101 "$out/todo" > /dev/null &
pid=$!
run "FlyNext, 1 core" http://127.0.0.1:4101 "$pid" POST /_fly/rpc/Todos.list '{}'
kill "$pid"; wait "$pid" 2> /dev/null || true

"$out/todo/server" 4102 "$out/todo" > /dev/null &
pid=$!
run "FlyNext, every core" http://127.0.0.1:4102 "$pid" POST /_fly/rpc/Todos.list '{}'
fly=$pid

(cd "$next" && exec npx next start -p 4103 > /dev/null 2>&1) &
npid=$!
sleep 1
wait_for http://127.0.0.1:4103/
nodepid=$(lsof -ti tcp:4103 -sTCP:LISTEN | head -1)
run "Next.js" http://127.0.0.1:4103 "$nodepid" GET /api/todos ''

# In a browser.
if [ -n "$NODE_PATH" ]; then
  node "$here/web.js" "FlyNext=http://127.0.0.1:4102/" "Next.js=http://127.0.0.1:4103/" > "$out/browser.json"
  printf '\n| Site | Scripts | Downloaded | Gzipped | Interactive after | Link followed in |\n| :--- | ---: | ---: | ---: | ---: | ---: |\n' >> "$results"
  node -e '
    const r = require(process.argv[1]);
    for (const [k, v] of Object.entries(r)) console.log(`| ${k} | ${v.scripts} | ${(v.bytes / 1024).toFixed(0)} KB | ${(v.gzipped / 1024).toFixed(0)} KB | ${v.interactiveMs.toFixed(0)} ms | ${v.linkMs.toFixed(0)} ms |`);
  ' "$out/browser.json" >> "$results"
fi

kill "$fly" 2> /dev/null || true
kill "$nodepid" "$npid" 2> /dev/null || true
cat "$results"
