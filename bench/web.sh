#!/bin/sh
# The todo app as FlyNext builds it (examples/todo), against the same app in Next.js and React
# (bench/next): pages rendered per request and a JSON call, under load from wrk; each server's
# memory after it; and, with Playwright (NODE_PATH), what a page downloads, how soon it is
# interactive, and how fast a link is followed. `bench/web.sh`; results in target/bench/web.md.
# The client runs on the machine the server does, with four threads of its own.
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
  script="$out/$1.lua"
  if [ -n "$3" ]; then
    printf 'wrk.method = "%s"\nwrk.body = %s\nwrk.headers["Content-Type"] = "application/json"\n' "$3" "'$4'" > "$script"
  else
    : > "$script"
  fi
  # Non-2xx answers are counted apart: a server failing fast must not look fast.
  cat >> "$script" <<'LUA'
done = function(summary, latency, requests)
  io.write(string.format("%d req/s, p50 %.2f ms, p99 %.2f ms (%d errors)\n", summary.requests / (summary.duration / 1e6),
    latency:percentile(50) / 1000, latency:percentile(99) / 1000, summary.errors.status + summary.errors.connect + summary.errors.read + summary.errors.write + summary.errors.timeout))
end
LUA
  wrk -t4 -c "$conns" -d "${secs}s" -s "$script" "$2" 2> /dev/null | tail -1
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

printf '| Server | Page `/` | Page `/todos/2` | JSON endpoint `/api/todos` | Memory after |\n| :--- | :--- | :--- | :--- | :--- |\n' >> "$results"

# FlyNext on one core, then on every core.
FLY_THREADS=1 "$out/todo/server" 4101 "$out/todo" > /dev/null &
pid=$!
run "FlyNext, 1 core" http://127.0.0.1:4101 "$pid" GET /api/todos ''
kill "$pid"; wait "$pid" 2> /dev/null || true

"$out/todo/server" 4102 "$out/todo" > /dev/null &
pid=$!
run "FlyNext, every core" http://127.0.0.1:4102 "$pid" GET /api/todos ''
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

kill "$fly" "$nodepid" "$npid" 2> /dev/null || true
wait 2> /dev/null || true
cat "$results"
