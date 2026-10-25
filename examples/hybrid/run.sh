#!/bin/sh
# Serves the hybrid site as build.sh made it: the Next.js app on `port + 1`, and in front of it the
# FlyNext app on `port`, which answers its own routes and forwards the rest. `run.sh [port] [out]`.
set -e
here=$(cd "$(dirname "$0")" && pwd)
port=${1:-3000}
out=${2:-$here/app/.flynext/build}
(cd "$here/next" && exec node node_modules/next/dist/bin/next start -H 127.0.0.1 -p $((port + 1))) &
next=$!
trap 'kill $next 2>/dev/null' EXIT INT TERM
"$out/server" "$port" "$out" --upstream=http://127.0.0.1:$((port + 1))
