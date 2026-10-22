#!/bin/sh
# Builds the site: the server, natively, and the program of each page in `client/` as WebAssembly,
# with what runs it in the browser and the site's files. `examples/todo/build.sh [compiler.js]
# [out]`, by default into `build/`; then `build/server [port] build` serves it. Needs what
# selfhost/wasm.sh needs, and a C compiler.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
compiler=${1:-$root/selfhost/seed.js}
out=${2:-$here/build}
mkdir -p "$out/_fly"
node --stack-size=65500 "$compiler" "$here/server.fly" "$out/server.c" "$root"
cc -std=gnu11 -O2 -w -o "$out/server" "$out/server.c" -lm
rm -f "$out/server.c"
# Each page is its own program.
for page in "$here"/client/*.fly; do
  sh "$root/selfhost/wasm.sh" "$compiler" "$page" "$out/_fly/$(basename "$page" .fly).wasm" --imports
done
cp "$root/web/flynext.js" "$out/_fly/"
cp "$here"/public/* "$out/"
