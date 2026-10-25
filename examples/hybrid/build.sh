#!/bin/sh
# Builds the hybrid site: the FlyNext app (app/), with what the Next.js app uses of it — `api.ts`
# and `FlyIsland.tsx`, which its build writes into next/fly — and the React components its pages
# show (widgets/); then the Next.js app (next/). `build.sh [out]`, the FlyNext build going to `out`.
# Needs what web/flynext needs, and the Next.js app's packages installed (`pnpm install` in next/).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=${FLY_ROOT:-$(cd "$here/../.." && pwd)}
out=${1:-$here/app/.flynext/build}
modules=$here/next/node_modules
sh "$root/web/flynext" build "$here/app" "$out"
mkdir -p "$here/next/fly"
cp "$here/app/.flynext/next/api.ts" "$here/app/.flynext/next/FlyIsland.tsx" "$here/next/fly/"
NODE_PATH="$modules" "$modules/.bin/esbuild" "$here/widgets/widgets.tsx" --bundle --format=esm --jsx=automatic --minify --log-level=warning \
  --external:/_fly/flynext.js --define:process.env.NODE_ENV='"production"' --outfile="$out/widgets.js"
(cd "$here/next" && node "$modules/next/dist/bin/next" build)
