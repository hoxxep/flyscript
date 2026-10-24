#!/bin/sh
# Compiles each program of the run corpus with a self-hosted compiler and checks what it prints
# against the program's `// expect:` lines: `selfhost/corpus.sh [--c | --wasm | --llvm] [--leaks]
# [--threads] compiler.js [program.fly...]`.
# With `--c` each program is compiled to C and built with `cc`, with the address and undefined
# behavior sanitizers, so a memory error fails the program. With `--leaks` too, a program that
# leaks fails: on Linux the address sanitizer checks for leaks itself; where it cannot, on macOS,
# a plain build, on the C library's allocator, is run under `leaks`. A program that panics exits at once, and is not checked.
# With `--wasm` each is compiled to WebAssembly for WASI, through LLVM, and run by
# `selfhost/wasm.js`. With
# `--llvm` each is compiled through LLVM by `selfhost/llvm.sh`, with the sanitizers as for `--c`.
# With `--threads` too, natively, each runs on worker threads, not against a simulated world,
# under the thread sanitizer. `FLY_SANITIZE`, if set, replaces the sanitizers' flags. Programs are
# checked on every core at once, `FLY_JOBS` at a time if it is set, and reported in the order given.
c=false
wasm=false
llvm=false
leaks=false
threads=false
while :; do
  case "$1" in
    --c) c=true ;;
    --wasm) wasm=true ;;
    --llvm) llvm=true ;;
    --leaks) leaks=true ;;
    --threads) threads=true ;;
    *) break ;;
  esac
  shift
done
command -v leaks > /dev/null 2>&1 || leaks=false
# On threads the sanitizer is the thread sanitizer, and the program runs against no simulated
# world, on four workers.
sanitize="-fsanitize=address,undefined -fno-sanitize-recover=all"
$threads && sanitize="-fsanitize=thread"
# `FLY_SANITIZE` replaces the sanitizers' flags; empty, programs run as built for use, on the
# runtime's own allocator.
sanitize=${FLY_SANITIZE-$sanitize}
compiler=$1; shift
root=$(cd "$(dirname "$0")/.." && pwd)
ccflags=$(sh "$root/selfhost/ccflags.sh")
# Run as `--one out file`, it checks one program, leaving `name.pass` or `name.fail` in `out`.
if [ "$1" = "--one" ]; then
f=$3; out=$2
name=$(basename "$f" .fly)
# `// env: NAME=value` lines are its environment.
envs=$(grep '^// env: ' "$f" | sed 's#^// env: ##' | tr '\n' ' ')
grep '^// expect: ' "$f" | sed 's#^// expect: ##' > "$out/$name.want"
# `// file: name=text` lines are files the program finds in its working directory.
mkdir -p "$out/$name.cwd"
grep '^// file: ' "$f" | sed 's#^// file: ##' | while IFS='=' read -r file text; do
  printf '%b' "$text" > "$out/$name.cwd/$file"
done
# A program may end in a panic, which it prints; what it prints is what is compared.
if $wasm; then
  sh "$root/selfhost/wasm.sh" "$compiler" "$f" "$out/$name.wasm" > "$out/$name.err" 2>&1
  run="node --no-warnings $root/selfhost/wasm.js $out/$name.wasm"
elif $llvm; then
  sh "$root/selfhost/llvm.sh" "$compiler" "$f" "$out/$name.exe" $sanitize > "$out/$name.err" 2>&1
  run="$out/$name.exe"
elif $c; then
  node --stack-size=65500 "$compiler" "$f" "$out/$name.c" "$root" > "$out/$name.err" 2>&1 &&
    cc -std=gnu11 -g -O1 -w $ccflags $sanitize -o "$out/$name.exe" "$out/$name.c" -lm >> "$out/$name.err" 2>&1
  run="$out/$name.exe"
else
  node --stack-size=65500 "$compiler" "$f" "$out/$name.js" "$root" > "$out/$name.err" 2>&1
  run="node $out/$name.js"
fi
# Its header describes the simulated world it runs against, as for `flyc run`'s tests.
world=$(node -e '
  const w = { incoming: [], peers: {}, profiles: {}, quotas: {}, faults: 0, seed: 0x5eed };
  for (const line of require("fs").readFileSync(process.argv[1], "utf8").split("\n")) {
    if (!line.startsWith("//")) break;
    const m = /^\/\/\s*(\w+):\s?(.*)$/.exec(line);
    if (!m) continue;
    const [, key, value] = m, [k, v] = value.split("=");
    if (key === "request") w.incoming.push(value.replace(/\\r/g, "\r").replace(/\\n/g, "\n"));
    if (key === "peer") { const at = value.indexOf("="); w.peers[value.slice(0, at)] = value.slice(at + 1).replace(/\\r/g, "\r").replace(/\\n/g, "\n"); }
    if (key === "profile") w.profiles[k] = v;
    if (key === "quota") w.quotas[k] = v === "true";
    if (key === "faults") w.faults = Number(value);
    if (key === "seed") w.seed = Number(value);
  }
  console.log(JSON.stringify(w));' "$f")
if $threads; then
  [ -s "$out/$name.err" ] || (cd "$out/$name.cwd" && FLY_THREADS=4 $run) > "$out/$name.got" 2>&1
else
  # shellcheck disable=SC2086
  [ -s "$out/$name.err" ] || (cd "$out/$name.cwd" && FLY_WORLD="$world" env $envs $run) > "$out/$name.got" 2>&1
fi
if $c && $leaks && [ ! -s "$out/$name.err" ] && ! grep -q '<panic' "$out/$name.want"; then
  cc -std=gnu11 -g -O1 -w $ccflags -DFLY_SYSTEM_MALLOC -o "$out/$name.plain" "$out/$name.c" -lm &&
    (cd "$out/$name.cwd" && FLY_WORLD="$world" env $envs leaks --atExit -- "$out/$name.plain" 2>&1) | grep -q ' 0 leaks for ' ||
    echo "leaks" >> "$out/$name.err"
fi
if [ ! -s "$out/$name.err" ] && cmp -s "$out/$name.want" "$out/$name.got"; then
  : > "$out/$name.pass"
else
  { echo "FAIL $name"
    [ -n "$VERBOSE" ] && { head -c 2000 "$out/$name.err"; diff "$out/$name.want" "$out/$name.got" | head -20; }
  } > "$out/$name.fail"
fi
exit 0
fi
out=$(mktemp -d)
[ $# -eq 0 ] && set -- "$root"/tests/run/*.fly
jobs=${FLY_JOBS:-$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)}
flags=""
$c && flags="$flags --c"
$wasm && flags="$flags --wasm"
$llvm && flags="$flags --llvm"
$leaks && flags="$flags --leaks"
$threads && flags="$flags --threads"
# A program needing what WASI does not have says so.
for f in "$@"; do
  if $wasm && grep -q '^// skip: wasm' "$f"; then continue; fi
  printf '%s\n' "$f"
done > "$out/programs"
# shellcheck disable=SC2086
tr '\n' '\0' < "$out/programs" | xargs -0 -P "$jobs" -n 1 sh "$0" $flags "$compiler" --one "$out"
pass=0; total=0
while IFS= read -r f; do
  total=$((total + 1))
  name=$(basename "$f" .fly)
  if [ -e "$out/$name.pass" ]; then pass=$((pass + 1)); else cat "$out/$name.fail" 2>/dev/null || echo "FAIL $name"; fi
done < "$out/programs"
echo "$pass/$total pass"
