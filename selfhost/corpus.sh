#!/bin/sh
# Compiles each program of the run corpus with a self-hosted compiler and checks what it prints
# against the program's `// expect:` lines: `selfhost/corpus.sh compiler.js [program.fly...]`.
compiler=$1; shift
root=$(cd "$(dirname "$0")/.." && pwd)
out=$(mktemp -d)
[ $# -eq 0 ] && set -- "$root"/tests/run/*.fly
pass=0; total=0
for f in "$@"; do
  total=$((total + 1))
  name=$(basename "$f" .fly)
  grep '^// expect: ' "$f" | sed 's#^// expect: ##' > "$out/$name.want"
  if node "$compiler" "$f" "$out/$name.js" "$root" > "$out/$name.err" 2>&1 \
    && [ ! -s "$out/$name.err" ] \
    && node "$out/$name.js" > "$out/$name.got" 2>&1 \
    && cmp -s "$out/$name.want" "$out/$name.got"; then
    pass=$((pass + 1))
  else
    echo "FAIL $name"
  fi
done
echo "$pass/$total pass"
