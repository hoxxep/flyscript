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
  # `// file: name=text` lines are files the program finds in its working directory.
  mkdir -p "$out/$name.cwd"
  grep '^// file: ' "$f" | sed 's#^// file: ##' | while IFS='=' read -r file text; do
    printf '%b' "$text" > "$out/$name.cwd/$file"
  done
  # A program may end in a panic, which it prints; what it prints is what is compared.
  node --stack-size=65500 "$compiler" "$f" "$out/$name.js" "$root" > "$out/$name.err" 2>&1
  [ -s "$out/$name.err" ] || (cd "$out/$name.cwd" && node "$out/$name.js") > "$out/$name.got" 2>&1
  if [ ! -s "$out/$name.err" ] && cmp -s "$out/$name.want" "$out/$name.got"; then
    pass=$((pass + 1))
  else
    echo "FAIL $name"
  fi
done
echo "$pass/$total pass"
