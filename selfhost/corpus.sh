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
  # Its header describes the simulated world it runs against, as for `flyc run`'s tests.
  world=$(node -e '
    const w = { incoming: [], profiles: {}, quotas: {}, faults: 0, seed: 0x5eed };
    for (const line of require("fs").readFileSync(process.argv[1], "utf8").split("\n")) {
      if (!line.startsWith("//")) break;
      const m = /^\/\/\s*(\w+):\s?(.*)$/.exec(line);
      if (!m) continue;
      const [, key, value] = m, [k, v] = value.split("=");
      if (key === "request") w.incoming.push(value.replace(/\\n/g, "\n"));
      if (key === "profile") w.profiles[k] = v;
      if (key === "quota") w.quotas[k] = v === "true";
      if (key === "faults") w.faults = Number(value);
      if (key === "seed") w.seed = Number(value);
    }
    console.log(JSON.stringify(w));' "$f")
  [ -s "$out/$name.err" ] || (cd "$out/$name.cwd" && FLY_WORLD="$world" node "$out/$name.js") > "$out/$name.got" 2>&1
  if [ ! -s "$out/$name.err" ] && cmp -s "$out/$name.want" "$out/$name.got"; then
    pass=$((pass + 1))
  else
    echo "FAIL $name"
  fi
done
echo "$pass/$total pass"
