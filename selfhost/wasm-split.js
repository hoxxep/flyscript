// Splits a page program's linked LLVM module into a core and a module for each route, so that a page
// downloads its own code and the core: `node selfhost/wasm-split.js in.ll out-dir pattern`, with
// `pattern` a regular expression whose first group numbers a route's function (`flyRoute(\d+)_`).
//
// What a route's function reaches and nothing else does — its page's views, updates, models and
// their code — goes into the route's module; everything else, what two routes share among it, stays
// in the core. In the core each route's function becomes a stub of the same type that asks the host
// for the route's module (`fly.route(k)`), which loads it the first time, and calls the function
// there through the function table the two share: a call from WebAssembly to WebAssembly, so the
// program suspends through it as through any call. The program is the same; only where its code is changes.
//
// The module is expected internalized around its true roots, the routes' functions among them, and
// optimized, those kept from being inlined. Writes `all.ll`, the module with every symbol named
// across modules external; for `llvm-extract`, `route<k>.args`, each route's symbols, and
// `core.args`, every symbol that is not the core's; `stubs.ll`, the core's stubs; `exports.txt`,
// what the routes take of the core's own, `undefined.txt`, what they take of the C library's or the
// host's, and `routes.txt`, the routes' numbers (selfhost/wasm.sh).

const fs = require("fs");
const path = require("path");

const [input, outDir, pattern] = process.argv.slice(2);
const routeRe = new RegExp(`^${pattern}`);
const text = fs.readFileSync(input, "utf8");
const lines = text.split("\n");

const NAME = /@("(?:[^"\\]|\\.)*"|[-a-zA-Z$._][-a-zA-Z$._0-9]*)/g;
const nameAt = (line) => {
  const m = /@("(?:[^"\\]|\\.)*"|[-a-zA-Z$._][-a-zA-Z$._0-9]*)/.exec(line);
  return m ? m[1] : null;
};

// The module's entities: functions defined, with their lines, and globals, with theirs.
const defs = new Map(); // name -> { kind, start, end, refs }
const order = [];
const header = []; // everything that is neither a definition nor a declaration of a symbol
const declares = new Map(); // name -> line
for (let i = 0; i < lines.length; i++) {
  const line = lines[i];
  if (line.startsWith("define ")) {
    const name = nameAt(line.slice(line.indexOf("@")));
    let j = i;
    while (lines[j] !== "}") j++;
    defs.set(name, { kind: "fn", start: i, end: j });
    order.push(name);
    i = j;
  } else if (line.startsWith("declare ")) {
    declares.set(nameAt(line), line);
  } else if (/^@/.test(line)) {
    const name = nameAt(line);
    defs.set(name, { kind: "data", start: i, end: i });
    order.push(name);
  } else {
    header.push(line);
  }
}
const refsOf = (name) => {
  const out = new Set();
  const d = defs.get(name);
  const src = d.kind === "fn" ? lines.slice(d.start + 1, d.end).join("\n") : lines[d.start].slice(lines[d.start].indexOf("=") + 1);
  for (const m of src.matchAll(NAME)) if (m[1] !== name && (defs.has(m[1]) || declares.has(m[1]))) out.add(m[1]);
  return out;
};
const refs = new Map(order.map((n) => [n, refsOf(n)]));
const routeOf = new Map();
for (const n of order) {
  const m = routeRe.exec(n.replace(/^"|"$/g, ""));
  if (m && defs.get(n).kind === "fn") routeOf.set(n, Number(m[1]));
}

// What each root reaches.
const reach = (roots) => {
  const seen = new Set(roots);
  const stack = [...roots];
  while (stack.length) {
    const n = stack.pop();
    for (const r of refs.get(n) ?? []) {
      if (!defs.has(r) || seen.has(r) || routeOf.has(r)) continue;
      seen.add(r);
      stack.push(r);
    }
  }
  return seen;
};
const coreRoots = order.filter((n) => !routeOf.has(n) && !/^(define|@)[^\n]*\b(internal|private)\b/.test(lines[defs.get(n).start]));
const core = reach(coreRoots);
const owner = new Map(); // name -> route, for what one route alone reaches
const shared = new Set();
for (const [n, k] of routeOf) {
  for (const x of reach([n])) {
    if (core.has(x)) continue;
    if (owner.has(x) && owner.get(x) !== k) shared.add(x);
    else owner.set(x, k);
  }
}
for (const x of shared) owner.delete(x);

// A symbol named across modules is external, not internal: each module's linker finds the other's.
// Of default visibility, so that a route reaches what is the core's through the table of offsets
// the loader fills in, not at an address its compiler assumed.
const external = (line) => line
  .replace(/^define (internal|private) /, "define ")
  .replace(/^(@\S+ = )(internal|private) /, "$1");
fs.mkdirSync(outDir, { recursive: true });
const bare = (n) => n.replace(/^"|"$/g, "");
// The whole module, every symbol named across modules hidden rather than internal, for `llvm-extract`
// to take each module's part of, metadata and all.
fs.writeFileSync(path.join(outDir, "all.ll"), lines.map(external).join("\n"));
const routes = [...new Set(routeOf.values())].sort((a, b) => a - b);
const exported = new Set();
const moved = [];
for (const k of routes) {
  const names = order.filter((n) => owner.get(n) === k || routeOf.get(n) === k);
  const mine = new Set(names);
  for (const n of names) for (const r of refs.get(n)) if (!mine.has(r)) exported.add(r);
  const args = names.map((n) => `--${defs.get(n).kind === "fn" ? "func" : "glob"}=${bare(n)}`);
  fs.writeFileSync(path.join(outDir, `route${k}.args`), args.join("\n") + "\n");
  for (const n of names) if (!routeOf.has(n)) moved.push(`--${defs.get(n).kind === "fn" ? "func" : "glob"}=${bare(n)}`);
}
// The core: all the rest, the routes' functions declared, and defined by stubs linked in.
for (const n of routeOf.keys()) moved.push(`--func=${bare(n)}`);
fs.writeFileSync(path.join(outDir, "core.args"), moved.join("\n") + "\n");
const stubs = [header.filter((h) => h.startsWith("target ")).join("\n")];
for (const [n, k] of routeOf) {
  const line = lines[defs.get(n).start];
  const open = line.indexOf("(", line.indexOf("@"));
  let depth = 0, close = open;
  for (; close < line.length; close++) {
    if (line[close] === "(") depth++;
    else if (line[close] === ")" && --depth === 0) break;
  }
  const params = splitParams(line.slice(open + 1, close)).map((p) => {
    const toks = p.trim().split(/\s+/);
    return [toks[0], toks[toks.length - 1]];
  });
  const ret = /^define (?:\S+ )*?(\S+) @/.exec(line.replace(/ (noalias|noundef|zeroext|signext)\b/g, "").replace(/ range\([^)]*\)/g, ""))[1];
  const decl = params.map(([t, v]) => `${t} ${v}`).join(", ");
  const call = `call ${ret} %f(${decl})`;
  stubs.push(`define ${ret} @${n}(${decl}) {\n  %f = call ptr @fly_route_load(i32 ${k})\n  ${ret === "void" ? call : `%v = ${call}`}\n  ret ${ret === "void" ? "void" : `${ret} %v`}\n}`);
}
stubs.push(`declare ptr @fly_route_load(i32) #0\nattributes #0 = { "wasm-import-module"="fly" "wasm-import-name"="route" }`);
fs.writeFileSync(path.join(outDir, "stubs.ll"), stubs.join("\n") + "\n");
fs.writeFileSync(path.join(outDir, "exports.txt"), [...exported].filter((n) => defs.has(n) && !routeOf.has(n)).map(bare).join("\n") + "\n");
fs.writeFileSync(path.join(outDir, "undefined.txt"), [...exported].filter((n) => !defs.has(n) && !n.startsWith("llvm.")).map(bare).join("\n") + "\n");
fs.writeFileSync(path.join(outDir, "routes.txt"), routes.join("\n") + "\n");

function splitParams(s) {
  const out = [];
  let depth = 0, start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if ("[{<(".includes(c)) depth++;
    else if ("]}>)".includes(c)) depth--;
    else if (c === "," && depth === 0) { out.push(s.slice(start, i)); start = i + 1; }
  }
  if (s.trim()) out.push(s.slice(start));
  return out;
}
