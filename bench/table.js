// The benchmarks' results as tables, from hyperfine's JSON in target/bench: the median time of each
// way of running each program, and the most memory it held. `node table.js benchmark=size ...`
const fs = require("fs"), path = require("path");
const dir = path.join(__dirname, "..", "target", "bench");
const ways = [["fly-c", "Flyscript (C)"], ["fly-llvm", "Flyscript (LLVM)"], ["fly-js", "Flyscript (JS)"], ["c", "C"], ["rust", "Rust"], ["go", "Go"], ["js", "JavaScript"]];
const rows = process.argv.slice(2).map((a) => a.split("="));
const head = `| Benchmark | ${ways.map((w) => w[1]).join(" | ")} |\n| :--- |${ways.map(() => " ---: |").join("")}`;
const cell = (results, name, f) => { const r = results.find((x) => x.name === name); return r ? f(r.summary) : "–"; };
let time = head, memory = head;
for (const [b, n] of rows) {
  const results = JSON.parse(fs.readFileSync(path.join(dir, `${b}.json`), "utf8")).results;
  time += `\n| ${b} (${n}) | ${ways.map(([k]) => cell(results, k, (s) => `${(s.time_wall_clock.median * 1000).toFixed(0)} ms`)).join(" | ")} |`;
  memory += `\n| ${b} (${n}) | ${ways.map(([k]) => cell(results, k, (s) => `${(s.memory_peak_resident.median / 1048576).toFixed(1)} MB`)).join(" | ")} |`;
}
console.log(`### Time (median of ${process.env.RUNS ?? 5})\n\n${time}\n\n### Peak memory\n\n${memory}`);
