// binary-trees, single-threaded: allocation and freeing of many small trees.
const make = (d) => d > 0 ? { l: make(d - 1), r: make(d - 1) } : { l: null, r: null };
const check = (n) => n.l ? 1 + check(n.l) + check(n.r) : 1;
const n = +(process.argv[2] ?? 10), max = Math.max(6, n);
console.log(`stretch tree of depth ${max + 1}\t check: ${check(make(max + 1))}`);
const long = make(max);
for (let d = 4; d <= max; d += 2) {
  const iters = 1 << (max - d + 4); let sum = 0;
  for (let i = 0; i < iters; i++) sum += check(make(d));
  console.log(`${iters}\t trees of depth ${d}\t check: ${sum}`);
}
console.log(`long lived tree of depth ${max}\t check: ${check(long)}`);
