// Word frequencies: text built from a vocabulary, split into words, counted in a hash map, and
// the most frequent shown; strings, hashing and sorting.
const n = +(process.argv[2] ?? 1000);
const parts = [];
let seed = 42n;
const M = (1n << 64n) - 1n;
for (let i = 0; i < n; i++) {
  seed = (seed * 6364136223846793005n + 1442695040888963407n) & M;
  parts.push(`w${(seed >> 33n) % 20000n}`);
}
const text = parts.join(" ");
const counts = new Map();
for (const w of text.split(/\s+/)) if (w) counts.set(w, (counts.get(w) ?? 0) + 1);
console.log(`${counts.size} distinct words`);
const all = [...counts].sort((a, b) => b[1] - a[1] || (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
for (const [w, c] of all.slice(0, 10)) console.log(`${w} ${c}`);
