// fannkuch-redux: permutations of small arrays, flipped; integer work over arrays.
const n = +(process.argv[2] ?? 7);
const perm = new Int32Array(16), perm1 = new Int32Array(16), count = new Int32Array(16);
let maxFlips = 0, checksum = 0, r = n, permCount = 0;
for (let i = 0; i < n; i++) perm1[i] = i;
outer: for (;;) {
  while (r !== 1) { count[r - 1] = r; r--; }
  perm.set(perm1);
  let flips = 0, k;
  while ((k = perm[0]) !== 0) {
    for (let i = 0, j = k; i < j; i++, j--) { const t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    flips++;
  }
  if (flips > maxFlips) maxFlips = flips;
  checksum += permCount % 2 === 0 ? flips : -flips;
  for (;;) {
    if (r === n) { console.log(`${checksum}\nPfannkuchen(${n}) = ${maxFlips}`); break outer; }
    const p0 = perm1[0];
    for (let i = 0; i < r; i++) perm1[i] = perm1[i + 1];
    perm1[r] = p0;
    if (--count[r] > 0) break;
    r++;
  }
  permCount++;
}
