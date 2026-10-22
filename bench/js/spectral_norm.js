// spectral-norm: the largest eigenvalue of an infinite matrix, by the power method; floating point
// loops over arrays.
const A = (i, j) => 1 / ((i + j) * (i + j + 1) / 2 + i + 1);
const mulAv = (v, av) => { for (let i = 0; i < av.length; i++) { let s = 0; for (let j = 0; j < v.length; j++) s += A(i, j) * v[j]; av[i] = s; } };
const mulAtv = (v, atv) => { for (let i = 0; i < atv.length; i++) { let s = 0; for (let j = 0; j < v.length; j++) s += A(j, i) * v[j]; atv[i] = s; } };
const n = +(process.argv[2] ?? 100);
const u = new Float64Array(n).fill(1), v = new Float64Array(n), tmp = new Float64Array(n);
for (let i = 0; i < 10; i++) { mulAv(u, tmp); mulAtv(tmp, v); mulAv(v, tmp); mulAtv(tmp, u); }
let vBv = 0, vv = 0;
for (let i = 0; i < n; i++) { vBv += u[i] * v[i]; vv += v[i] * v[i]; }
console.log(Math.sqrt(vBv / vv).toFixed(9));
