// n-body: a simulation of the Jovian planets; floating point arithmetic and square roots.
const PI = Math.PI, SOLAR_MASS = 4 * PI * PI, DAYS = 365.24;
const body = (x, y, z, vx, vy, vz, m) => ({ x, y, z, vx: vx * DAYS, vy: vy * DAYS, vz: vz * DAYS, m: m * SOLAR_MASS });
const b = [
  body(0, 0, 0, 0, 0, 0, 1),
  body(4.84143144246472090e+00, -1.16032004402742839e+00, -1.03622044471123109e-01, 1.66007664274403694e-03, 7.69901118419740425e-03, -6.90460016972063023e-05, 9.54791938424326609e-04),
  body(8.34336671824457987e+00, 4.12479856412430479e+00, -4.03523417114321381e-01, -2.76742510726862411e-03, 4.99852801234917238e-03, 2.30417297573763929e-05, 2.85885980666130812e-04),
  body(1.28943695621391310e+01, -1.51111514016986312e+01, -2.23307578892655734e-01, 2.96460137564761618e-03, 2.37847173959480950e-03, -2.96589568540237556e-05, 4.36624404335156298e-05),
  body(1.53796971148509165e+01, -2.59193146099879641e+01, 1.79258772950371181e-01, 2.68067772490389322e-03, 1.62824170038242295e-03, -9.51592254519715870e-05, 5.15138902046611451e-05),
];
const energy = () => {
  let e = 0;
  for (let i = 0; i < 5; i++) {
    e += 0.5 * b[i].m * (b[i].vx * b[i].vx + b[i].vy * b[i].vy + b[i].vz * b[i].vz);
    for (let j = i + 1; j < 5; j++) { const dx = b[i].x - b[j].x, dy = b[i].y - b[j].y, dz = b[i].z - b[j].z; e -= b[i].m * b[j].m / Math.sqrt(dx * dx + dy * dy + dz * dz); }
  }
  return e;
};
const n = +(process.argv[2] ?? 1000);
let px = 0, py = 0, pz = 0;
for (const p of b) { px += p.vx * p.m; py += p.vy * p.m; pz += p.vz * p.m; }
b[0].vx = -px / SOLAR_MASS; b[0].vy = -py / SOLAR_MASS; b[0].vz = -pz / SOLAR_MASS;
console.log(energy().toFixed(9));
for (let s = 0; s < n; s++) {
  for (let i = 0; i < 5; i++) for (let j = i + 1; j < 5; j++) {
    const bi = b[i], bj = b[j], dx = bi.x - bj.x, dy = bi.y - bj.y, dz = bi.z - bj.z;
    const d2 = dx * dx + dy * dy + dz * dz, mag = 0.01 / (d2 * Math.sqrt(d2));
    bi.vx -= dx * bj.m * mag; bi.vy -= dy * bj.m * mag; bi.vz -= dz * bj.m * mag;
    bj.vx += dx * bi.m * mag; bj.vy += dy * bi.m * mag; bj.vz += dz * bi.m * mag;
  }
  for (const p of b) { p.x += 0.01 * p.vx; p.y += 0.01 * p.vy; p.z += 0.01 * p.vz; }
}
console.log(energy().toFixed(9));
