// What a page costs a browser, for each site: what it downloads before it is interactive, how long
// after the navigation starts it can be used, and how long a link takes to show the next page.
// `node web.js name=url ...`, with Playwright where `require` finds it; prints JSON.
const { chromium } = require("playwright");
const zlib = require("zlib");

// Interactive once the list's first check mark answers clicks: FlyNext's program has given it a
// message, React has given it props.
const interactive = () => {
  const el = document.querySelector("li .check");
  if (!el) return false;
  return el.__fly?.click !== undefined || Object.keys(el).some((k) => k.startsWith("__reactProps"));
};

const median = (xs) => { const s = [...xs].sort((a, b) => a - b); return s[Math.floor(s.length / 2)]; };

(async () => {
  const browser = await chromium.launch();
  const out = {};
  for (const arg of process.argv.slice(2)) {
    const [name, base] = arg.split("=");
    const ready = [], nav = [];
    let bytes = 0, gzipped = 0, requests = 0;
    for (let i = 0; i < 11; i++) {
      // A fresh browser context each time: nothing cached.
      const context = await browser.newContext();
      const page = await context.newPage();
      const seen = [];
      if (i === 0) {
        page.on("response", async (r) => {
          const type = r.headers()["content-type"] ?? "";
          if (!/javascript|wasm/.test(type)) return;
          seen.push(r.body().then((b) => ({ raw: b.length, gz: zlib.gzipSync(b, { level: 9 }).length })).catch(() => ({ raw: 0, gz: 0 })));
        });
      }
      await page.goto(base, { waitUntil: "commit" });
      await page.waitForFunction(interactive, null, { timeout: 20000, polling: "raf" });
      const t = await page.evaluate(() => performance.now());
      if (i > 0) ready.push(t);
      if (i === 0) {
        for (const s of await Promise.all(seen)) { bytes += s.raw; gzipped += s.gz; requests++; }
      }
      // A link followed: from the click until the next page's heading is there.
      const start = await page.evaluate(() => performance.now());
      await page.click("a[href='/todos/2']");
      await page.waitForFunction(() => document.querySelector("h1")?.textContent === "Compile it to WebAssembly", null, { timeout: 20000, polling: "raf" });
      const end = await page.evaluate(() => performance.now());
      if (i > 0) nav.push(end - start);
      await context.close();
    }
    out[name] = { scripts: requests, bytes, gzipped, interactiveMs: median(ready), linkMs: median(nav) };
  }
  await browser.close();
  console.log(JSON.stringify(out));
})().catch((e) => { console.error(e); process.exit(1); });
