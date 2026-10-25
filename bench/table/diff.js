const { chromium } = require("playwright");
// How long the page takes to show each change to its thousand rows: `node diff.js port`, with
// Playwright where `require` finds it (NODE_PATH). Each change is a click, timed until the page
// shows it; the median of thirty of each kind of change, in milliseconds.
const port = process.argv[2];
(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  await page.goto(`http://127.0.0.1:${port}/`);
  await page.waitForFunction(() => document.querySelector("#tick")?.__fly?.click !== undefined, null, { timeout: 10000 });
  const timed = async (button, done) => {
    const times = [];
    for (let i = 0; i < 30; i++) {
      // Timed until the change shows, as the DOM changes, not to the next frame.
      times.push(await page.evaluate(([b, d, i]) => new Promise((resolve) => {
        const shown = () => (new Function("i", d))(i);
        const start = performance.now();
        const seen = new MutationObserver(() => { if (shown()) { seen.disconnect(); resolve(performance.now() - start); } });
        seen.observe(document.body, { subtree: true, childList: true, characterData: true });
        document.querySelector(b).click();
      }), [button, done, i]));
    }
    times.sort((a, b) => a - b);
    return times[15].toFixed(2);
  };
  const tick = await timed("#tick", "return document.querySelector('#ticks').textContent === String(i + 1)");
  const reverse = await timed("#reverse", "return document.querySelector('tr td').textContent === (i % 2 === 0 ? 'row 999' : 'row 0')");
  console.log(`tick ${tick} ms, reverse ${reverse} ms`);
  await browser.close();
})().catch((e) => { console.error(e); process.exit(1); });
