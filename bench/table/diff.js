const { chromium } = require("playwright");
// How long the page takes to show each change to its rows: `node diff.js port`, with Playwright
// where `require` finds it (NODE_PATH). Each change is a click, timed until the page shows it, as
// the DOM changes; the median of twenty-one of each, in milliseconds. On a thousand rows: a change to
// every tenth row's count, to one row's, the rows reversed, and a thousand made from nothing; on ten
// thousand, a change to one row's.
const port = process.argv[2];
(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  const open = async (path) => {
    await page.goto(`http://127.0.0.1:${port}${path}`);
    await page.waitForFunction(() => document.querySelector("#tick")?.__fly?.click !== undefined, null, { timeout: 20000 });
  };
  // A sample is `batch` changes one after the other, each clicked once the last shows, timed together
  // and divided, since a browser's clock is coarser than one change; `before` runs untimed before
  // each, what the change starts from, and then a sample is one change.
  const timed = async (button, done, before) => {
    const times = [];
    const batch = before ? 1 : 10;
    for (let i = 0; i < 21; i++) {
      if (before) {
        await page.click(before);
        await page.waitForFunction(() => document.querySelectorAll("tr").length === 0);
      }
      const ticks = Number(await page.textContent("#ticks"));
      times.push(await page.evaluate(([b, d, ticks, batch]) => new Promise((resolve) => {
        let k = 0;
        const shown = () => (new Function("ticks", d))(ticks + k);
        const start = performance.now();
        const seen = new MutationObserver(() => {
          if (!shown()) return;
          k += 1;
          if (k === batch) { seen.disconnect(); resolve((performance.now() - start) / batch); } else document.querySelector(b).click();
        });
        seen.observe(document.body, { subtree: true, childList: true, characterData: true });
        document.querySelector(b).click();
      }), [button, done, ticks, batch]));
    }
    times.sort((a, b) => a - b);
    return times[10].toFixed(3);
  };
  const ticked = "return document.querySelector('#ticks').textContent === String(ticks + 1)";
  await open("/");
  const tick = await timed("#tick", ticked);
  const one = await timed("#one", ticked);
  const reverse = await timed("#reverse", "const first = document.querySelector('tr td').textContent; if (first === window.__was) return false; window.__was = first; return true");
  const create = await timed("#create", "return document.querySelectorAll('tr').length === 1000 && document.querySelector('#ticks').textContent === String(ticks + 1)", "#clear");
  await open("/big");
  const big = await timed("#one", ticked);
  console.log(`1,000 rows: every tenth ${tick} ms, one ${one} ms, reversed ${reverse} ms, made ${create} ms; 10,000 rows: one ${big} ms`);
  await browser.close();
})().catch((e) => { console.error(e); process.exit(1); });
