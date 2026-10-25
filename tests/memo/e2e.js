const { chromium } = require("playwright");
// Drives tests/memo's page: `node e2e.js port`, with Playwright where `require` finds it (NODE_PATH).
// After each change the list is what a model of it says, every row kept is the node it was, and a
// click on any row says which row it is.
const port = process.argv[2];
const check = (ok, what) => { if (!ok) throw new Error(`FAILED: ${what}`); console.log(`ok - ${what}`); };
(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  const errors = [];
  page.on("pageerror", (e) => errors.push(e.message));
  page.on("console", (m) => { if (m.type() === "error" && !m.text().startsWith("Failed to load resource")) errors.push(m.text()); });
  page.on("response", (r) => { if (r.status() >= 400 && !r.url().endsWith("/favicon.ico")) errors.push(`${r.status()}: ${r.url()}`); });
  await page.goto(`http://127.0.0.1:${port}/`);
  await page.waitForFunction(() => document.querySelector("#prepend")?.__fly?.click !== undefined, null, { timeout: 10000 });
  check(await page.evaluate(() => globalThis.flyRebuilt === undefined), "the page takes over the server's rows, memos and all");
  let model = [0, 1, 2, 3, 4].map((id) => ({ id, n: 0 }));
  let next = 5;
  const shown = () => page.$$eval("li", (els) => els.map((li) => li.textContent));
  const expected = () => model.map((it) => `item ${it.id}${it.n}`);
  // Each row's node, marked, to tell a row kept from one made again.
  const mark = () => page.evaluate(() => { for (const li of document.querySelectorAll("li")) li.__mark = li.textContent; });
  const marked = () => page.$$eval("li", (els) => els.map((li) => li.__mark === undefined ? null : li.__mark));
  const step = async (button, change, kept) => {
    await mark();
    const before = model.map((it) => `item ${it.id}${it.n}`);
    change();
    await page.click(button);
    await page.waitForFunction((want) => JSON.stringify([...document.querySelectorAll("li")].map((li) => li.textContent)) === want, JSON.stringify(expected()), { timeout: 5000 });
    // A row whose data is what it was is the same node as before.
    const marks = await marked();
    const now = expected();
    const stayed = now.every((t, i) => !before.includes(t) || !kept || marks[i] === t);
    check(stayed, `${button}: the list is as it should be, ${kept ? "each row kept the node it had" : "rows made anew as need be"}`);
    // A click on each of the first, middle and last rows says which it is.
    for (const i of [0, Math.floor(model.length / 2), model.length - 1]) {
      if (i < 0 || i >= model.length) continue;
      await page.click(`li:nth-child(${i + 1})`);
      await page.waitForFunction((want) => document.querySelector("#clicked").textContent === want, `item ${model[i].id}`, { timeout: 5000 });
    }
    check(true, `${button}: a click on a row gives that row's message`);
  };
  await step("#prepend", () => { model.unshift({ id: next++, n: 0 }); }, true);
  await step("#append", () => { model.push({ id: next++, n: 0 }); }, true);
  await step("#remove", () => { model.splice(1, 1); }, true);
  await step("#reverse", () => { model.reverse(); }, true);
  await step("#swap", () => { const t = model[0]; model[0] = model[model.length - 1]; model[model.length - 1] = t; }, true);
  await step("#bump", () => { model[Math.floor(model.length / 2)].n += 1; }, true);
  await step("#bump", () => { model[Math.floor(model.length / 2)].n += 1; }, true);
  for (let k = 0; k < 12; k++) await step("#prepend", () => { model.unshift({ id: next++, n: 0 }); }, true);
  await step("#reverse", () => { model.reverse(); }, true);
  await step("#remove", () => { model.splice(1, 1); }, true);
  await step("#clear", () => { model = []; }, false);
  await step("#append", () => { model.push({ id: next++, n: 0 }); }, false);
  check(errors.length === 0, `nothing went wrong in the page${errors.length ? `: ${errors.join("; ")}` : ""}`);
  await browser.close();
})().catch((e) => { console.error(e.message); process.exit(1); });
