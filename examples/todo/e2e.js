const { chromium } = require("playwright");
// Drives the site in a browser, as someone would: `node e2e.js port [screenshots-dir]`, with
// Playwright where `require` finds it (NODE_PATH). The server is fresh: its store as it starts.
const port = process.argv[2], shots = process.argv[3];
const base = `http://127.0.0.1:${port}`;
const shoot = async (page, name) => { if (shots) await page.screenshot({ path: `${shots}/${name}.png` }); };
const check = (ok, what) => { if (!ok) throw new Error(`FAILED: ${what}`); console.log(`ok - ${what}`); };
(async () => {
  const html = await (await fetch(`${base}/`)).text();
  check(html.includes('<a href="/todos/3" class="title">Render pages on the server'), "the server renders the list");
  check(html.includes('<script type="text/plain" id="fly-page">index\n/\n'), "the server embeds what the page starts from");
  const missing = await fetch(`${base}/todos/999`);
  check(missing.status === 404 && (await missing.text()).includes("Nothing here"), "an item that is not there is not found, with a page saying so");
  check((await fetch(`${base}/nowhere`)).status === 404, "an address no page answers is not found");

  const browser = await chromium.launch();
  const page = await browser.newPage({ viewport: { width: 900, height: 720 } });
  const logs = [];
  // A request that fails is an error, but the one for an item that is not there, on purpose.
  page.on("console", (m) => { if ((m.type() === "error" || m.type() === "warning") && !m.text().startsWith("Failed to load resource")) logs.push(`${m.type()}: ${m.text()}`); });
  page.on("response", (r) => { if (r.status() >= 400 && !r.url().endsWith("/todos/999")) logs.push(`${r.status()}: ${r.url()}`); });
  page.on("pageerror", (e) => logs.push(`pageerror: ${e.message}`));
  const ready = () => page.waitForFunction(() => document.querySelector("li .check")?.__fly?.click !== undefined, null, { timeout: 10000 });
  await page.goto(`${base}/`);
  await ready();
  check(await page.evaluate(() => globalThis.flyRebuilt === undefined), "the page takes over the server's DOM without rebuilding it");
  const titles = async () => page.$$eval("li .title", (els) => els.map((e) => e.textContent));
  check((await titles()).length === 3, "three things to do");
  await shoot(page, "list");

  // Changing the list asks the server, and shows the page as it is meanwhile.
  await page.route("**/_fly/rpc/Todos.add", async (route) => { await new Promise((r) => setTimeout(r, 500)); await route.continue(); });
  await page.fill("input", "Ship the web framework");
  await page.click("button[type=submit]");
  await page.waitForSelector("button[type=submit]:disabled", { timeout: 2000 });
  check((await page.textContent("button[type=submit]")) === "Adding…", "the page shows it is adding before the server answers");
  await page.waitForFunction(() => document.querySelectorAll("li").length === 4, null, { timeout: 5000 });
  await page.unroute("**/_fly/rpc/Todos.add");
  check((await titles())[3] === "Ship the web framework", "adding asks the server, and shows its answer");
  check(await page.inputValue("input") === "", "the draft is cleared");
  await page.click("button[type=submit]");
  await page.waitForSelector("p.error", { timeout: 5000 });
  check((await page.textContent("p.error")) === "Write something to do first.", "an empty title is refused, the failure raised on the page");
  await page.click("li:nth-child(3) .check");
  await page.waitForFunction(() => document.querySelector("li:nth-child(3)").classList.contains("done"), null, { timeout: 5000 });
  check(await page.$("p.error") === null, "toggling marks it done, and what went wrong is gone");
  check((await page.textContent("footer span")) === "1 left", "the footer counts what is left");

  // Following a link renders the next page in place: no new document, the layout's nodes kept.
  await page.evaluate(() => { globalThis.stillHere = true; globalThis.oldNav = document.querySelector("nav"); });
  await page.click("a[href='/todos/4']");
  await page.waitForFunction(() => location.pathname === "/todos/4" && document.querySelector("h1")?.textContent === "Ship the web framework", null, { timeout: 5000 });
  check(await page.evaluate(() => globalThis.stillHere === true), "a link is followed without loading a page");
  check(await page.evaluate(() => document.querySelector("nav") === globalThis.oldNav), "the layout around both pages is kept as it was");
  check((await page.title()) === "Ship the web framework", "the title is the page's");
  await shoot(page, "item");
  await page.fill("input", "Ship the web framework, completely");
  await page.click("button[type=submit]");
  await page.waitForFunction(() => document.querySelector("h1")?.textContent === "Ship the web framework, completely", null, { timeout: 5000 });
  check(true, "renaming asks the server, and shows the new name");
  await page.click("a.back");
  await page.waitForFunction(() => location.pathname === "/" && document.querySelectorAll("li").length === 4, null, { timeout: 5000 });
  check((await titles())[3] === "Ship the web framework, completely", "back on the list, it has the new name");

  // The history steps back and forward through pages the program renders.
  await page.goBack();
  await page.waitForFunction(() => location.pathname === "/todos/4" && document.querySelector("h1")?.textContent?.startsWith("Ship"), null, { timeout: 5000 });
  check(await page.evaluate(() => globalThis.stillHere === true), "stepping back renders the page before, without loading it");
  await page.goForward();
  await page.waitForFunction(() => location.pathname === "/" && document.querySelector("li") !== null, null, { timeout: 5000 });
  check(true, "and forward again");

  // A component keeps its own state in its page's model.
  await page.click("nav a[href='/about']");
  await page.waitForSelector("h1:text('About')", { timeout: 5000 });
  await page.click(".counter button:last-child");
  await page.click(".counter button:last-child");
  await page.click(".counter button:first-child");
  await page.waitForFunction(() => document.querySelector(".counter output")?.textContent === "1", null, { timeout: 5000 });
  check(true, "a component's messages are its page's: up, up, down is 1");
  check(await page.evaluate(() => document.querySelector("nav a.here")?.getAttribute("href") === "/about"), "the layout marks where the page is");
  await shoot(page, "about");

  // Removing an item goes back to the list, from a page the browser loaded whole.
  await page.goto(`${base}/todos/4`);
  await page.waitForFunction(() => document.querySelector(".actions button")?.__fly?.click !== undefined, null, { timeout: 10000 });
  check(await page.evaluate(() => globalThis.flyRebuilt === undefined), "a page loaded at its own address is taken over as the list was");
  await page.click(".actions button");
  await page.waitForFunction(() => location.pathname === "/" && document.querySelectorAll("li").length === 3, null, { timeout: 5000 });
  check(!(await titles()).some((t) => t.startsWith("Ship")), "removing it asks the server, and the page goes back to the list");

  // A link to nothing, followed, shows the page for nothing found.
  await page.evaluate(() => { const a = document.createElement("a"); a.href = "/todos/999"; a.id = "lost"; a.textContent = "lost"; document.querySelector("footer").append(a); });
  await page.click("#lost");
  await page.waitForSelector("h1:text('Nothing here')", { timeout: 5000 });
  check(await page.evaluate(() => document.querySelector("nav") !== null), "the page for nothing found is shown inside the layout");

  await page.reload();
  await ready().catch(() => {});
  await page.goto(`${base}/`);
  await ready();
  check((await titles()).length === 3, "the server kept the changes");
  await page.setViewportSize({ width: 390, height: 760 });
  await shoot(page, "phone");
  check(logs.length === 0, `no errors in the page${logs.length ? ":\n" + logs.join("\n") : ""}`);
  await browser.close();
})().catch((e) => { console.error(e.message); process.exit(1); });
