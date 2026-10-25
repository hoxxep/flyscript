const { chromium } = require("playwright");
// Drives the hybrid site in a browser: `node e2e.js port`, with Playwright where `require` finds it
// (NODE_PATH), against run.sh's servers, fresh. A Next.js page calls the FlyNext server through
// `api.ts` and shows one of its islands; a link leads to a FlyNext page, which shows a React
// component; and both apps read the session cookie the Next.js app sets.
const port = process.argv[2];
const base = `http://127.0.0.1:${port}`;
const check = (ok, what) => { if (!ok) throw new Error(`FAILED: ${what}`); console.log(`ok - ${what}`); };
(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  const logs = [];
  page.on("console", (m) => { if (m.type() === "error") logs.push(`error: ${m.text()}`); });
  page.on("pageerror", (e) => logs.push(`pageerror: ${e.message}`));
  page.on("response", (r) => { if (r.status() >= 400) logs.push(`${r.status()}: ${r.url()}`); });

  // Signing in is the Next.js app's: its route handler sets the session cookie, and its redirect,
  // which names its own address, is followed here.
  await page.goto(`${base}/login`);
  check(new URL(page.url()).origin === base && new URL(page.url()).pathname === "/", "the Next.js app signs in and sends the browser back through the FlyNext server");
  await page.waitForSelector("text=Notes, in Next.js");
  await page.waitForFunction(() => document.querySelector(".who")?.textContent === "Signed in as alice", null, { timeout: 10000 });
  check(true, "a Next.js page calls `Notes.whoami` through api.ts, and the FlyNext server reads the cookie the Next.js app set");
  await page.waitForFunction(() => document.querySelectorAll(".notes li").length === 1, null, { timeout: 10000 });
  await page.click("button.add");
  await page.waitForFunction(() => [...document.querySelectorAll(".notes li")].some((li) => li.textContent === "Written in Next.js"), null, { timeout: 10000 });
  check(true, "and adds a note through api.ts, the answer typed as `{ Ok: Note[] }`");
  await page.click("button.add-empty");
  await page.waitForFunction(() => document.querySelector(".error")?.textContent === "Write something first.", null, { timeout: 10000 });
  check(true, "a failure comes back as `{ Err: \"Empty\" }`");

  // The island: a FlyNext component, run in the Next.js page by its own program.
  await page.waitForFunction(() => document.querySelector(".counter output")?.textContent === "5", null, { timeout: 15000 });
  check(true, "a `<FlyIsland>` shows the FlyNext counter with the model the Next.js page gave it");
  await page.click(".counter button.up");
  await page.click(".counter button.up");
  await page.waitForFunction(() => document.querySelector(".counter output")?.textContent === "7", null, { timeout: 5000 });
  check(true, "the island runs its own update on its own events");
  await page.click(".counter button.save");
  await page.waitForFunction(() => document.querySelector(".counter .saved")?.textContent === "3 notes", null, { timeout: 5000 });
  check(true, "the island performs `Notes.add`, asked of the FlyNext server");

  // A link from the Next.js app to a FlyNext page: Next's router finds it is not its own, and the
  // browser loads it, rendered by the FlyNext server.
  await page.click("a.to-fly");
  await page.waitForFunction(() => location.pathname === "/fly" && document.querySelector("h1")?.textContent === "Notes, in Flyscript", null, { timeout: 10000 });
  check(true, "following a Next.js `<Link>` to a FlyNext route loads the FlyNext page");
  check((await page.textContent(".who")) === "Signed in as alice", "the FlyNext page's `load` reads the session cookie the Next.js app set");
  const notes = await page.$$eval(".notes li", (els) => els.map((e) => e.textContent));
  check(notes.includes("Written in Next.js") && notes.includes("The island counted to 7"), "and shows the notes both apps added");

  // A React component the FlyNext page shows, mounted by the page's program, whose emits are the
  // page's events.
  await page.waitForSelector(".stars button[data-star='3']", { timeout: 10000 });
  check(true, "the FlyNext page mounts a React component where its view puts it");
  await page.click(".stars button[data-star='3']");
  await page.waitForFunction(() => document.querySelector(".rating")?.textContent === "Rated 3 of 5", null, { timeout: 5000 });
  check(true, "what the component emits is a message to the page's update");
  await page.waitForFunction(() => document.querySelectorAll(".stars button").length === 5 && document.querySelector(".stars button[data-star='3']").textContent === "★", null, { timeout: 5000 });
  check(true, "and the component, given its new props, renders again, the program leaving its DOM as React made it");

  // Back to the Next.js app: a link to a route that is not the FlyNext app's is the browser's.
  await page.click("text=Back to the Next.js app");
  await page.waitForFunction(() => location.pathname === "/" && document.querySelector("h1")?.textContent === "Notes, in Next.js", null, { timeout: 10000 });
  check(true, "a link from a FlyNext page to a Next.js route loads the Next.js page");
  check(logs.length === 0, `nothing went wrong in the browser${logs.length ? `:\n${logs.join("\n")}` : ""}`);
  await browser.close();
})().catch((e) => { console.error(e.message); process.exit(1); });
