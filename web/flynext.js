// The page's side of a Flyscript program compiled to WebAssembly (web/dom.fly): it gives the program
// what WASI would, fibers by JavaScript promise integration, and the page — its nodes by number,
// its events, the server — through functions that may suspend the program until there is an
// answer. `start(url)` runs the program at `url` in the page's element `#app`. Following a link
// within the site, or stepping through the history, is an event too: the program asks the server
// for what the next page shows, and renders it, the module and its state kept.

const ENOSYS = 52;
const EBADF = 8;

export async function start(url, root = document.getElementById("app")) {
  if (!WebAssembly.Suspending || !WebAssembly.promising) {
    throw new Error("this browser has no WebAssembly promise integration (JSPI)");
  }
  const module = await WebAssembly.compile(await (await fetch(url)).arrayBuffer());
  let exports;
  const mem = () => new Uint8Array(exports.memory.buffer);
  const view = () => new DataView(exports.memory.buffer);
  const decoder = new TextDecoder();
  const encoder = new TextEncoder();
  const str = (ptr, len) => decoder.decode(mem().subarray(ptr, ptr + len));

  // ---- WASI, as far as a page can ----
  let stdout = "";
  const wasi = {
    fd_write(fd, iovs, n, written) {
      let total = 0;
      for (let i = 0; i < n; i++) {
        const p = view().getUint32(iovs + i * 8, true);
        const l = view().getUint32(iovs + i * 8 + 4, true);
        stdout += str(p, l);
        total += l;
      }
      let nl;
      while ((nl = stdout.indexOf("\n")) >= 0) {
        (fd === 2 ? console.error : console.log)(stdout.slice(0, nl));
        stdout = stdout.slice(nl + 1);
      }
      view().setUint32(written, total, true);
      return 0;
    },
    fd_close: () => 0,
    fd_seek: () => ENOSYS,
    fd_fdstat_get: (fd, out) => { view().setUint8(out, fd <= 2 ? 2 : 0); return fd <= 2 ? 0 : EBADF; },
    fd_prestat_get: () => EBADF,
    fd_prestat_dir_name: () => EBADF,
    environ_sizes_get: (n, size) => { view().setUint32(n, 0, true); view().setUint32(size, 0, true); return 0; },
    environ_get: () => 0,
    args_sizes_get: (n, size) => { view().setUint32(n, 0, true); view().setUint32(size, 0, true); return 0; },
    args_get: () => 0,
    clock_time_get: (id, precision, out) => {
      const ns = BigInt(Math.round((id === 0 ? Date.now() : performance.now()) * 1e6));
      view().setBigUint64(out, ns, true);
      return 0;
    },
    random_get: (ptr, len) => { crypto.getRandomValues(mem().subarray(ptr, ptr + len)); return 0; },
    proc_exit: (code) => { throw new Exit(code); },
  };
  const wasiImports = new Proxy(wasi, { get: (t, k) => t[k] ?? (() => ENOSYS) });

  // ---- fibers: each runs as a call of its own, on a stack of its own, switched by the host ----
  const waiting = new Map();
  const saved = new Map();
  let runFiber;
  const fly = {
    switch: new WebAssembly.Suspending(async (from, to) => {
      const sp = exports.__stack_pointer;
      saved.set(from, sp.value);
      const back = new Promise((resolve) => waiting.set(from, resolve));
      const resume = waiting.get(to);
      if (resume) {
        waiting.delete(to);
        resume();
      } else {
        sp.value = exports.fly_fiber_top(to);
        runFiber(to).catch(ended);
      }
      await back;
      sp.value = saved.get(from);
    }),
    free: (f) => { waiting.delete(f); saved.delete(f); },
  };

  // ---- the page ----
  const nodes = [null];
  const ids = new WeakMap();
  const idOf = (node) => {
    if (!node) return 0;
    let id = ids.get(node);
    if (id === undefined) {
      id = nodes.length;
      nodes.push(node);
      ids.set(node, id);
    }
    return id;
  };
  // What the program takes next: a string it is told the length of, then copies out.
  let pending = new Uint8Array(0);
  const keep = (s) => { pending = encoder.encode(s); return pending.length; };
  // Events, as they happen, for the program to wait for in turn.
  const events = [];
  let wake = null;
  const happened = (e) => {
    events.push(e);
    if (wake) { const w = wake; wake = null; w(); }
  };
  // A link within the site, followed by a plain click, is the program's to follow.
  const ours = (a) => a && a.href && a.origin === location.origin && !a.target && !a.hasAttribute("download");
  document.addEventListener("click", (ev) => {
    if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
    const a = ev.target.closest?.("a");
    if (!ours(a)) return;
    ev.preventDefault();
    happened(`\u0001\0${a.pathname}${a.search}\0${1}`);
  });
  addEventListener("popstate", () => happened(`\u0001\0${location.pathname}${location.search}\0${0}`));
  // What a page shows is asked for as soon as a link to it is pointed at, and taken once.
  const prefetched = new Map();
  const ask = (url) => fetch(url, { headers: { "X-Fly-Data": "1" } }).then((r) => r.text());
  const prefetch = (ev) => {
    const a = ev.target.closest?.("a");
    if (!ours(a)) return;
    const url = `${a.pathname}${a.search}`;
    if (!prefetched.has(url)) {
      prefetched.set(url, ask(url).catch(() => null));
      setTimeout(() => prefetched.delete(url), 10000);
    }
  };
  document.addEventListener("mouseover", prefetch);
  document.addEventListener("touchstart", prefetch, { passive: true });
  const listen = (node, type) => {
    node.__fly ??= {};
    // One listener for each kind of event, which looks up the message the last render gave it.
    if (node.__flyListens?.has(type)) return;
    (node.__flyListens ??= new Set()).add(type);
    node.addEventListener(type, (ev) => {
      const msg = node.__fly?.[type];
      if (msg === undefined) return;
      if (type === "submit" || (type === "keydown" && ev.key === "Enter")) ev.preventDefault();
      const t = ev.target;
      happened(`${msg}\0${t.value ?? ""}\0${ev.key ?? ""}\0${t.checked === true}`);
    });
  };
  const env = {
    fly_dom_root: () => idOf(root),
    fly_dom_child: (parent, i) => idOf(nodes[parent].childNodes[i]),
    fly_dom_children: (parent) => nodes[parent].childNodes.length,
    fly_dom_is: (node, tag, len) => (nodes[node]?.nodeName.toLowerCase() ?? "") === str(tag, len) ? 1 : 0,
    fly_dom_create: (tag, len) => idOf(document.createElement(str(tag, len))),
    fly_dom_text: (s, len) => idOf(document.createTextNode(str(s, len))),
    fly_dom_set_text: (node, s, len) => { nodes[node].data = str(s, len); },
    fly_dom_set_attr: (node, n, nl, v, vl) => {
      const el = nodes[node], name = str(n, nl), value = str(v, vl);
      el.setAttribute(name, value);
      // What an input shows is its property, which its attribute only starts.
      if (name === "value" && el.value !== value) el.value = value;
      if (name === "checked") el.checked = true;
    },
    fly_dom_remove_attr: (node, n, nl) => {
      const el = nodes[node], name = str(n, nl);
      el.removeAttribute(name);
      if (name === "checked") el.checked = false;
    },
    fly_dom_insert: (parent, node, before) => {
      const p = nodes[parent], n = nodes[node], b = before ? nodes[before] : null;
      if (n.parentNode !== p || n.nextSibling !== b) p.insertBefore(n, b);
    },
    fly_dom_remove: (node) => { nodes[node]?.remove(); },
    // A page whose server render was not what its program shows is made afresh: counted, for tests.
    fly_dom_clear: (parent) => { nodes[parent].replaceChildren(); globalThis.flyRebuilt = (globalThis.flyRebuilt ?? 0) + 1; },
    fly_dom_on: (node, e, len, msg) => {
      const el = nodes[node], type = str(e, len);
      listen(el, type);
      el.__fly[type] = msg;
    },
    fly_dom_off: (node) => { const el = nodes[node]; if (el.__fly) el.__fly = {}; },
    fly_wait_event: new WebAssembly.Suspending(async () => {
      while (events.length === 0) await new Promise((resolve) => { wake = resolve; });
      return keep(events.shift());
    }),
    fly_fetch: new WebAssembly.Suspending(async (u, ul, b, bl) => {
      const res = await fetch(str(u, ul), { method: "POST", body: str(b, bl), headers: { "Content-Type": "application/json" } });
      return keep(await res.text());
    }),
    fly_get: new WebAssembly.Suspending(async (u, ul) => {
      const url = str(u, ul);
      const early = prefetched.get(url);
      prefetched.delete(url);
      let text = early ? await early : null;
      if (text === null) {
        try { text = await ask(url); } catch (_) { location.href = url; await new Promise(() => {}); }
      }
      return keep(text);
    }),
    fly_arrived: (u, ul, t, tl, push) => {
      const url = str(u, ul);
      document.title = str(t, tl);
      if (push) { history.pushState(null, "", url); scrollTo(0, 0); }
      globalThis.flyArrivals = (globalThis.flyArrivals ?? 0) + 1;
    },
    fly_initial: () => keep(document.getElementById("fly-page")?.textContent ?? ""),
    fly_take: (out, len) => { mem().set(pending.subarray(0, len), out); },
  };

  const ended = (e) => { if (!(e instanceof Exit)) console.error(e); };
  const instance = await WebAssembly.instantiate(module, { wasi_snapshot_preview1: wasiImports, fly, env });
  exports = instance.exports;
  runFiber = WebAssembly.promising(exports.fly_fiber_run);
  // The program runs for as long as the page is open, waiting for its events.
  return WebAssembly.promising(exports._start)().catch(ended);
}

class Exit {
  constructor(code) { this.code = code; }
}
