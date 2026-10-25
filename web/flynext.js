// The page's side of a Flyscript program compiled to WebAssembly (web/dom.fly): it gives the program
// what WASI would, and the page — its nodes by number,
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
  // Each page's own code is a module of its own (selfhost/wasm-split.js), fetched as soon as the page
  // is known: this one's at once, beside the program's.
  const base = new URL(url, location.href);
  const modules = new Map();
  const moduleOf = (k) => {
    const file = typeof ROUTES === "undefined" ? null : ROUTES.modules[k]?.file;
    if (!file) return null;
    if (!modules.has(k)) modules.set(k, fetch(new URL(`routes/${file}`, base)).then((r) => r.arrayBuffer()).then((b) => WebAssembly.compile(b)));
    return modules.get(k);
  };
  const routeOf = (name) => (typeof ROUTES === "undefined" ? undefined : ROUTES.names[name]);
  // A page as the server describes it starts with the name of its route (web/dom.fly's `arrival`).
  const routeIn = (text) => routeOf(text.slice(0, (text.indexOf("\n") + 1 || text.length + 1) - 1));
  { const k = routeIn(document.getElementById("fly-page")?.textContent ?? ""); if (k !== undefined) moduleOf(k); }
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

  // ---- what the program asks of the host, which may suspend it, by promise integration ----
  const fly = {
    // A route's function, from its module, linked into the program the first time: its place in the
    // table of functions the two share, which the program calls it through.
    route: new WebAssembly.Suspending(async (k) => {
      if (!linked.has(k)) linked.set(k, link(k));
      return linked.get(k);
    }),
    // The runtime's cryptography (runtime.c's `crypto_op`) by the page's WebCrypto, which answers
    // later: the program waits for it, by promise integration.
    crypto: new WebAssembly.Suspending(async (op, a, na, b, nb, c, nc, d, nd, out, cap) => {
      const at = (p, n) => mem().slice(p, p + n);
      const [A, B, C, D] = [at(a, na), at(b, nb), at(c, nc), at(d, nd)];
      const give = (buf) => { const bytes = new Uint8Array(buf); mem().set(bytes.subarray(0, cap), out); return Math.min(bytes.length, cap); };
      const s = crypto.subtle;
      const hash = { 1: "SHA-256", 2: "SHA-384", 3: "SHA-512" }[op];
      if (hash) return give(await s.digest(hash, A));
      if (op === 4 || op === 5) {
        // A key of no bytes is, padded to the block, the key of one zero byte, which WebCrypto takes.
        const key = await s.importKey("raw", A.length ? A : new Uint8Array(1), { name: "HMAC", hash: op === 4 ? "SHA-256" : "SHA-512" }, false, ["sign"]);
        return give(await s.sign("HMAC", key, B));
      }
      if (op === 6) {
        if (cap === 0) return 0;
        const key = await s.importKey("raw", A, "HKDF", false, ["deriveBits"]);
        return give(await s.deriveBits({ name: "HKDF", hash: "SHA-256", salt: B, info: C }, key, cap * 8));
      }
      if (op === 7 || op === 8) {
        if (A.length !== 32 || B.length !== 12) return -2;
        const key = await s.importKey("raw", A, "AES-GCM", false, [op === 7 ? "encrypt" : "decrypt"]);
        const how = { name: "AES-GCM", iv: B, additionalData: D, tagLength: 128 };
        if (op === 7) return give(await s.encrypt(how, key, C));
        try { return give(await s.decrypt(how, key, C)); } catch { return -1; }
      }
      const pkcs8 = (k) => { const der = new Uint8Array(48); der.set([0x30, 0x2e, 2, 1, 0, 0x30, 5, 6, 3, 0x2b, 0x65, 0x70, 4, 0x22, 4, 0x20]); der.set(k, 16); return der; };
      if (op === 9 || op === 10) {
        if (A.length !== 32) return -2;
        const key = await s.importKey("pkcs8", pkcs8(A), "Ed25519", true, ["sign"]);
        if (op === 10) return give(await s.sign("Ed25519", key, B));
        const x = (await s.exportKey("jwk", key)).x.replaceAll("-", "+").replaceAll("_", "/");
        return give(Uint8Array.from(atob(x), (ch) => ch.charCodeAt(0)));
      }
      if (op === 11) {
        if (A.length !== 32 || C.length !== 64) return -1;
        try {
          const key = await s.importKey("raw", A, "Ed25519", false, ["verify"]);
          return (await s.verify("Ed25519", key, C, B)) ? 0 : -1;
        } catch { return -1; }
      }
      return -2;
    }),
  };

  // ---- routes: modules linked as WebAssembly's dynamic linking lays them out ----
  const linked = new Map();
  let slots = null;
  // A function's place in the table, given one if it has none.
  const slotOf = (f) => {
    const table = exports.__indirect_function_table;
    if (!slots) {
      slots = new Map();
      for (let i = 0; i < table.length; i++) { const g = table.get(i); if (g && !slots.has(g)) slots.set(g, i); }
    }
    let i = slots.get(f);
    if (i === undefined) { i = table.grow(1); table.set(i, f); slots.set(f, i); }
    return i;
  };
  // `dylink.0`'s first part: the memory and the table a module needs of its own.
  const needs = (mod) => {
    const sec = WebAssembly.Module.customSections(mod, "dylink.0")[0];
    const out = { memory: 0, memoryAlign: 0, table: 0, tableAlign: 0 };
    if (!sec) return out;
    const b = new Uint8Array(sec);
    let at = 0;
    const leb = () => { let v = 0, shift = 0, x; do { x = b[at++]; v |= (x & 0x7f) << shift; shift += 7; } while (x & 0x80); return v >>> 0; };
    while (at < b.length) {
      const type = b[at++], size = leb(), end = at + size;
      if (type === 1) { out.memory = leb(); out.memoryAlign = leb(); out.table = leb(); out.tableAlign = leb(); }
      at = end;
    }
    return out;
  };
  const link = async (k) => {
    const mod = await moduleOf(k);
    const need = needs(mod);
    const align = 2 ** need.memoryAlign;
    const raw = need.memory ? exports.calloc(need.memory + align, 1) : 0;
    const memoryBase = (raw + align - 1) & ~(align - 1);
    const table = exports.__indirect_function_table;
    const tableBase = table.length;
    if (need.table) table.grow(need.table);
    const got = (value) => new WebAssembly.Global({ value: "i32", mutable: true }, value);
    const imports = {
      env: {
        memory: exports.memory,
        __indirect_function_table: table,
        __stack_pointer: exports.__stack_pointer,
        __memory_base: new WebAssembly.Global({ value: "i32", mutable: false }, memoryBase),
        __table_base: new WebAssembly.Global({ value: "i32", mutable: false }, tableBase),
      },
      "GOT.mem": {},
      "GOT.func": {},
      fly,
      wasi_snapshot_preview1: wasiImports,
    };
    for (const i of WebAssembly.Module.imports(mod)) {
      if (i.module === "env" && i.kind === "function") imports.env[i.name] = exports[i.name] ?? env[i.name];
      else if (i.module === "env" && i.kind === "tag") imports.env[i.name] = exports[i.name];
      else if (i.module === "GOT.mem") imports["GOT.mem"][i.name] = got(exports[i.name].value);
      else if (i.module === "GOT.func") imports["GOT.func"][i.name] = got(slotOf(exports[i.name]));
    }
    const instance = await WebAssembly.instantiate(mod, imports);
    instance.exports.__wasm_apply_data_relocs?.();
    instance.exports.__wasm_call_ctors?.();
    return slotOf(instance.exports[ROUTES.modules[k].fn]);
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
  // The head's description of the page, as the server writes it (web/site.fly): what a search engine
  // or a link preview shows of it.
  const describe = (title, description) => {
    const meta = (key, value, content) => {
      let m = document.head.querySelector(`meta[${key}="${value}"]`);
      if (content === "") { m?.remove(); return; }
      if (!m) { m = document.createElement("meta"); m.setAttribute(key, value); document.head.append(m); }
      m.setAttribute("content", content);
    };
    meta("name", "description", description);
    meta("property", "og:description", description);
    meta("property", "og:title", title);
  };
  // What a page shows is asked for as soon as a link to it is pointed at, and taken once.
  const prefetched = new Map();
  const ask = (url) => fetch(url, { headers: { "X-Fly-Data": "1" } }).then((r) => r.text());
  const prefetch = (ev) => {
    const a = ev.target.closest?.("a");
    if (!ours(a)) return;
    const url = `${a.pathname}${a.search}`;
    if (!prefetched.has(url)) {
      // With the page's data, its module, so following the link waits for neither.
      const early = ask(url).then((text) => {
        const k = routeIn(text);
        if (k !== undefined) moduleOf(k);
        return text;
      });
      prefetched.set(url, early.catch(() => null));
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
    // A timer is an event of the element's: it stops once the element is gone.
    const timer = /^(every|after):(\d+)$/.exec(type);
    if (timer) {
      // A timer stops once its element is gone, or a render no longer gives it one.
      const fire = () => {
        const msg = node.__fly?.[type];
        if (!node.isConnected || msg === undefined) { clearInterval(id); node.__flyListens.delete(type); return; }
        happened(`${msg}\0\0\0false`);
      };
      const id = timer[1] === "every" ? setInterval(fire, +timer[2]) : setTimeout(fire, +timer[2]);
      return;
    }
    node.addEventListener(type, (ev) => {
      const msg = node.__fly?.[type];
      if (msg === undefined) return;
      // The program has the event: the browser does not post what posts it without the program.
      if (type === "submit" || (type === "keydown" && ev.key === "Enter") || node.hasAttribute("formaction")) ev.preventDefault();
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
    fly_arrived: (u, ul, t, tl, d, dl, push) => {
      const url = str(u, ul);
      // What happened on the page before is not the new page's: its messages are numbered anew.
      for (let i = events.length - 1; i >= 0; i--) if (!events[i].startsWith("\u0001")) events.splice(i, 1);
      const title = str(t, tl);
      document.title = title;
      describe(title, str(d, dl));
      if (push) { history.pushState(null, "", url); scrollTo(0, 0); }
      globalThis.flyArrivals = (globalThis.flyArrivals ?? 0) + 1;
    },
    fly_initial: () => keep(document.getElementById("fly-page")?.textContent ?? ""),
    fly_take: (out, len) => { mem().set(pending.subarray(0, len), out); },
  };

  const ended = (e) => { if (!(e instanceof Exit)) console.error(e); };
  const instance = await WebAssembly.instantiate(module, { wasi_snapshot_preview1: wasiImports, fly, env });
  exports = instance.exports;
  // The program runs for as long as the page is open, waiting for its events.
  return WebAssembly.promising(exports._start)().catch(ended);
}

class Exit {
  constructor(code) { this.code = code; }
}
