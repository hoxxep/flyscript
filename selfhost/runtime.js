"use strict";
// The runtime of Flyscript compiled to JavaScript: what compiled code calls that the standard
// library declares without a body (`$b`), and the operations code generation leaves to it (`$rt`).
//
// Values: integers are BigInts and floats numbers; a string holds one byte per character, so
// that lengths and offsets are the byte counts Flyscript defines; `void` is `undefined`. Structs
// and records are objects, tuples and lists arrays, a tag `{ $tag, $ }`. A value of type `mut T`
// is a reference: an object whose `v` reads and writes the place lent. A generator yields the
// operations it performs: `Yielded` for an item, `Op` for an effect of the program's own.
const { $rt, $b } = (() => {
  const fs = require("fs");

  class Fail {
    constructor(value) { this.value = value; }
  }
  class Panic extends Error {}
  function panic(message) { throw new Panic(message); }
  function raise(value) { throw new Fail(value); }

  // ---- references ----

  // A field or element of an object, lent `mut`.
  class FieldRef {
    constructor(o, k) { this.o = o; this.k = k; }
    get v() { return this.o[this.k]; }
    set v(x) { this.o[this.k] = x; }
  }
  // A range of a list lent `mut`: it reads as a copy and writes back.
  class RangeRef {
    constructor(a, lo, hi) { this.a = a; this.lo = lo; this.hi = hi; }
    get v() { return this.a.slice(this.lo, this.hi); }
    set v(x) { for (let i = 0; i < x.length; i++) this.a[this.lo + i] = x[i]; }
  }
  function indexRef(a, i) { return new FieldRef(a, at(a, i)); }
  // The list a reference to a list or a range of one reaches, and the range.
  function rangeOf(r) { return r instanceof RangeRef ? [r.a, r.lo, r.hi] : [r.v, 0, r.v.length]; }
  function rangeRef(a, lo, hi) {
    const l = Number(lo), h = hi === undefined ? a.length : Number(hi);
    if (l > h || h > a.length) panic(`range ${l}..${h} out of bounds (length ${a.length})`);
    return new RangeRef(a, l, h);
  }

  // ---- generators ----

  class Yielded {
    constructor(item) { this.item = item; }
  }
  class Op {
    constructor(effect, op, args) { this.effect = effect; this.op = op; this.args = args; }
  }
  const yielded = (item) => new Yielded(item);
  const isYield = (v) => v instanceof Yielded;
  const perform = (effect, op, args) => new Op(effect, op, args);

  // `return` inside a `handle`, leaving the function around it.
  class Return {
    constructor(v) { this.v = v; }
  }
  const YIELD = { name: "Yield" };

  // A `handle`: runs `body`, a generator, with `arms` handling `effect` (§5.2): deep, so a
  // continuation resumes the body with the handler still around it.
  function* handle(effect, body, arms) {
    return yield* resume(body(), undefined, effect, arms);
  }
  // Runs `g` from `v` until it ends, or performs an operation of `effect`, whose arm's value is
  // the result; any other operation is passed on, and its answer back.
  function* resume(g, v, effect, arms) {
    let r = g.next(v);
    for (;;) {
      if (r.done) return r.value;
      const op = r.value;
      const ours = effect === YIELD ? op instanceof Yielded : op instanceof Op && op.effect === effect;
      if (ours) {
        const name = effect === YIELD ? "yield" : op.op;
        const args = effect === YIELD ? [op.item] : op.args;
        const arm = arms[name];
        if (arm.length <= args.length) {
          // An arm that does not resume: the body is done, its cleanup run first (§5.2).
          if (g.return) g.return();
          return yield* arm(...args);
        }
        let resumed = false;
        const k = function* (x) {
          if (resumed) panic("a continuation resumed twice");
          resumed = true;
          return yield* resume(g, x, effect, arms);
        };
        return yield* arm(...args, k);
      }
      r = g.next(yield op);
    }
  }
  // ---- destructors: what was moved out of an owner, by field path ----

  function moved(m, path) { const out = m === null ? new Set() : new Set(m); out.add(path); return out; }
  const under = (path, p) => p === path || p.startsWith(path + ".");
  function isMoved(m, path) {
    if (m === null) return false;
    for (const p of m) if (under(p, path)) return true;
    return false;
  }
  // The paths moved out below field `f`, relative to it.
  function sub(m, f) {
    if (m === null) return null;
    let out = null;
    for (const p of m) if (p.startsWith(f + ".")) { if (out === null) out = new Set(); out.add(p.slice(f.length + 1)); }
    return out;
  }
  // A place assigned anew owns all of it again.
  function unmove(m, path) {
    if (m === null) return null;
    const out = new Set([...m].filter((p) => !under(path, p)));
    return out.size === 0 ? null : out;
  }
  // Runs a destructor that may perform `Io` to its end, without letting other tasks in.
  function drive(g) {
    for (let r = g.next(); !r.done; r = g.next()) if (!(r.value instanceof Point)) panic("a destructor performed an effect that nothing handles");
  }

  // Runs a generator where nothing can handle what it performs.
  function run(g) {
    const r = g.next();
    if (!r.done) panic("an effect performed that nothing handles");
    return r.value;
  }

  // `Gen<T, E>`: an iterator of what a generator yields.
  class Gen {
    constructor(it) { this.it = it; }
  }
  // A list's items, stepped as a generator yielding them would be, with one step object reused:
  // whoever steps it reads the item before stepping again.
  class ListOps {
    constructor(items) { this.items = items; this.i = 0; this.y = new Yielded(undefined); this.step = { done: false, value: this.y }; }
    next() {
      if (this.i >= this.items.length) return { done: true, value: undefined };
      this.y.item = this.items[this.i++];
      return this.step;
    }
    return() { this.i = this.items.length; return { done: true, value: undefined }; }
    [Symbol.iterator]() { return this; }
  }
  const genOf = (items) => new Gen(new ListOps(items));
  // The next item of a generator, or `undefined` once it is done.
  function step(g) {
    const r = g.it.next();
    if (r.done) return undefined;
    if (!(r.value instanceof Yielded)) panic("an effect performed inside a generator that is not handled here");
    return r.value;
  }

  // What a `for` iterates directly.
  function items(v) {
    if (Array.isArray(v)) return v;
    if (v instanceof Bytes) return v.items();
    if (typeof v === "string") return Array.from(v, (c) => BigInt(c.charCodeAt(0)));
    panic(`cannot iterate over ${show(v)}`);
  }

  // ---- strings ----

  // A string's bytes, `s.asBytes()`: a view of the string, not a copy of it.
  class Bytes {
    constructor(s) { this.s = s; }
    get length() { return this.s.length; }
    items() { return Array.from(this.s, (c) => BigInt(c.charCodeAt(0))); }
  }

  // ---- integers ----

  const BOUNDS = {
    i8: [-(1n << 7n), (1n << 7n) - 1n], i16: [-(1n << 15n), (1n << 15n) - 1n], i32: [-(1n << 31n), (1n << 31n) - 1n],
    i64: [-(1n << 63n), (1n << 63n) - 1n], isize: [-(1n << 63n), (1n << 63n) - 1n], i128: [-(1n << 127n), (1n << 127n) - 1n],
    u8: [0n, 255n], u16: [0n, 65535n], u32: [0n, (1n << 32n) - 1n], u64: [0n, (1n << 64n) - 1n], usize: [0n, (1n << 64n) - 1n],
  };
  const WIDTHS = { i8: [8, true], i16: [16, true], i32: [32, true], i64: [64, true], isize: [64, true], i128: [128, true],
    u8: [8, false], u16: [16, false], u32: [32, false], u64: [64, false], usize: [64, false] };
  const checks = {}, wraps = {};
  for (const name of Object.keys(BOUNDS)) {
    const [lo, hi] = BOUNDS[name];
    const [w, signed] = WIDTHS[name];
    // Overflowing `i128`, the widest type, is overflowing whatever the static type is.
    checks[name] = (x) => {
      if (x < lo || x > hi) {
        if (x < BOUNDS.i128[0] || x > BOUNDS.i128[1]) panic("arithmetic overflow");
        panic(`arithmetic overflow: ${x} does not fit in \`${name}\``);
      }
      return x;
    };
    wraps["wrap_" + name] = signed ? (x) => BigInt.asIntN(w, x) : (x) => BigInt.asUintN(w, x);
  }
  function div(x, y, check) {
    if (y === 0n) panic("division by zero");
    return check(x / y);
  }
  function rem(x, y) {
    if (y === 0n) panic("division by zero");
    return x % y;
  }
  function fmod(x, y) { return x % y; }
  function truncFloat(f) {
    if (Number.isNaN(f)) return 0n;
    if (f >= 1.7e38) return BOUNDS.i128[1];
    if (f <= -1.7e38) return BOUNDS.i128[0];
    return BigInt(Math.trunc(f));
  }
  const toInt = (v) => (typeof v === "boolean" ? (v ? 1n : 0n) : v);

  // ---- lists ----

  function at(a, i) {
    const n = Number(i);
    if (n < 0 || n >= a.length) panic(`index ${i} out of bounds (length ${a.length})`);
    return n;
  }
  function idx(a, i) {
    const n = at(a, i);
    if (a instanceof Bytes) return BigInt(a.s.charCodeAt(n));
    if (typeof a === "string") return BigInt(a.charCodeAt(n));
    return a[n];
  }
  const continuation = (s, i) => i < s.length && (s.charCodeAt(i) & 0xc0) === 0x80;
  function slice(a, lo, hi) {
    const l = Number(lo), h = hi === undefined ? a.length : Number(hi);
    if (l > h || h > a.length) panic(`range ${l}..${h} out of bounds (length ${a.length})`);
    // A string's bounds fall between characters: not on a UTF-8 continuation byte (§3.1).
    if (typeof a === "string" && (continuation(a, l) || continuation(a, h))) panic(`range ${l}..${h} splits a character`);
    if (a instanceof Bytes) return new Bytes(a.s.slice(l, h));
    return a.slice(l, h);
  }

  // A `Copy` object copied: JavaScript shares objects, Flyscript copies `Copy` ones.
  function copy(v) {
    if (typeof v !== "object" || v === null) return v;
    if (Array.isArray(v)) return v.map(copy);
    if (Object.getPrototypeOf(v) !== Object.prototype) return v;
    const out = {};
    for (const k of Object.keys(v)) out[k] = copy(v[k]);
    return out;
  }

  // ---- display ----

  function showFloat(f) {
    if (Number.isInteger(f) && Math.abs(f) < 1e15) return f.toFixed(1);
    if (Number.isNaN(f)) return "NaN";
    if (f === Infinity) return "inf";
    if (f === -Infinity) return "-inf";
    return String(f);
  }
  function quoted(s) {
    return "\"" + s.replace(/[\\"\n\t\r]/g, (c) => ({ "\\": "\\\\", "\"": "\\\"", "\n": "\\n", "\t": "\\t", "\r": "\\r" })[c]) + "\"";
  }
  // What `Show.show` writes, as a string.
  function shown(show, v) {
    const out = { v: "" };
    show(v, out);
    return out.v;
  }
  // A value's structure, as the interpreter shows one with no `Show` to hand.
  function show(v) {
    switch (typeof v) {
      case "string": return v;
      case "bigint": case "boolean": return String(v);
      case "number": return showFloat(v);
      case "undefined": return "void";
      case "function": return "<function>";
    }
    return nested(v);
  }
  function nested(v) {
    if (typeof v === "string") return quoted(v);
    if (typeof v !== "object" || v === null) return show(v);
    if (Array.isArray(v)) return "[" + v.map(nested).join(", ") + "]";
    if (v instanceof Bytes) return nested(v.items());
    if (v.$tag !== undefined) {
      if (!("$" in v)) return "#" + v.$tag;
      if (Array.isArray(v.$)) return "#" + v.$tag + "(" + v.$.map(nested).join(", ") + ")";
      if (typeof v.$ === "object" && v.$ !== null && Object.getPrototypeOf(v.$) === Object.prototype && v.$.$tag === undefined) return "#" + v.$tag + " " + nested(v.$);
      return "#" + v.$tag + "(" + nested(v.$) + ")";
    }
    if (v instanceof HashMap) return "{ " + [...v.m.values()].map(([k, x]) => nested(k) + ": " + nested(x)).join(", ") + " }";
    const fields = Object.keys(v).sort().map((k) => k + ": " + nested(v[k]));
    return "{ " + fields.join(", ") + " }";
  }

  // ---- structural order, for what the runtime sorts ----

  function compare(a, b) {
    switch (typeof a) {
      case "number":
        if (Number.isNaN(a)) return Number.isNaN(b) ? 0 : 1;
        if (Number.isNaN(b)) return -1;
        return a < b ? -1 : a > b ? 1 : 0;
      case "bigint": case "string": case "boolean":
        return a < b ? -1 : a > b ? 1 : 0;
    }
    if (Array.isArray(a)) {
      const n = Math.min(a.length, b.length);
      for (let i = 0; i < n; i++) { const c = compare(a[i], b[i]); if (c !== 0) return c; }
      return a.length < b.length ? -1 : a.length > b.length ? 1 : 0;
    }
    return compare(keyOf(a), keyOf(b));
  }
  const ordinal = (o) => (o.$tag === "Less" ? -1 : o.$tag === "Greater" ? 1 : 0);

  // ---- maps ----

  // A key's identity: its structure, as equal values have equal structure.
  function keyOf(k) {
    switch (typeof k) {
      case "string": return "s" + k;
      case "bigint": return "i" + k;
      case "boolean": return k ? "t" : "f";
      case "number": return "n" + (k === 0 ? 0 : k);
      case "undefined": return "u";
    }
    if (Array.isArray(k)) return "[" + k.map(keyOf).join(",") + "]";
    if (k instanceof Bytes) return "s" + k.s;
    return "{" + Object.keys(k).sort().map((f) => f + ":" + keyOf(k[f])).join(",") + "}";
  }

  class HashMap {
    constructor() { this.m = new Map(); }
  }
  const none = () => ({ $tag: "None" });
  const some = (v) => ({ $tag: "Some", $: v });

  class Hasher {
    constructor() { this.h = 0xcbf29ce484222325n; }
    bytes(bs) { for (const b of bs) this.h = BigInt.asUintN(64, (this.h ^ BigInt(b)) * 0x100000001b3n); }
  }

  // ---- the simulated world ----

  let clock = 0n;

  // The deterministic world the program runs against (§6.4), from `FLY_WORLD`, JSON: connections
  // waiting to be accepted, a database of profiles and quotas, the percent of I/O operations that
  // time out, and the seed that decides which do, and how tasks interleave.
  const world = Object.assign({ incoming: [], profiles: {}, quotas: {}, faults: 0, seed: 0x5eed },
    process.env.FLY_WORLD ? JSON.parse(process.env.FLY_WORLD) : {});
  let faultRng = BigInt(Math.max(1, world.seed));
  // Whether the next I/O operation fails.
  function fault() {
    let r = faultRng;
    r = BigInt.asUintN(64, r ^ (r << 13n));
    r = BigInt.asUintN(64, r ^ (r >> 7n));
    r = BigInt.asUintN(64, r ^ (r << 17n));
    faultRng = r;
    return r % 100n < BigInt(world.faults);
  }

  // ---- tasks (§6.1): one runs at a time, and at each scheduling point the next is chosen by a
  // seeded generator, as the interpreter's scheduler does, so a seed reproduces an interleaving.

  // What a task's generator yields to the scheduler: a scheduling point, or a wait.
  class Point {
    constructor(wait) { this.wait = wait; }
  }
  class Cancelled extends Error {}
  const sched = {
    on: false, current: 0, ready: [], blocked: new Map(), finished: new Set(), rng: BigInt(Math.max(1, world.seed)), next: 1,
    tasks: new Map(), channels: new Map(), closed: new Set(), senders: new Map(), cancelled: new Set(), scopes: new Map(), scopeIds: 1,
  };
  // Hands the baton to a ready task, chosen by the seed; `false` if none can run.
  function pass() {
    if (sched.ready.length === 0) return false;
    let r = sched.rng;
    r = BigInt.asUintN(64, r ^ (r << 13n));
    r = BigInt.asUintN(64, r ^ (r >> 7n));
    r = BigInt.asUintN(64, r ^ (r << 17n));
    sched.rng = r;
    const i = Number(r % BigInt(sched.ready.length));
    sched.current = sched.ready.splice(i, 1)[0];
    return true;
  }
  function wake(kind, id) {
    for (const [t, w] of [...sched.blocked]) {
      if (w[0] === kind && w[1] === id) { sched.blocked.delete(t); sched.ready.push(t); }
    }
  }
  // A scheduling point: another ready task may run, this one again among them.
  function* point() { if (sched.on) yield new Point(undefined); }
  // Parks the task until `wait` is met.
  function* block(wait) {
    if (!sched.on) panic("deadlock: every task is waiting");
    yield new Point(wait);
  }
  function cancel(t) {
    sched.cancelled.add(t);
    if (sched.blocked.delete(t)) sched.ready.push(t);
  }
  // Runs the tasks, starting with `main`, until `main` ends.
  function runTasks(main) {
    sched.on = true;
    sched.tasks.set(0, { gen: main, input: undefined, error: undefined });
    for (;;) {
      const me = sched.current;
      const t = sched.tasks.get(me);
      let r;
      try {
        // A cancelled task unwinds at its next scheduling point; one not started never runs.
        if (t.error === undefined && sched.cancelled.has(me)) t.error = new Cancelled();
        const error = t.error, input = t.input;
        t.error = undefined;
        t.input = undefined;
        r = error !== undefined ? t.gen.throw(error) : t.gen.next(input);
      } catch (e) {
        if (me === 0) throw e;
        endTask(me, { error: e });
        continue;
      }
      if (r.done) {
        if (me === 0) return r.value;
        endTask(me, { value: r.value });
        continue;
      }
      if (!(r.value instanceof Point)) panic("an effect performed that nothing handles");
      if (r.value.wait === undefined) {
        sched.ready.push(me);
        pass();
      } else {
        sched.blocked.set(me, r.value.wait);
        if (!pass()) {
          // Nothing else can run, so nothing can ever wake this task: reported, not waited on.
          sched.blocked.delete(me);
          sched.current = me;
          t.error = new Panic("deadlock: every task is waiting");
        }
      }
    }
  }
  // Task `me` has finished: its outcome goes to its scope, and its joiners wake.
  function endTask(me, outcome) {
    const t = sched.tasks.get(me);
    const st = sched.scopes.get(t.scope);
    if (outcome.error === undefined) {
      st.fibers.set(me, { value: outcome.value });
    } else if (outcome.error instanceof Fail) {
      // The first failure cancels the scope: its body and its other tasks.
      if (st.failure === undefined) {
        st.failure = outcome.error;
        cancel(st.owner);
        for (const o of st.tasks) if (o !== me) cancel(o);
      }
      st.fibers.set(me, { error: outcome.error });
    } else if (outcome.error instanceof Panic) {
      if (st.panic === undefined) st.panic = outcome.error;
    } else if (!(outcome.error instanceof Cancelled)) {
      throw outcome.error;
    }
    sched.finished.add(me);
    wake("task", me);
    if (!pass()) panic("deadlock: every task is waiting");
  }
  function* join(t) {
    if (!sched.finished.has(t)) yield* block(["task", t]);
  }
  // A task's body: a generator, or what a plain closure gives.
  function* body(f, ...args) {
    const r = f(...args);
    if (r !== null && typeof r === "object" && typeof r.next === "function" && typeof r[Symbol.iterator] === "function") return yield* r;
    return r;
  }
  function spawnTask(sid, task) {
    const id = sched.next++;
    sched.ready.push(id);
    sched.tasks.set(id, { gen: body(task), input: undefined, error: undefined, scope: sid });
    sched.scopes.get(sid).tasks.push(id);
    return id;
  }
  function channel() {
    const id = sched.next++;
    sched.channels.set(id, []);
    sched.senders.set(id, 1);
    return id;
  }
  function* send(ch, v) {
    sched.channels.get(ch).push(v);
    wake("channel", ch);
    yield* point();
  }
  // The next message, or `undefined` once the channel is closed and drained.
  function* recv(ch) {
    for (;;) {
      const q = sched.channels.get(ch);
      if (q.length > 0) return { v: q.shift() };
      if (sched.closed.has(ch)) return undefined;
      yield* block(["channel", ch]);
    }
  }
  function* close(ch) {
    const left = Math.max(0, (sched.senders.get(ch) || 0) - 1);
    sched.senders.set(ch, left);
    if (left === 0) { sched.closed.add(ch); wake("channel", ch); }
    yield* point();
  }

  // ---- what the standard library declares without a body ----

  const $b = {
    panic,
    println(s) { process.stdout.write(Buffer.from(s + "\n", "latin1")); },
    writeFile(path, content) {
      try { fs.writeFileSync(Buffer.from(path, "latin1").toString("utf8"), Buffer.from(content, "latin1")); }
      catch (e) { throw new Fail({ $tag: "PermissionDenied" }); }
    },
    parseInt(s) { return /^[+-]?\d+$/.test(s) ? some(BigInt(s)) : none(); },
    parseFloat(s) { const f = Number(s); return s.trim() !== "" && !Number.isNaN(f) ? some(f) : none(); },
    replace(r, v) { const old = r.v; r.v = v; return old; },
    swap(a, b) { const t = a.v; a.v = b.v; b.v = t; },
    alloc: (v) => v,
    allocAll: (vs) => vs.slice(),
    fmt: (s) => s,
    copyUtf8: (bytes) => (bytes instanceof Bytes ? bytes.s : String.fromCharCode(...bytes.map(Number))),
    repeat: (v, n) => Array.from({ length: n }, () => copy(v)),
    generate: (producer) => new Gen(producer()),

    Option_isSome: (o) => o.$tag === "Some",
    Option_take(r) { const old = r.v; r.v = none(); return old; },
    Option_unwrapOr: (o, d) => (o.$tag === "Some" ? o.$ : d),
    Option_cloned: (o) => o,
    Result_unwrap: (r) => (r.$tag === "Ok" ? r.$ : raise(r.$)),
    Fail_capture(body) {
      try { return { $tag: "Ok", $: body() }; }
      catch (e) { if (e instanceof Fail) return { $tag: "Err", $: e.value }; throw e; }
    },
    Fail_map(body, wrap) {
      try { return body(); }
      catch (e) { if (e instanceof Fail) throw new Fail(wrap(e.value)); throw e; }
    },

    String_new: () => "",
    String_len: (s) => BigInt(s.length),
    String_push(r, s) { r.v = r.v + s; },
    String_asStr: (s) => s,
    String_clone: (s) => s,
    String_fromUtf8: (bytes) => some(String.fromCharCode(...bytes.map(Number))),
    str_slice: (s, i, j) => slice(s, i, j),
    str_len: (s) => BigInt(s.length),
    str_toString: (s) => s,
    *str_bytes(s) { for (let i = 0; i < s.length; i++) yield new Yielded(BigInt(s.charCodeAt(i))); },
    str_asBytes: (s) => new Bytes(s),
    *str_splitWhitespace(s) { for (const w of s.split(/[ \t\n\r]+/)) if (w !== "") yield new Yielded(w); },
    *str_lines(s) { const ls = s.split("\n"); if (ls[ls.length - 1] === "") ls.pop(); for (const l of ls) yield new Yielded(l.endsWith("\r") ? l.slice(0, -1) : l); },
    str_split: (s, sep) => s.split(sep),
    str_trim: (s) => s.replace(/^[ \t\n\r]+|[ \t\n\r]+$/g, ""),
    str_includes: (s, p) => s.includes(p),
    str_startsWith: (s, p) => s.startsWith(p),
    str_endsWith: (s, p) => s.endsWith(p),
    str_indexOf: (s, p) => { const i = s.indexOf(p); return i < 0 ? none() : some(BigInt(i)); },
    // Byte strings hold UTF-8: only ASCII letters change case.
    str_toUpperCase: (s) => s.replace(/[a-z]/g, (c) => c.toUpperCase()),
    str_toLowerCase: (s) => s.replace(/[A-Z]/g, (c) => c.toLowerCase()),
    str_replaceAll: (s, a, b) => s.split(a).join(b),

    slice_len: (a) => BigInt(a.length),
    slice_iter: (a) => genOf(items(a)),
    slice_iterMut: (r) => { const a = r.v; return new Gen((function* () { for (let i = 0; i < a.length; i++) yield new Yielded(new FieldRef(a, i)); })()); },
    slice_splitAt(r, i) { const a = r.v; const n = at(a.concat([undefined]), i); return [new RangeRef(a, 0, n), new RangeRef(a, n, a.length)]; },
    slice_sortBy(r, cmp) {
      const a = r.v;
      const sorted = a.map((x, i) => [x, i]).sort((x, y) => ordinal(cmp(x[0], y[0])) || x[1] - y[1]).map((x) => x[0]);
      r.v = sorted;
      if (r instanceof RangeRef) return;
      for (let i = 0; i < sorted.length; i++) a[i] = sorted[i];
    },
    slice_reverse(r) { r.v = r.v.slice().reverse(); },
    *slice_each(a) { for (const x of items(a)) yield new Yielded(x); },
    *array_each(a) { for (const x of a) yield new Yielded(x); },

    // `std/par`: a list split into disjoint slices, each lent `mut`.
    slice_slice: (r) => (r instanceof RangeRef ? r : new RangeRef(r.v, 0, r.v.length)),
    array_slice: (r) => $b.slice_slice(r),
    Vec_slice: (r) => $b.slice_slice(r),
    slice_split(s, i) {
      const [a, lo, hi] = rangeOf(s), n = Number(i);
      if (n > hi - lo) panic(`index ${i} out of bounds (length ${hi - lo})`);
      return [new RangeRef(a, lo, lo + n), new RangeRef(a, lo + n, hi)];
    },
    array_split: (s, i) => $b.slice_split(s, i),
    Vec_split: (s, i) => $b.slice_split(s, i),
    slice_viewAt(s, i) { const [a, lo, hi] = rangeOf(s); if (i < 0n || Number(i) >= hi - lo) panic(`index ${i} out of bounds (length ${hi - lo})`); return new FieldRef(a, lo + Number(i)); },
    array_viewAt: (s, i) => $b.slice_viewAt(s, i),
    Vec_viewAt: (s, i) => $b.slice_viewAt(s, i),
    slice_readAt: (a, i) => idx(a, i),
    array_readAt: (a, i) => idx(a, i),
    Vec_readAt: (a, i) => idx(a, i),
    array_len: (a) => BigInt(a.length),

    Vec_new: () => [],
    Vec_push(r, x) { r.v.push(x); },
    Vec_pop(r) { const a = r.v; return a.length === 0 ? none() : some(a.pop()); },
    Vec_remove(r, i) { const a = r.v; return a.splice(at(a, i), 1)[0]; },
    Vec_insert(r, i, x) { const a = r.v; if (i < 0n || Number(i) > a.length) panic(`index ${i} out of bounds (length ${a.length})`); a.splice(Number(i), 0, x); },
    Vec_retain(r, keep) { const a = r.v; let j = 0; for (const x of a) if (keep(x)) a[j++] = x; a.length = j; },
    Vec_truncate(r, n) { const a = r.v; if (a.length > Number(n)) a.length = Number(n); },
    Vec_drain(r) { const a = r.v; return genOf(a.splice(0)); },
    Vec_len: (a) => BigInt(a.length),
    Vec_iter: (a) => genOf(a),
    Vec_iterMut: (r) => $b.slice_iterMut(r),
    *Vec_each(a) { for (const x of a) yield new Yielded(x); },

    Box_new: (v) => v, Box_get: (v) => v, Box_into: (v) => v,
    Arc_new: (v) => v, Arc_get: (v) => v, Arc_clone: (v) => v,
    Ref_get: (v) => v, Ref_clone: (v) => v,

    Hasher_new: () => new Hasher(),
    Hasher_writeInt(r, i) { const b = []; let x = BigInt.asUintN(64, i); for (let k = 0; k < 8; k++) { b.push(Number(x & 255n)); x >>= 8n; } r.v.bytes(b); },
    Hasher_writeFloat(r, f) { $b.Hasher_writeStr(r, String(f === 0 ? 0 : f)); },
    Hasher_writeBool(r, b) { r.v.bytes([b ? 1 : 0]); },
    Hasher_writeStr(r, s) { r.v.bytes(Array.from(s, (c) => c.charCodeAt(0))); },
    Hasher_finish: (h) => h.h,

    HashMap_new: () => new HashMap(),
    HashMap_insert(r, k, v) { r.v.m.set(keyOf(k), [k, v]); },
    HashMap_get(m, k) { const e = m.m.get(keyOf(k)); return e === undefined ? none() : some(e[1]); },
    HashMap_getMut(r, k) { const e = r.v.m.get(keyOf(k)); return e === undefined ? none() : some(new FieldRef(e, 1)); },
    HashMap_has: (m, k) => m.m.has(keyOf(k)),
    HashMap_remove(r, k) {
      const m = r.v.m, key = keyOf(k), e = m.get(key);
      if (e === undefined) return none();
      m.delete(key);
      return some(e[1]);
    },
    HashMap_len: (m) => BigInt(m.m.size),
    HashMap_keys: (m) => genOf(Array.from(m.m.values(), (e) => e[0])),
    HashMap_values: (m) => genOf(Array.from(m.m.values(), (e) => e[1])),
    HashMap_valuesMut: (r) => genOf(Array.from(r.v.m.values(), (e) => new FieldRef(e, 1))),
    HashMap_entries: (m) => genOf(Array.from(m.m.values(), (e) => [e[0], e[1]])),
    HashMap_sortedByValue: (m) => Array.from(m.m.values(), (e) => [e[0], e[1]]).sort((a, b) => compare(b[1], a[1]) || compare(a[0], b[0])),

    Cell_new: (v) => ({ v }),
    Cell_get: (c) => c.v,
    Cell_set(c, v) { c.v = v; },
    Cell_clone: (c) => c,
    RegionList_new: () => [],
    RegionList_push(l, v) { l.push(v); },
    RegionList_len: (l) => BigInt(l.length),
    RegionList_clone: (l) => l,
    *RegionList_each(l) { for (const x of l) yield new Yielded(x); },

    Gen_next(r) { const s = step(r.v); return s === undefined ? none() : some(s.item); },
    Gen_map: (g, f) => new Gen((function* () { for (let s = step(g); s !== undefined; s = step(g)) yield new Yielded(f(s.item)); })()),
    Gen_filter: (g, keep) => new Gen((function* () { for (let s = step(g); s !== undefined; s = step(g)) if (keep(s.item)) yield s; })()),
    Gen_take: (g, n) => new Gen((function* () { let i = 0n; if (i >= n) return; for (let s = step(g); s !== undefined; s = step(g)) { yield s; if (++i >= n) return; } })()),
    Gen_zip: (g, h) => new Gen((function* () { for (let s = step(g); s !== undefined; s = step(g)) { const t = step(h); if (t === undefined) return; yield new Yielded([s.item, t.item]); } })()),
    Gen_enumerate: (g) => new Gen((function* () { let i = 0n; for (let s = step(g); s !== undefined; s = step(g)) yield new Yielded([i++, s.item]); })()),
    Gen_collect(g) { const out = []; for (let s = step(g); s !== undefined; s = step(g)) out.push(s.item); return out; },
    *Gen_each(g) { yield* g.it; },
    Gen_drop(r) { if (r.v.it.return) r.v.it.return(); },

    File_open(path) {
      try { return { text: fs.readFileSync(Buffer.from(path, "latin1").toString("utf8")).toString("latin1") }; }
      catch (e) { throw new Fail({ $tag: "NotFound" }); }
    },
    File_readText: (r) => r.v.text,
    *File_lines(r) { yield* $b.str_lines(r.v.text); },

    // ---- tasks and channels: generators, as they are scheduling points ----
    *Io_scope$g(f) {
      const sid = sched.scopeIds++;
      const st = { owner: sched.current, tasks: [], fibers: new Map(), failure: undefined, panic: undefined };
      sched.scopes.set(sid, st);
      let result, error;
      try { result = yield* body(f, { v: { sid } }); }
      catch (e) {
        // The body unwound because a task failed: the scope rethrows that failure.
        if (!(e instanceof Cancelled && st.failure !== undefined)) error = e;
      }
      sched.cancelled.delete(sched.current);
      // A scope returns only when every task started in it has finished (§6.1).
      for (const t of st.tasks) {
        for (;;) {
          try { yield* join(t); break; }
          catch (e) { if (!(e instanceof Cancelled)) throw e; sched.cancelled.delete(sched.current); }
        }
      }
      sched.cancelled.delete(sched.current);
      sched.scopes.delete(sid);
      if (st.panic !== undefined) throw st.panic;
      if (error !== undefined) throw error;
      if (st.failure !== undefined) throw st.failure;
      return result;
    },
    *Scope_spawn$g(r, task) { spawnTask(r.v.sid, task); yield* point(); },
    *Scope_fork$g(r, task) { const t = spawnTask(r.v.sid, task); yield* point(); return { task: t }; },
    *Fiber_join$g(f) {
      yield* join(f.task);
      for (const st of sched.scopes.values()) {
        const o = st.fibers.get(f.task);
        if (o !== undefined) { if (o.error !== undefined) throw o.error; return o.value; }
      }
      panic("a joined task did not finish");
    },
    channel: () => { const ch = channel(); return [{ ch }, { ch }]; },
    Reply_new: () => { const ch = channel(); return [{ ch }, { ch }]; },
    *Sender_send$g(s, v) { yield* send(s.ch, v); },
    *Reply_send$g(s, v) { yield* send(s.ch, v); },
    *Receiver_recv$g(rx) { const m = yield* recv(rx.ch); return m === undefined ? none() : some(m.v); },
    *Pending_wait$g(p) { const m = yield* recv(p.ch); if (m === undefined) panic("the reply was dropped unsent"); return m.v; },
    *Sender_close$g(s) { yield* close(s.ch); },
    // A destructor does not suspend: a sender dropped closes its channel then and there.
    Sender_drop(r) {
      const ch = r.v.ch, left = Math.max(0, (sched.senders.get(ch) || 0) - 1);
      sched.senders.set(ch, left);
      if (left === 0) { sched.closed.add(ch); wake("channel", ch); }
    },
    Sender_clone: (s) => { sched.senders.set(s.ch, (sched.senders.get(s.ch) || 0) + 1); return { ch: s.ch }; },
    *Receiver_each(rx) { for (let m = yield* recv(rx.ch); m !== undefined; m = yield* recv(rx.ch)) yield new Yielded(m.v); },
    Mutex_new: (v) => ({ v }),
    *Mutex_lock$g(m, f) { yield* point(); return yield* body(f, m); },

    // ---- the simulated network and database ----
    Listener_bind: () => ({ listener: 0 }),
    *Listener_accept() {
      while (world.incoming.length > 0) yield new Yielded({ input: world.incoming.shift(), pos: 0 });
    },
    Socket_read(r, buf) {
      if (fault()) throw new Fail({ $tag: "TimedOut" });
      const sock = r.v, cells = buf.v, n = Math.min(cells.length, sock.input.length - sock.pos);
      for (let i = 0; i < n; i++) cells[i] = BigInt(sock.input.charCodeAt(sock.pos + i));
      buf.v = cells;
      sock.pos += n;
      return BigInt(n);
    },
    Socket_writeStatus(r, code, body) {
      if (fault()) throw new Fail({ $tag: "BrokenPipe" });
      // The simulated client's transcript doubles as the program's output.
      $b.println(`-> ${code} ${body}`);
    },
    Socket_close() {},
    Db_connect: () => ({ db: 0 }),
    Db_fetchProfile(db, user) {
      if (fault()) throw new Fail({ $tag: "TimedOut" });
      const name = world.profiles[user];
      if (name === undefined) throw new Fail({ $tag: "NotFound" });
      return { displayName: name };
    },
    Db_checkQuota(db, token) {
      if (fault()) throw new Fail({ $tag: "TimedOut" });
      return { allowed: world.quotas[token] === true };
    },

    Io_now: () => ({ nanos: clock }),
    Io_sleep(d) { clock += d.nanos; },
    Io_write(fd, buf) {
      const s = buf instanceof Bytes ? buf.s : String.fromCharCode(...buf.map(Number));
      process.stdout.write(Buffer.from(s, "latin1"));
      return { $tag: "Ok", $: BigInt(s.length) };
    },
    Io_read: () => ({ $tag: "Ok", $: 0n }),
  };
  // The root `Io` operations are scheduling points.
  for (const op of ["Io_now", "Io_sleep", "Io_write", "Io_read"]) {
    const f = $b[op];
    $b[op + "$g"] = function* (...args) { yield* point(); return f(...args); };
  }
  // Higher-order builtins whose closures may suspend.
  $b.Fail_capture$g = function* (f) {
    try { return { $tag: "Ok", $: yield* body(f) }; }
    catch (e) { if (e instanceof Fail) return { $tag: "Err", $: e.value }; throw e; }
  };
  $b.Fail_map$g = function* (f, wrap) {
    try { return yield* body(f); }
    catch (e) { if (e instanceof Fail) throw new Fail(yield* body(wrap, e.value)); throw e; }
  };
  $b.Gen_next$g = function* (r) {
    const g = r.v;
    let answer;
    for (;;) {
      const s = g.it.next(answer);
      if (s.done) return none();
      if (s.value instanceof Yielded) return some(s.value.item);
      answer = yield s.value;
    }
  };
  // Steps a generator, passing on what it performs other than its items.
  function* items$g(g, each) {
    let answer;
    for (;;) {
      const s = g.it.next(answer);
      answer = undefined;
      if (s.done) return;
      if (s.value instanceof Yielded) { if ((yield* each(s.value.item)) === false) return; }
      else answer = yield s.value;
    }
  }
  $b.Gen_map$g = (g, f) => new Gen(items$g(g, function* (x) { yield new Yielded(yield* body(f, x)); }));
  $b.Gen_filter$g = (g, keep) => new Gen(items$g(g, function* (x) { if (yield* body(keep, x)) yield new Yielded(x); }));
  $b.Gen_collect$g = function* (g) { const out = []; yield* items$g(g, function* (x) { out.push(x); }); return out; };
  // Any other builtin, called where its caller may suspend, is the same as a generator.
  for (const k of Object.keys($b)) {
    const f = $b[k];
    if (k.endsWith("$g") || $b[k + "$g"] !== undefined || f.constructor.name === "GeneratorFunction") continue;
    $b[k + "$g"] = function* (...args) { return f(...args); };
  }
  for (const t of ["i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "usize"]) {
    const [w, signed] = WIDTHS[t];
    const wrap = signed ? (x) => BigInt.asIntN(w, x) : (x) => BigInt.asUintN(w, x);
    $b[t + "_wrappingAdd"] = (a, b) => wrap(a + b);
    $b[t + "_wrappingSub"] = (a, b) => wrap(a - b);
    $b[t + "_wrappingMul"] = (a, b) => wrap(a * b);
  }

  // ---- running a program ----

  const argv = process.argv.slice(2).map((a) => Buffer.from(a, "utf8").toString("latin1"));
  const argStr = (i) => argv[i];
  function argInt(i) { return /^-?\d+$/.test(argv[i]) ? BigInt(argv[i]) : panic(`argument ${i + 1} is not an integer`); }

  // Runs a program's `main`, as `flyc run` does.
  function start(main, suspends, tasks) {
    try {
      if (tasks) runTasks(body(main));
      else {
        const r = main();
        if (suspends) for (let s = r.next(); !s.done; s = r.next()) panic("an effect performed that nothing handles");
      }
    } catch (e) {
      if (e instanceof Panic) { process.stdout.write(Buffer.from(`<panic: ${e.message}>\n`, "latin1")); process.exit(101); }
      if (e instanceof Fail) { process.stdout.write(Buffer.from(`<uncaught: ${show(e.value)}>\n`, "latin1")); process.exit(1); }
      throw e;
    }
  }

  const $rt = {
    Fail, Panic, Return, YIELD, handle, run, drive, moved, isMoved, sub, unmove, panic, raise, FieldRef, indexRef, rangeRef, yielded, isYield, perform, items,
    div, rem, fmod, truncFloat, toInt, at, idx, slice, copy, showFloat, shown, show,
    unmatched: (v) => panic(`no arm matched ${show(v)}`),
    argStr, argInt, start,
    ...checks, ...wraps,
  };
  return { $rt, $b };
})();
