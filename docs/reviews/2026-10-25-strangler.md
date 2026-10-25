# Review: strangler

- spec: 0cb38fcb682a
- request: af7236b9199f3845
- tokens: prompt 61122, cached 0, answer 4275

## Question

# Strangling a Next.js app with FlyNext: design check

FlyNext is Flyscript's web framework: a native server (Flyscript's own HTTP/1.1, a task per connection) renders pages from `Ui<M>` views; in the browser one WebAssembly program per site (core + a module per route, JSPI) hydrates and diffs flat op lists. RPC: `api.fly` declares effects; the browser's handler POSTs `/_fly/rpc/Effect.op` with JSON args; the server handles them. Messages are values (no closures in renders): `on("click", #Open(3))`, and `update(m, msg, ev: Event)` gets the event's text/key/checked.

Goal: an existing Next.js + React + TS app migrates one route/component/endpoint at a time. Done when an e2e test runs a hybrid site where a Next.js page calls `api.fly` through a generated `api.ts`, mounts a `<FlyIsland>`, follows a link into a native `.flyx` page that embeds a React widget, and both share session cookies.

## Plan

1. **Front proxy.** The FlyNext server is the front door (`--upstream=http://127.0.0.1:3001`). It answers natively: its routes, `public/`, `/_fly/*`. Any other request is forwarded: method, path+query, headers (Host kept, `X-Forwarded-For/Host/Proto` added, hop-by-hop dropped), body as bytes (request bodies become `Vec<u8>`; chunked request bodies decoded). One upstream TCP connection per request with `Connection: close`. The upstream response's head is parsed; body relayed by its framing (Content-Length copied, chunked relayed chunk by chunk as it arrives, close-delimited re-chunked so the client connection stays alive). `Upgrade` (Next dev HMR websocket) is tunnelled: after the 101, two tasks copy bytes each way until either side closes. With an upstream, FlyNext's own 404 page never answers; the upstream's does.
2. **Links.** The browser program intercepts only links to FlyNext routes (route patterns shipped to the page and matched client-side); others navigate normally. Next's `<Link>` to a FlyNext route is a plain navigation (Next client router fetch of a non-Next page falls back to hard navigation).
3. **FlyNext inside React (islands).** `app/islands/<name>.fly(x)` exports `Model`, `Msg`, `view`, optional `update`, optional `initial`. Each becomes its own small WebAssembly program (`/_fly/islands/<name>.wasm`), whose `main` runs `view/update` on a given root, model from JSON passed in (or `initial()`), app effects by RPC. `flynext.js` exports `mountIsland(el, url, initialJson)` — the same host as a page, minus link/history interception, one instance per island. The build also writes `FlyIsland.tsx`, a React component that mounts one in a `useEffect`, loading `/_fly/flynext.js` at run time (`webpackIgnore`).
4. **React inside FlyNext.** `react(name, props, msg)` in `ui.fly` renders `<div data-fly-react=name data-fly-props=json>` with no children and an event `fly-react` giving `msg`; the host mounts `globalThis.FlyReact[name]` with `ReactDOM.createRoot` the first time it sees the node and re-renders when `data-fly-props` changes; the component gets `emit(text)`, which is an event whose `ev.text` is `text`. The diff never touches children it did not record, so React's DOM survives patches. Deliberate deviation from the roadmap's `onMsg: (e: Event) => M`: a message value, as every event in FlyNext is, its payload in `ev.text`.
5. **Typed client.** From `api.fly`'s AST (and the types it imports from the app), the build writes `api.ts`: each op an `async` function POSTing to `/_fly/rpc`, TS types mapped from Flyscript's JSON encoding: records/structs → object types; tag unions/enums → unions of `"Name"` and `{ Name: payload }`; `Option<T>` → `T | null`; `Vec<T>`/slices/arrays → `T[]`; tuples → TS tuples; integers and floats → `number`; `String`/`str` → `string`; `Result<T, E>` → `{ Ok: T } | { Err: E }`.

## Questions
1. Is the front-proxy direction right (FlyNext in front, Next behind), versus Next in front with rewrites to FlyNext? I chose FlyNext in front so cookies, RPC and islands are same-origin with no Next config, and so the end state is "remove the upstream flag".
2. Per-request upstream connections with `Connection: close` vs a keep-alive pool: acceptable for the strangled (shrinking) part?
3. Islands as separate WebAssembly instances (own memory, own copy of the runtime, ~50 KB core each) vs one shared program hosting many roots. Separate is simplest and isolates failures; is the duplication a real problem?
4. `react(name, props, msg)` with the payload in `ev.text` vs a function `(e: Event) => M` (which would need closures kept in a render). Agree with the deviation?
5. Anything in the type mapping that will bite (64-bit integers as `number`; `Option<Option<T>>` ambiguity; maps)?

## Answer

### Verdicts

- **1. Front proxy direction (FlyNext in front, Next behind):** **Agree with changes.** FlyNext in front is the right direction, but the proxy must preserve repeated response headers (`Set-Cookie`) as a list rather than a map, flush SSE / streaming chunks immediately without buffering, and retain whatever bytes the HTTP header parser already read into its buffer when switching to the WebSocket `101` tunnel.
- **2. Per-request upstream TCP connections (`Connection: close`):** **Agree.** Acceptable for a strangler proxy; on loopback (`127.0.0.1`), TCP handshake cost is ~20–50 µs and avoids pool lifecycle bugs (stale half-closed sockets, head-of-line blocking).
- **3. Islands as separate WebAssembly instances:** **Agree with changes.** Separate instances per mount are fine (and give fault isolation per island), provided the browser caches the compiled `WebAssembly.Module` per island URL (`compileStreaming` once, `instantiate` per mount) and cleans up the instance on React unmount (`useEffect` cleanup).
- **4. `react(name, props, msg)` with payload in `ev.text` instead of a closure `(e: Event) => M`:** **Agree with changes.** Keeping messages as pure data values (`M`) rather than storing closures in the op list is essential (storing closures in the render op list would break `M`'s value semantics and `§4.3` borrowing rules inside `view`), *provided* `react` is clean on unmount (`root.unmount()`) and you note that `ev.text` can carry JSON for structured payloads.
- **5. Typed client (`api.ts`) type mapping:** **Agree with changes.** Three things in `std/json`'s encoding (`§7.5`) will bite in TypeScript if not handled explicitly: multi-element tag payloads (`#A(T1, T2)` vs `#A(T)` vs `#A { ... }`), `i64`/`u64`/`i128` precision loss in JS `JSON.parse`/`JSON.stringify`, and RPC operational errors vs application `Result`.

---

### Problems

#### 1. [Front Proxy] Three Protocol Bugs That Break Next.js Auth, HMR, and Streaming (`Plan 1`)

When FlyNext's HTTP/1.1 server proxies to Next.js, three concrete Next.js behaviors will break a naive request/response relay:

1. **Multiple `Set-Cookie` headers (Session + CSRF / OAuth cookies):**
   Next.js (NextAuth / App Router cookies) routinely sends **multiple** `Set-Cookie` headers in one response. If FlyNext parses response headers into a `HashMap<String, String>`, all but one `Set-Cookie` header are silently overwritten, breaking the exact "both share session cookies" goal.
   ```ts
   // Broken if headers is HashMap<String, String>:
   // Set-Cookie: session=abc; Path=/; HttpOnly
   // Set-Cookie: csrf=xyz; Path=/
   ```
   - **Fix:** Store request and response headers in the proxy as `Vec<{ name: String; value: String }>` (or `Vec<[String, String]>`), never a `HashMap`.

2. **Buffered reads before `101 Switching Protocols` (Next.js HMR WebSocket):**
   In `Plan 1`:
   > *"`Upgrade` (Next dev HMR websocket) is tunnelled: after the 101, two tasks copy bytes each way until either side closes."*
   When FlyNext reads the upstream's `101 Switching Protocols` response headers (using a buffered reader or a `u8[4096]` stack buffer as in `§10.2`), the `Socket.read` that reads the end of the HTTP response headers (`\r\n\r\n`) will frequently read the **first WebSocket frame** sent by Next's HMR server in the same TCP segment!
   If the tunnel tasks then start copying directly from the raw `Socket` (`fd`), those already-read bytes sitting in the header parser's buffer are **dropped**, corrupting the WebSocket stream on connect.
   - **Fix:** When parsing upstream response headers (and client request headers on an `Upgrade` request), return `( ResponseHead, leftoverBytes: readonly u8[] )` and write `leftoverBytes` to the peer *before* starting the raw `Socket` copy loop:
     ```ts
     const [head, leftover] = readResponseHead(mut upConn, mut buf);
     clientConn.write( head.rawBytes );
     if (leftover.len() > 0) { clientConn.write(leftover); }
     Io.scope((s) => {
       s.spawn(() => pipe(upConn, clientConn));
       s.spawn(() => pipe(clientConn, upConn));
     });
     ```
   - Also remember: for `101`, you must **not** drop `Connection: Upgrade` or `Upgrade: websocket` when forwarding to upstream, and must **not** send `Connection: close` on an `Upgrade` request!

3. **Unflushed chunks on Next.js RSC / SSR streaming and HMR SSE (`/_next/webpack-hmr`):**
   Next.js App Router streams HTML/RSC payloads with `Transfer-Encoding: chunked`, and Next dev mode also uses Server-Sent Events (`text/event-stream`). If the chunk relay buffers chunks or waits for a buffer to fill before calling `Socket.write`, React Suspense boundaries and HMR hang.
   - **Fix:** As soon as a chunk (or partial chunk bytes) arrives from upstream, write and flush it to the client socket immediately without coalescing.

---

#### 2. [Links & Next.js Router] Next.js `<Link>` Prefetch and Soft-Navigation Do Not Automatically Fall Back Without Help (`Plan 2`)

In `Plan 2`, you wrote:
> *"Next's `<Link>` to a FlyNext route is a plain navigation (Next client router fetch of a non-Next page falls back to hard navigation)."*

Verify what Next.js (both Pages Router and App Router) actually does when a user clicks `<Link href="/migrated-fly-route">`:
1. **Pages Router:** Next looks up `/_next/data/<buildId>/migrated-fly-route.json`. That URL starts with `/_next/`, so your FlyNext front proxy will forward it to **Next.js**, which returns `404` (`{"notFound": true}`), and Next's client router renders **Next.js's 404 page client-side** instead of doing a hard navigation to FlyNext!
2. **App Router:** Next sends `GET /migrated-fly-route?_rsc=...` with header `RSC: 1`. Because `/migrated-fly-route` matches a FlyNext route, FlyNext will answer it with **HTML (`text/html`)** instead of an RSC flight payload (`text/x-component`). Depending on the Next version, when `fetch` receives `200 OK` with `Content-Type: text/html` where `text/x-component` was expected (or without `x-nextjs-rewritten-path`), Next either throws a client router error or breaks prefetch cache unless it sees a redirect/header or HTML fallback.

- **Fix (2 lines in the FlyNext route handler):**
  1. When FlyNext matches one of its own routes and sees header `RSC: 1` or `Next-Router-State-Tree` (an App Router client fetch), respond with status `200` and header `x-nextjs-redirect: <path>` (or status `205` / non-RSC `Content-Type: text/html` — test against your target Next version; in App Router, `x-nextjs-redirect: /migrated-fly-route` or a tiny capture-phase click listener in `FlyIsland.tsx` / `flynext.js` forces `window.location.href = url`).
  2. For Pages Router `/_next/data/<buildId>/<path>.json`: if `<path>` matches a FlyNext route, do **not** proxy to Next (which returns a soft 404 JSON!); return `404` with header `x-nextjs-matched-path` omitted or redirect, or intercept clicks on `a[href]` matching FlyNext routes in `flynext.js` when loaded on a Next page.

---

#### 3. [Islands & React-in-FlyNext] Lifecycle Leaks and Prop Re-entrancy (`Plan 3`, `Plan 4`)

1. **`ReactDOM.createRoot` leak when FlyNext unmounts a `react(name, props, msg)` node (`Plan 4`):**
   In `Plan 4`:
   > *"the host mounts `globalThis.FlyReact[name]` with `ReactDOM.createRoot` the first time it sees the node and re-renders when `data-fly-props` changes... The diff never touches children it did not record, so React's DOM survives patches."*
   What happens when the FlyNext page navigates to another FlyNext route, or a branch `if (showWidget) { react(...) }` turns `false` and the diff **removes** the `<div data-fly-react=...>` element from the DOM?
   If the diff simply calls `parent.removeChild(el)` without calling `root.unmount()` on the React root attached to `el`, React **never runs the widget's `useEffect` cleanups** (timers, WebSockets, event listeners leak forever!).
   - **Fix:** When the op-list diff removes a DOM node (or subtree), check if it (or any `[data-fly-react]` descendant) has a mounted `el.__flyReactRoot`, and call `el.__flyReactRoot.unmount()` before removing it.

2. **`FlyIsland.tsx` unmount and Wasm module caching (`Plan 3`):**
   - If a Next.js page renders 20 `<FlyIsland name="Counter" />` components in a list, fetching and compiling `/_fly/islands/Counter.wasm` 20 times is wasteful; caching `Map<string, Promise<WebAssembly.Module>>` in `flynext.js` and calling `WebAssembly.instantiate(module, imports)` per island takes < 0.5 ms and shares all code pages across instances.
   - When React unmounts `<FlyIsland>`, the `useEffect` cleanup must mark the island instance dead (aborting any pending RPC `fetch` / event listeners on that root) so a late RPC response doesn't try to patch a detached DOM node.

3. **Why `react(name, props, msg)` with `ev.text` is the right choice (`Plan 4`):**
   Look at `§10.8` (`Dom<M>`) and how FlyNext works: `view` is a pure function (modulo `Ui<M>`), and in Flyscript a closure `(e: Event) => M` that captures anything local to `view` is **second-class (`class 2`, `§4.3`)** — it *cannot* be stored in a heap table by the runtime to be called later when a browser event fires! And if it moved its captures (`class 1`), you would allocate a closure per render frame. Passing a value `msg: M` and delivering the payload in `ev.text` (which the user can `parse<Payload>(ev.text)` with `std/json`!) obeys Law 1 (`§4.2`–`§4.3`) with zero new concepts.
   - **One convenience worth adding:** Make `props` in `react<P extends ToJson, M>(name: str, props: readonly P, msg: M)` accept any `T extends ToJson` and call `stringify(props)` inside `react`, rather than making callers manually `stringify` at every call site.

---

#### 4. [Typed Client `api.ts`] Three Mismatches Between `std/json` (`§7.5`) and Your TS Mapping (`Plan 5`)

Check how `std/json` (`§7.2`, `§7.5`) actually encodes Flyscript types vs. the mapping in `Plan 5`:

1. **`Option<Option<T>>` and missing fields (`§7.5`):**
   Look at `§7.5`:
   ```ts
   #None => comptime if (isOption(f.type)) { #None } else { throw #MissingField(f.name.toString()) },
   ```
   - For a record/struct field `referrer: Option<String>`, `FromJson` allows the key to be omitted (`referrer?: string | null` in TS), whereas `ToJson` emits `null` (or omits it). In `api.ts`, generating `field?: T | null` on input objects (or `T | null`) matches both `{ referrer: null }` and `{}`!
   - For `Option<Option<T>>`: since `Option<T>`'s handwritten `ToJson`/`FromJson` impl encodes `#None` as JSON `null` and `#Some(v)` as `v`, both `#None` and `#Some(#None)` encode to JSON `null`! That's an inherent property of untagged `null` for `Option` in `std/json`: in `api.ts` (or in `api.fly`'s compiler check), **reject `Option<Option<T>>` in `api.fly` signatures** with a clear diagnostic saying to use a named tag union (`#Present(Option<T>) | #Absent`).

2. **Tag unions / enums with 0, 1, or N tuple fields vs record fields (`§3.2`, `§7.2`, `§7.5`):**
   Look at `§7.2` and `§7.5`:
   > `type TagInfo = { name: str; payload: Option<Type> }; // the one type of #A(T), or the tuple or record`
   > `// … tuples, and tag unions as "Name" or { "Name": payload }`
   In `Plan 5`, you wrote:
   > *"tag unions/enums → unions of `"Name"` and `{ Name: payload }`"*
   Make sure `api.ts` matches `Type.info(T)`'s exact payload shape for all three tag forms (`§2.3`, `§3.2`):
   - `#Quit` (no payload / `void` payload): `"Quit"`
   - `#Id(u32)` (1-arg payload): `{ Id: number }`
   - `#Point(f64, f64)` (2+ tuple payload): `{ Point: [number, number] }`
   - `#User { id: u32; name: String }` (record payload): `{ User: { id: number; name: string } }`

3. **`Result<T, E>` and `Fail<E>` over `/_fly/rpc/Effect.op` (`§3.2`, `§5.1`, `§7.5`):**
   Look at `§5.1`:
   > *"Operations have no effects of their own. ... one that can fail returns a `Result`"*
   Since `Result<T, E>` is just the alias `#Ok(T) | #Err(E)` (`§3.2`), unless `Result` has a custom `ToJson`/`FromJson` impl, it is encoded by the union derivation as:
   - `{ Ok: T } | { Err: E }` — **except when `T` is `void`!**
   Look at `§3.2`:
   > *"and a tag without one is written bare — including where the payload type is `void`, so `#Ok` is the success of a `Result<void, E>`."*
   Check what `ToJson` emits for `Result<void, E>` (`#Ok | #Err(E)`):
   - Is `#Ok` in `Result<void, E>` encoded as `"Ok"` (a bare string, because its payload is `None`/`void`) or `{ "Ok": null }`?
   - In `Plan 5`, you wrote: `Result<T, E> → { Ok: T } | { Err: E }`. If `T` is `void` and `ToJson` encodes bare `#Ok` as `"Ok"`, then `{ Ok: void }` in `api.ts` will **not match** the runtime JSON `"Ok"`!
   - **Check `std/json`'s union arm for `void` payloads** and make sure `api.ts` generates `"Ok" | { Err: E }` (or `{ Ok: null } | { Err: E }`, whichever `std/json` actually emits and expects for `#Ok` in `Result<void, E>`!).

4. **64-bit integers (`i64`, `u64`, `isize`, `usize`, `i128`):**
   Look at `§3.1`:
   > *"`isize` and `usize` are as wide as the target's addresses: 64 bits natively, and 53 on JavaScript, whose numbers hold integers exactly to that width"*
   As long as timestamps (ms since epoch $\approx 1.7 \times 10^{12} \ll 2^{53} - 1$), counts, and DB IDs fit in 53 bits, mapping `i64`/`u64`/`usize`/`isize` to TS `number` in `api.ts` is completely fine and infinitely more ergonomic in TS than `bigint` (which `JSON.stringify` rejects!). Only reject `i128` in `api.fly` signatures (or map `HashMap<String, V>` to `Record<string, V>` if `std/json` supports it).

---

### Smaller points

- **Forwarding request cookies and `Host` on SSR:** If the Next.js page runs `getServerSideProps` or a React Server Component on `:3001` and calls `api.ts` during **SSR** (on the server, not in the browser), a relative `fetch("/_fly/rpc/...")` fails in Node.js (Node's `fetch` requires an absolute URL), and a server-side `fetch` won't automatically carry the browser's `Cookie` header unless passed or unless `api.ts` takes an optional `{ baseUrl?: string, headers?: HeadersInit }` (or reads `process.env.FLY_ORIGIN`). Supporting an optional `opts?: { headers?: HeadersInit; baseUrl?: string }` last parameter (or a small `createApiClient({ baseUrl, headers })` factory in `api.ts` alongside the default exports) makes calling `api.fly` from Next.js Server Components / Route Handlers work too.
- **`X-Forwarded-*` headers in `Plan 1`:** When adding `X-Forwarded-Host` and `X-Forwarded-Proto`, preserve any incoming `X-Forwarded-Proto` if FlyNext itself is behind TLS termination in production, and default to `http` otherwise; Next.js uses `X-Forwarded-Host` and `X-Forwarded-Proto` to construct canonical URLs and validate Server Action origins.
