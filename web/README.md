# FlyNext: a web framework, in Flyscript

What Next.js and React are for a JavaScript site, in one Flyscript app: pages rendered on the server and taken over in the browser, streamed where part of a page is slow, or kept and revalidated where it is the same for everyone, routes from files, layouts, data loaded on the server with the request's headers and cookies, titles and descriptions for search engines and link previews, middleware, redirects, endpoints, server functions called from the page as if they were local, links followed without loading a page, timers, and forms that work before the page's program has loaded, or without it. The server is native code; the browser runs WebAssembly: a core every page shares, and each page's own code a module of its own, which it downloads with the page, or as a link to the page is pointed at, and links into the program the first time the page is shown. [examples/todo](../examples/todo/) is an app built with it.

```sh
web/flynext dev app            # serves the app on :3000, rebuilding and reloading pages as it changes
web/flynext build app out      # the server, natively, and the pages' program, as WebAssembly
web/flynext start out 3000     # serves a build
```

## An app

```
app/
  routes/            the pages: each file one, its place its address
    layout.fly       what every page shows around itself
    index.fly        /
    about.fly        /about
    todos/[id].fly   /todos/7, with the parameter `id`
    docs/[...path].fly  /docs/a/b, `path` "a/b": one segment or more; `[[...path]]` none too
    (shop)/cart.fly  /cart: a directory in parentheses groups pages under a layout of its own
    api/todos.fly    an endpoint: it answers /api/todos itself
    404.fly          what an address nothing answers shows
    error.fly        what a page whose `load` failed shows
    loading.fly      what shows while a followed link waits for the next page
  middleware.fly     what runs before every page, endpoint and call
  api.fly            the effects the pages ask the server for
  server.fly         how the server answers them
  public/            files served as they are
  head.html          what every page's <head> holds, if not the stylesheet /style.css
```

**A page** exports its `Model` and `Msg` types, a `view` that performs `Ui<Msg>`, and how its model is made: `load`, which the server runs — given the address's `Params`, performing the app's effects, and failing with `#NotFound` for an address it has nothing for, which is then the 404 page, and with anything else for a page that failed, which is then the error page, with the status 500 — or `initial`, which needs nothing. A page made by `initial` at an address with no parameters is the same for every request: the server renders it once, as it starts, and answers with that. It may export an `update`, which changes the model for each message its view gives, and a `title` and a `description`, each a constant or a function of the model: the description goes in the page's head as what a search engine or a link preview shows (`description`, `og:description`, with the title as `og:title`), and following a link changes both, as it changes the title.

**A page with something slow to show** exports `later`, which makes the rest of its model once `load` has made what is quick: `export function later(m: mut Model): void uses Todos { … }`, given the address's `Params` too if it asks for them. The server sends the page as `load` left it at once — its view showing what is still to come as it likes, a field of the model `#None`, say — and then, in the same answer, the page as it is once `later` has filled the model in, which takes the first's place before the page's program takes it over: what React's `Suspense` does on the server, with one model and one view rather than boundaries of their own. Following a link, the program asks for the page whole, and shows `loading.fly`'s view meanwhile. By the time `later` runs the answer's headers are gone, so it cannot fail — what went wrong is for its model to say — nor set a cookie, which panics; if it performs `Http.redirect`, the browser goes there.

```ts
export type Model = { todos: Vec<Todo>; summary: Option<String> };
export function load(): Model uses Todos { { todos: Todos.list(), summary: #None } }
export function later(m: mut Model): void uses Io { m.summary = #Some(summarize(m.todos)); }
```

**A page kept for a while** exports `revalidate`, a number of seconds: `export const revalidate: u64 = 3600;`. The server renders it at an address once and answers every request for the address with that render, as HTML or as the page's data, until the seconds have passed, and tells shared caches they may keep it as long (`s-maxage`); `X-Fly-Cache` says whether an answer was kept (`HIT`) or rendered (`MISS`). Which pages are the same for every request needs no guessing: a page is the request's own exactly when its `load` performs `Http` to read the request — a header or a cookie — or sets a cookie, and then the server renders it for each request as it does a page that does not export `revalidate`. `Http.revalidate(path)` drops what is kept for `path`, so a change the server makes — in a handler of the app's effects, say — is shown at once:

```ts
add(title) resumes k => {
  const r = db.lock((s) => addTo(mut s, title));
  Http.revalidate("/progress");
  k(r)
}
```

```ts
export type Model = { todo: Todo; draft: String };
export type Msg = #Draft | #Rename;

export function title(m: readonly Model): String { m.todo.title.clone() }
export function description(m: readonly Model): String { `To do: ${m.todo.title}` }

export function load(p: readonly Params): Model uses Todos, Fail<#NotFound> { … }

export function view(m: readonly Model): void uses Ui<Msg> {
  link("/", () => text("← All things to do"));
  el("h1", () => text(m.todo.title.asStr()));
  el("form", () => { on("submit", #Rename); el("input", () => { attr("value", m.draft.asStr()); on("input", #Draft); }); });
}

export function update(m: mut Model, msg: Msg, ev: readonly Event): void uses Todos, Page<Model> { … }
```

**An endpoint** is a route file that exports `handle(req: readonly Request, p: readonly Params): Response`, performing what the app's server handles, rather than a view: it answers any request for its address itself, with JSON, say.

**The request** is an effect too, `Http` (`request.fly`), which the server handles around a page's `load`, an endpoint's `handle`, and its own handlers of the app's effects: `Http.header(name)` and `Http.cookie(name)` read the request, `Http.setCookie(name, value, maxAge)` sets a cookie on the answer, its value percent-encoded where a cookie may not hold a byte (and `Http.cookie` decodes it), `Http.redirect(url)` answers instead by sending the browser to `url` — from a `load`, the page there is shown in its place, whether the browser asked for the page or the program followed a link to it — and `Http.revalidate(path)` drops the page kept for `path`.

**What shows when nothing else does**: `404.fly` and `error.fly` export a `Model`, an `initial` that makes it, and a `view`, shown inside the outermost layout; `loading.fly` exports a `view` of nothing.

**Middleware**, `middleware.fly`, exports `middleware(url: str): void`, which the server runs with the request's address, its query too, before any page, endpoint or call answers, under the same handlers as a page's `load`. Performing `Http`, it may read the request's headers and cookies, set cookies, which go with whatever answers, even a public file, or send the browser elsewhere with `Http.redirect(url)`, and then nothing else answers.

**A layout** wraps the pages of its directory and those below it, given the page's address: `export function layout<M>(path: str, body: () => void uses Ui<M>): void uses Ui<M>`. Layouts nest, the outermost first.

**What pages ask of the server** is an effect, declared in `api.fly`. On the server, `server.fly`'s `provide` handles it, around the page's `load` and around each call; `init` makes the state it shares, once. In the browser the app compiler makes a handler of the same effect that calls the server, its arguments and results as JSON, and a failure the server answers with is raised where the page asked. So a page's code is the same on both sides, and calling the server is calling the effect.

**Links** are ordinary `<a>` elements (`link(href, body)`). Followed within the site, the program shows `loading.fly`'s view inside the outermost layout, if the app has one, asks the server for the next page's data, renders it in place, and moves the history on; what both pages show alike, a layout, is left as it is. The data of a page a link points at is asked for as soon as the pointer is over it. Back and forward render the pages again the same way. Without the program, a link is a link.

**Components** are a model, a view and an update, as a page is. A page shows one by `map`, which makes the component's messages the page's: `map((c) => #Counter(c), () => counter.view(m.counter))`.

**Timers** are events of an element: `every(ms, msg)` gives the page a message every `ms` milliseconds for as long as the element is shown, and `after(ms, msg)` once.

**Without the page's program** — before it has loaded, or in a browser that runs no scripts — a page still works: a form posts to its page, a button with a click's message posts that, and the server makes the page's model as it would to show it, gives its `update` each input's message with what the form posted for it and then the form's message, as the program would have, its effects handled on the server, and sends the browser where the update went, or back to the page. The page's attributes say what posts what, the same in the server's HTML and the program's render.

**An update** may perform `Page.show(m)` to render the model as it is so far, before something slow — the button says "Adding…" while the server answers — and `Page.go(url)` to go to another page when it is done.

## How it is put together

| | |
| :--- | :--- |
| `ui.fly` | `Ui<M>`, the effect a view performs: elements opened and closed, their keys, attributes and events, and text; `link`, `map`, `every`, `after`; `html`, which renders a view as HTML; what posts an event's message without the program. |
| `request.fly` | `Http`, the effect of the request being answered: its headers and cookies, cookies set, redirects. |
| `dom.fly` | The browser's side of `Ui`, in WebAssembly: a render recorded as the flat list of the view's operations and diffed against the last, keyed children matched by key — across pages too; the first render taking over the server's DOM; and `run`, which waits for an event, gives its message to `update`, and renders again, until a link leads elsewhere. |
| `router.fly` | Routes: patterns from files, matched against addresses, with their parameters and the query. |
| `site.fly` | What every site's server does: a page answered whole to a browser, or as its data to the program; pages streamed, and pages kept for a while; `Http` handled from the request; a form posted without the program, replayed through the page's update; the site's files; the build a page in development watches. |
| `flynext.fly` | The app compiler: it reads the app's pages, layouts and effects, with the compiler's own parser, and writes the server and the program. |
| `flynext` | The command that builds, serves, and rebuilds in development. |
| `flynext.js` | The page's host for the program: WASI as far as a page can, waiting by JavaScript promise integration, the DOM, events, links and the history, the server, and each page's module, linked into the program as WebAssembly's dynamic linking lays it out: its memory and its part of the table of functions given it, and what it takes of the core found among the core's exports. |
| `http.fly` | HTTP/1.1 over `std/net`: requests with keep-alive and pipelining, whole or chunked responses, and `serve`, which runs each connection in a task of its own. |

Nothing here is known to the language. An event's handler is a message, not a closure, so a render keeps no code of the view's; waiting for the next event, and for the server, suspends the page's program until the page has the answer, so a page runs as an ordinary loop with no state outside it. An app imports the framework as the package `web`.
