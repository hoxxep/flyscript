# A site in Flyscript

A list of things to do, as one FlyNext app ([web](../../web/)): a server compiled to native code, which renders each page from its store, and a WebAssembly program, which takes over the page the server rendered and from then on renders the pages links lead to itself, each page's own code a module it loads the first time the page is shown.

```sh
web/flynext dev examples/todo/app 8080
```

Then open <http://localhost:8080>.

## How it is put together

| | |
| :--- | :--- |
| `app/api.fly` | `Todos`, the effect the pages perform to ask the server for the list and to change it. |
| `app/server.fly` | The server's handler of `Todos`: the list in a `Mutex`, which every connection's task shares. |
| `app/routes/layout.fly` | The navigation every page shows, marking where it is. |
| `app/routes/index.fly` | The list: added to, its items marked done, its titles links to their pages. |
| `app/routes/todos/[id].fly` | One thing to do: renamed, marked done, or removed, which goes back to the list. |
| `app/routes/about.fly` | A page with a model of its own, a component in it, and a timer. |
| `app/routes/progress.fly` | A page the server keeps and answers every request with, until a change to the list revalidates it. |
| `app/routes/report.fly` | A page streamed: the list at once, and a summary that is slow to work out, by `later`, in its place once it is. |
| `app/routes/visits.fly` | A page whose `load` reads a cookie and sets it again: one that may be kept, but is each request's own. |
| `app/routes/old.fly` | An address the site no longer uses, whose `load` sends the browser to the page that took its place. |
| `app/routes/api/todos.fly` | An endpoint: the list as JSON. |
| `app/components/counter.fly` | The component: a model, a view and an update, as a page is. |
| `app/routes/404.fly` | What an address nothing answers shows. |

A view is the same code on both sides. The server handles `Ui` by writing HTML, and embeds the model the page was rendered with; the page's program reads that model, renders the view again, and adopts the nodes the server made, if they are what it shows. From then on each event gives the program a message, `update` changes the model — asking the server where it performs `Todos` — and the view is rendered again, the DOM changed only where the new render differs. A link asks the server for the next page's model, and the program renders that page in place. A failure the server answers with, such as an empty title, is raised where the page asked, as if the call were local.

`e2e.js` drives the site in a browser with Playwright: `NODE_PATH=…/node_modules node e2e.js <port>`, against a fresh server.
