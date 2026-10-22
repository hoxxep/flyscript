# A site in Flyscript

A list of things to do, as one Flyscript program: a server compiled to native code and, for each page, a program compiled to WebAssembly that takes over the page the server rendered.

```sh
examples/todo/build.sh          # the server, and build/_fly/index.wasm and about.wasm
examples/todo/build/server 8080 examples/todo/build
```

Then open <http://localhost:8080>.

## How it is put together

| | |
| :--- | :--- |
| `app/api.fly` | `Todos`, the effect the pages perform to ask the server for the list and to change it. |
| `app/store.fly` | The server's handler of `Todos`: the list in a `Mutex`, which every connection's task shares. |
| `app/client.fly` | The page's handler of `Todos`: each operation posts its arguments to the server as JSON, and gives what it answers. |
| `app/rpc.fly` | The server's side of those posts: the operation performed under the server's handler, its result as JSON. |
| `app/routes/` | The pages: each a model, a view that performs `Ui`, and an update from the view's messages. |
| `client/` | Each page's program: the state the server rendered the page with, then `run` (web/dom.fly). |
| `server.fly` | The server: pages rendered from the store, the pages' calls answered, the files pages load. |

A view is the same code on both sides. The server handles `Ui` by writing HTML, and embeds the model the page was rendered with; the page's program reads that model, renders the view again, and adopts the nodes the server made, if they are what it shows. From then on each event gives the program a message, `update` changes the model — asking the server where it performs `Todos` — and the view is rendered again, the DOM changed only where the new render differs. A failure the server answers with, such as an empty title, is raised where the page asked, as if the call were local.

`e2e.js` drives the site in a browser with Playwright: `NODE_PATH=…/node_modules node e2e.js <port>`, against a fresh server.
