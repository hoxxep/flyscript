# A web framework, in Flyscript

The parts a site is built from, all library code, which [examples/todo](../examples/todo/) puts together.

| | |
| :--- | :--- |
| `ui.fly` | `Ui<M>`, the effect a view performs: elements opened and closed, their keys, attributes and events, and text. `html` renders a view as HTML. |
| `page.fly` | A page as the server sends it: the view rendered, the state the page's program starts from, and the program. |
| `dom.fly` | The browser's side of `Ui`, in WebAssembly: a render recorded as the flat list of the view's operations and diffed against the last, keyed children matched by key; the first render adopting the server's DOM; and `run`, which waits for an event, gives its message to `update`, and renders again. |
| `flynext.js` | The page's host for a program compiled to WebAssembly: WASI as far as a page can, fibers and waiting by JavaScript promise integration, and the DOM, events and the server, through imports. |
| `http.fly` | HTTP/1.1 over `std/net`: requests with keep-alive and pipelining, whole or chunked responses, and `serve`, which runs each connection in a task of its own. |

Nothing here is known to the compiler. An event's handler is a message, not a closure, so a render keeps no code of the view's; what an input says comes to `update` with the message, as an `Event`. Waiting for the next event, and for the server, suspends the page's program until the page has the answer, so it is an ordinary loop with no state outside it.
