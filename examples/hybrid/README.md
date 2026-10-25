# A Next.js app, replaced a route at a time

A Next.js app (`next/`) and a FlyNext app (`app/`) serving one site: the FlyNext server is in front, answering its own routes and forwarding every other request to the Next.js app, so the two share an origin, its cookies and its links, and moving a page across is moving one file.

```sh
cd examples/hybrid/next && pnpm install && cd ..
sh build.sh             # the FlyNext app, what the Next.js app uses of it, and the Next.js app
sh run.sh 3000          # the FlyNext server on :3000, in front of the Next.js app on :3001
```

Then open <http://localhost:3000/login>, which signs in, and follow the link to the page in Flyscript.

| | |
| :--- | :--- |
| `app/api.fly` | `Notes`, the effect both apps ask the server for: the notes, and who the session cookie says is signed in. |
| `app/server.fly` | How the FlyNext server answers it. |
| `app/routes/fly.flyx` | A page of the FlyNext app's, at `/fly`, which shows a React component of the page's (`<React name="Stars" … />`). |
| `app/islands/counter.flyx` | An island: a FlyNext component a Next.js page shows, run there by a program of its own. |
| `widgets/widgets.tsx` | The React components the FlyNext app's pages show, registered with the page's program. |
| `next/app/board.tsx` | A Next.js component that calls `Notes` through the generated `api.ts`, its types checked, and shows the island with `<FlyIsland>`. |
| `next/app/login/route.ts` | A Next.js route handler that sets the session cookie, which the FlyNext app reads too. |
| `e2e.js` | Drives the site in a browser with Playwright: `NODE_PATH=…/node_modules node e2e.js 3000`. |

The FlyNext build writes `api.ts` and `FlyIsland.tsx` into `app/.flynext/next`, which `build.sh` copies into `next/fly`: the Next.js app's typed client for `api.fly`'s effects, and the component that shows an island. A link from a Next.js page to a FlyNext route is loaded as a page, which the FlyNext server answers; a link from a FlyNext page to a route of the Next.js app's is too, the page's program following only links to its own routes.
