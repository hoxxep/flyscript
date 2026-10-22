import { store } from "../../../lib/store";
export async function GET() { return Response.json(store.todos); }
export async function POST(req: Request) {
  const b = await req.json();
  if (b.op === "add") {
    const t = String(b.title ?? "").trim();
    if (!t) return Response.json({ error: "Write something to do first." });
    store.todos.push({ id: store.next++, title: t, done: false });
  } else if (b.op === "toggle") {
    for (const t of store.todos) if (t.id === b.id) t.done = !t.done;
  } else if (b.op === "clearDone") {
    store.todos = store.todos.filter((t) => !t.done);
  }
  return Response.json({ todos: store.todos });
}
