"use client";
import { useState } from "react";
import Link from "next/link";
import type { Todo } from "../lib/store";
export default function TodoList({ initial }: { initial: Todo[] }) {
  const [todos, setTodos] = useState(initial);
  const [draft, setDraft] = useState("");
  const [error, setError] = useState("");
  const [adding, setAdding] = useState(false);
  const call = async (body: object) => {
    const r = await fetch("/api/todos", { method: "POST", body: JSON.stringify(body) });
    return r.json();
  };
  const add = async (e: React.FormEvent) => {
    e.preventDefault(); setError(""); setAdding(true);
    const r = await call({ op: "add", title: draft });
    setAdding(false);
    if (r.error) setError(r.error); else { setTodos(r.todos); setDraft(""); }
  };
  const left = todos.filter((t) => !t.done).length, done = todos.length - left;
  return (
    <>
      <h1>Things to do</h1>
      <form onSubmit={add}>
        <input placeholder="What needs doing?" value={draft} onChange={(e) => setDraft(e.target.value)} />
        <button type="submit" disabled={adding}>{adding ? "Adding…" : "Add"}</button>
      </form>
      {error && <p className="error">{error}</p>}
      <ul className="todos">
        {todos.map((t) => (
          <li key={t.id} className={t.done ? "done" : undefined}>
            <span className="check" onClick={async () => setTodos((await call({ op: "toggle", id: t.id })).todos)}>{t.done ? "✓" : ""}</span>
            <Link href={`/todos/${t.id}`} className="title">{t.title}</Link>
          </li>
        ))}
      </ul>
      <footer><span>{left} left</span>{done > 0 && <button className="quiet" onClick={async () => setTodos((await call({ op: "clearDone" })).todos)}>Clear {done} done</button>}</footer>
    </>
  );
}
