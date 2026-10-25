"use client";

import { useEffect, useState } from "react";
import { Notes, type Note } from "../fly/api";
import { FlyIsland } from "../fly/FlyIsland";

// The notes, asked of the FlyNext server through `api.ts`, its types checked; a note added; and the
// counter, an island of the FlyNext app's, which runs its own program here.
export function Board() {
  const [who, setWho] = useState<string | null>(null);
  const [notes, setNotes] = useState<Note[]>([]);
  const [error, setError] = useState("");
  useEffect(() => {
    Notes.whoami().then(setWho);
    Notes.list().then(setNotes);
  }, []);
  async function add(text: string) {
    const r = await Notes.add(text);
    if ("Ok" in r) setNotes(r.Ok);
    else setError(r.Err === "Empty" ? "Write something first." : `At most ${r.Err.TooLong} characters.`);
  }
  return (
    <section>
      <p className="who">{who === null ? "Signed in as no one" : `Signed in as ${who}`}</p>
      <ul className="notes">
        {notes.map((n) => (
          <li key={n.id}>{n.text}</li>
        ))}
      </ul>
      <button className="add" onClick={() => add("Written in Next.js")}>Add a note</button>
      <button className="add-empty" onClick={() => add(" ")}>Add an empty note</button>
      {error && <p className="error">{error}</p>}
      <FlyIsland name="counter" model={{ n: 5, saved: 0 }} className="counter" />
    </section>
  );
}
