"use client";
import { useEffect, useState } from "react";
export default function Live() {
  const [n, setN] = useState(0);
  const [seconds, setSeconds] = useState(0);
  useEffect(() => { const t = setInterval(() => setSeconds((s) => s + 1), 1000); return () => clearInterval(t); }, []);
  return (
    <>
      <p>A component is a view, a model and an update, like a page&apos;s:</p>
      <span className="counter"><button onClick={() => setN(n - 1)}>−</button><output>{n}</output><button onClick={() => setN(n + 1)}>+</button></span>
      <p className="open">Open for {seconds} s.</p>
    </>
  );
}
