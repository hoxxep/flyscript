import Link from "next/link";
import { Board } from "./board";

// A page of the Next.js app's: it calls the FlyNext app's server through `api.ts`, shows one of its
// islands, and links to one of its pages.
export default function Home() {
  return (
    <main>
      <h1>Notes, in Next.js</h1>
      <Board />
      <p>
        <Link href="/fly" className="to-fly">The same notes, in Flyscript</Link>
      </p>
    </main>
  );
}
