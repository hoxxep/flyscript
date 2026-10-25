// The React components the FlyNext app's pages show (`<React name="Stars" … />`), registered with
// the page's program, which mounts each where a view puts it. Built into app/public/widgets.js.

import { createElement } from "react";
import { createRoot } from "react-dom/client";
// @ts-expect-error: the page's program, served by the FlyNext server.
import { registerReact } from "/_fly/flynext.js";

function Stars({ count, emit }: { count: number; emit: (v: string) => void }) {
  return (
    <span className="stars">
      {[1, 2, 3, 4, 5].map((i) => (
        <button key={i} data-star={i} onClick={() => emit(String(i))}>
          {i <= count ? "★" : "☆"}
        </button>
      ))}
    </span>
  );
}

registerReact({ createRoot, createElement }, { Stars });
