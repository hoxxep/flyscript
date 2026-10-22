export type Todo = { id: number; title: string; done: boolean };
const g = globalThis as unknown as { store?: { todos: Todo[]; next: number } };
export const store = (g.store ??= {
  todos: [
    { id: 1, title: "Write the language", done: true },
    { id: 2, title: "Compile it to WebAssembly", done: true },
    { id: 3, title: "Render pages on the server and take them over in the browser", done: false },
  ],
  next: 4,
});
