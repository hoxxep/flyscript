import { store } from "../lib/store";
import TodoList from "./TodoList";
export const dynamic = "force-dynamic";
export const metadata = {
  title: "Things to do",
  description: "A list of things to do, kept on the server and changed in place.",
};
export default function Page() {
  return <TodoList initial={store.todos} />;
}
