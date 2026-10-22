import { store } from "../lib/store";
import TodoList from "./TodoList";
export const dynamic = "force-dynamic";
export default function Page() {
  return <TodoList initial={store.todos} />;
}
