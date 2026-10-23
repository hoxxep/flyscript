import Link from "next/link";
import { notFound } from "next/navigation";
import { store } from "../../../lib/store";
export const dynamic = "force-dynamic";
export async function generateMetadata({ params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const t = store.todos.find((x) => x.id === Number(id));
  if (!t) return {};
  return { title: t.title, description: `${t.done ? "Done" : "To do"}: ${t.title}` };
}
export default async function Item({ params }: { params: Promise<{ id: string }> }) {
  const { id } = await params;
  const t = store.todos.find((x) => x.id === Number(id));
  if (!t) notFound();
  return (
    <>
      <Link href="/" className="back">← All things to do</Link>
      <h1>{t.title}</h1>
      <p className={t.done ? "status done" : "status"}><span className="check">{t.done ? "✓" : ""}</span>{t.done ? "Done" : "Not done yet"}</p>
    </>
  );
}
