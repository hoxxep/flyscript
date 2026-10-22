import "./globals.css";
import Link from "next/link";
export const metadata = { title: "Things to do" };
export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en"><body><main>
      <nav><span className="brand">Next.js</span><Link href="/" className="here">Things to do</Link><Link href="/about">About</Link></nav>
      {children}
    </main></body></html>
  );
}
