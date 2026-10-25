export const metadata = { title: "A Next.js app, a route at a time Flyscript" };

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
