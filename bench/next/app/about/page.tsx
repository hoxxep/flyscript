import Link from "next/link";
import Live from "./Live";
export const metadata = { title: "About" };
export default function About() {
  return (
    <>
      <h1>About</h1>
      <p>This site is one Flyscript app: a server compiled to native code, which renders each page and answers what pages ask of it, and one WebAssembly program, which takes over the page the server rendered and from then on renders the pages a link leads to itself.</p>
      <p>Its views are functions that perform <code>Ui</code>: the server handles it by writing HTML, the page by changing the DOM. What pages ask of the server is an effect too, <code>Todos</code>, which the server handles against its store and the page by asking the server.</p>
      <Live />
      <p>This page was at <Link href="/old">an older address</Link>, which sends you here.</p>
    </>
  );
}
