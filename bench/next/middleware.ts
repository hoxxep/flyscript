import { NextResponse, type NextRequest } from "next/server";

// As the FlyNext app's middleware.fly: the list's own address sends a reader home, and a link that
// says where it was shared, `?from=…`, is remembered for the day.
export function middleware(req: NextRequest) {
  const { pathname, searchParams } = req.nextUrl;
  if (pathname === "/todos" || pathname === "/todos/") return NextResponse.redirect(new URL("/", req.url), 303);
  const res = NextResponse.next();
  const from = searchParams.get("from");
  if (from) res.cookies.set("from", from, { path: "/", httpOnly: true, sameSite: "lax", maxAge: 86400 });
  return res;
}

export const config = { matcher: ["/((?!_next/).*)"] };
