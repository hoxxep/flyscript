import { NextResponse } from "next/server";

// Signs in: the session cookie, which the FlyNext app's server reads too.
export function GET(request: Request) {
  const res = NextResponse.redirect(new URL("/", request.url));
  res.cookies.set("session", "alice", { path: "/", httpOnly: true, sameSite: "lax" });
  return res;
}
