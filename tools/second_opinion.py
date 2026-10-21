#!/usr/bin/env python3
"""Ask Gemini 4 Argon (Vertex AI) for a second opinion on a Flyscript design decision.

    tools/second_opinion.py ask --topic m2-checker-design question.md [--context FILE ...] [--fresh]
    tools/second_opinion.py list

The reviewer instructions (tools/reviewer.md) and the spec (docs/spec.md) form a stable
prefix. Where the model supports Vertex explicit context caching, the prefix is held in a
cache keyed by its content hash; otherwise (as for gemini-4-argon) it is sent first in every
request, where Vertex's implicit caching can reuse it. Every exchange is saved under
docs/reviews/; asking the same question against the same spec and context returns the
saved answer instead of calling the model, and earlier reviews are sent as context so
feedback builds on itself.

Configuration: FLYSCRIPT_VERTEX_PROJECT (default: gcloud's core/project),
FLYSCRIPT_VERTEX_LOCATION (default: global), FLYSCRIPT_REVIEW_MODEL (default: gemini-4-argon).
Credentials come from `gcloud auth application-default print-access-token`.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REVIEWER = ROOT / "tools" / "reviewer.md"
SPEC = ROOT / "docs" / "spec.md"
REVIEWS = ROOT / "docs" / "reviews"
STATE = ROOT / ".second-opinion" / "cache.json"

MODEL = os.environ.get("FLYSCRIPT_REVIEW_MODEL", "gemini-4-argon")
LOCATION = os.environ.get("FLYSCRIPT_VERTEX_LOCATION", "global")
CACHE_TTL_SECONDS = 3600
# Earlier reviews are included newest first until this many characters.
HISTORY_BUDGET = 60_000


def sha(*parts: str) -> str:
    h = hashlib.sha256()
    for p in parts:
        h.update(p.encode())
        h.update(b"\0")
    return h.hexdigest()


def project() -> str:
    env = os.environ.get("FLYSCRIPT_VERTEX_PROJECT")
    if env:
        return env
    out = subprocess.run(["gcloud", "config", "get-value", "project"], capture_output=True, text=True)
    value = out.stdout.strip()
    if not value:
        sys.exit("set FLYSCRIPT_VERTEX_PROJECT or a gcloud default project")
    return value


def token() -> str:
    out = subprocess.run(
        ["gcloud", "auth", "application-default", "print-access-token"], capture_output=True, text=True
    )
    if out.returncode != 0:
        sys.exit("gcloud credentials expired: run `gcloud auth application-default login`\n" + out.stderr)
    return out.stdout.strip()


def host() -> str:
    return "aiplatform.googleapis.com" if LOCATION == "global" else f"{LOCATION}-aiplatform.googleapis.com"


def call(method: str, path: str, body: dict | None = None) -> dict:
    url = f"https://{host()}/v1/{path}"
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(url, data=data, method=method, headers={
        "Authorization": f"Bearer {token()}",
        "Content-Type": "application/json",
    })
    try:
        with urllib.request.urlopen(req, timeout=900) as resp:
            return json.load(resp)
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"{method} {path}: HTTP {e.code}: {e.read().decode()[:2000]}") from e


def model_path(proj: str) -> str:
    return f"projects/{proj}/locations/{LOCATION}/publishers/google/models/{MODEL}"


def prefix() -> tuple[str, str]:
    """The cached prefix: reviewer instructions (system) and the spec (first user turn)."""
    return REVIEWER.read_text(), "# The Flyscript specification\n\n" + SPEC.read_text()


def load_state() -> dict:
    return json.loads(STATE.read_text()) if STATE.exists() else {}


def save_state(state: dict) -> None:
    STATE.parent.mkdir(exist_ok=True)
    STATE.write_text(json.dumps(state, indent=2))


def context_cache(proj: str, system: str, spec: str) -> str | None:
    """Name of a live explicit cache holding the prefix, creating one if needed.

    Returns None when caching is unavailable; the caller then sends the prefix inline.
    """
    key = sha(MODEL, system, spec)
    state = load_state()
    if MODEL in state.get("no_explicit_cache", []):
        return None
    entry = state.get("context_cache")
    now = datetime.datetime.now(datetime.timezone.utc)
    if entry and entry["key"] == key and datetime.datetime.fromisoformat(entry["expires"]) > now + datetime.timedelta(minutes=5):
        return entry["name"]
    try:
        created = call("POST", f"projects/{proj}/locations/{LOCATION}/cachedContents", {
            "model": model_path(proj),
            "displayName": f"flyscript-spec-{key[:12]}",
            "systemInstruction": {"parts": [{"text": system}]},
            "contents": [{"role": "user", "parts": [{"text": spec}]}],
            "ttl": f"{CACHE_TTL_SECONDS}s",
        })
    except RuntimeError as e:
        if "does not support explicit context caching" in str(e):
            # Remember, so later calls skip straight to the inline prefix; Vertex's implicit
            # caching still applies because the prefix (instructions, then spec) is stable.
            state.setdefault("no_explicit_cache", []).append(MODEL)
            save_state(state)
        print(f"note: explicit context cache unavailable, sending the spec inline ({e})", file=sys.stderr)
        return None
    state["context_cache"] = {"key": key, "name": created["name"], "expires": created["expireTime"].replace("Z", "+00:00")}
    save_state(state)
    return created["name"]


def review_files() -> list[Path]:
    return sorted(REVIEWS.glob("*.md"), reverse=True) if REVIEWS.exists() else []


def history(exclude: Path | None) -> str:
    out, used = [], 0
    for f in review_files():
        if f == exclude:
            continue
        text = f.read_text()
        if used + len(text) > HISTORY_BUDGET:
            break
        out.append(text)
        used += len(text)
    if not out:
        return ""
    return "# Earlier review exchanges (newest first)\n\n" + "\n\n---\n\n".join(out)


def ask(args: argparse.Namespace) -> None:
    question = Path(args.question).read_text() if Path(args.question).exists() else args.question
    context = ""
    for f in args.context or []:
        context += f"\n\n# Context: {f}\n\n```\n{Path(f).read_text()}\n```"
    system, spec = prefix()
    spec_hash = sha(spec)[:12]
    request_key = sha(MODEL, system, spec, question, context)[:16]

    REVIEWS.mkdir(parents=True, exist_ok=True)
    for f in review_files():
        if f"request: {request_key}" in f.read_text() and not args.fresh:
            print(f"(saved answer: {f.relative_to(ROOT)})\n", file=sys.stderr)
            print(f.read_text())
            return

    proj = project()
    cache = context_cache(proj, system, spec)
    turn = "\n\n".join(p for p in [history(None), context, "# Question\n\n" + question] if p)
    body: dict = {
        "contents": [{"role": "user", "parts": [{"text": turn}]}],
        "generationConfig": {"maxOutputTokens": 32768, "temperature": 1.0},
    }
    if cache:
        body["cachedContent"] = cache
    else:
        body["systemInstruction"] = {"parts": [{"text": system}]}
        body["contents"].insert(0, {"role": "user", "parts": [{"text": spec}]})
        body["contents"].insert(1, {"role": "model", "parts": [{"text": "I have read the specification."}]})

    resp = call("POST", f"{model_path(proj)}:generateContent", body)
    parts = resp["candidates"][0]["content"]["parts"]
    answer = "".join(p.get("text", "") for p in parts if not p.get("thought"))
    usage = resp.get("usageMetadata", {})

    date = datetime.date.today().isoformat()
    slug = re.sub(r"[^a-z0-9]+", "-", args.topic.lower()).strip("-")
    path = REVIEWS / f"{date}-{slug}.md"
    n = 2
    while path.exists():
        path = REVIEWS / f"{date}-{slug}-{n}.md"
        n += 1
    path.write_text(
        f"# Review: {args.topic}\n\n"
        f"- spec: {spec_hash}\n"
        f"- request: {request_key}\n"
        f"- tokens: prompt {usage.get('promptTokenCount')}, cached {usage.get('cachedContentTokenCount', 0)}, "
        f"answer {usage.get('candidatesTokenCount')}\n\n"
        f"## Question\n\n{question.strip()}\n"
        + (f"\n## Context files\n\n" + "\n".join(f"- `{c}`" for c in args.context) + "\n" if args.context else "")
        + f"\n## Answer\n\n{answer.strip()}\n"
    )
    print(f"(saved to {path.relative_to(ROOT)}; tokens: {usage})\n", file=sys.stderr)
    print(answer)


def list_reviews(_: argparse.Namespace) -> None:
    for f in review_files():
        print(f.relative_to(ROOT), "-", f.read_text().splitlines()[0].removeprefix("# Review: "))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(required=True)
    a = sub.add_parser("ask", help="ask for a second opinion")
    a.add_argument("question", help="a question, or a file containing one")
    a.add_argument("--topic", required=True, help="short name, used for the saved review's file name")
    a.add_argument("--context", nargs="*", help="extra files to include (code, drafts)")
    a.add_argument("--fresh", action="store_true", help="ask again even if a saved answer exists")
    a.set_defaults(func=ask)
    sub.add_parser("list", help="list saved reviews").set_defaults(func=list_reviews)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
