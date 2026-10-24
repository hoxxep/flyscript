#!/usr/bin/env python3
"""Writes the tables of std/unicode.fly from the Unicode Character Database.

    python3 tools/unicode.py UCD_DIR

UCD_DIR holds the files of one version of the database, as https://www.unicode.org/Public/UCD/latest/
has them: UnicodeData.txt, SpecialCasing.txt, DerivedNormalizationProps.txt, DerivedCoreProperties.txt,
GraphemeBreakProperty.txt (auxiliary/) and emoji-data.txt (emoji/). The tables replace everything
in std/unicode.fly after the line that starts them, so the code above it is left as written.
"""

import os
import re
import sys

MARK = "// ---- tables, written by tools/unicode.py from the Unicode Character Database"
MAX = 0x110000


def rows(path):
    """Each line's fields, `#` comments and blank lines left out."""
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if line:
                yield [x.strip() for x in line.split(";")]


def span(field):
    """A code point or a range `A..B`, as the range of code points."""
    if ".." in field:
        a, b = field.split("..")
        return range(int(a, 16), int(b, 16) + 1)
    return range(int(field, 16), int(field, 16) + 1)


def version(ucd):
    with open(os.path.join(ucd, "DerivedCoreProperties.txt"), encoding="utf-8") as f:
        m = re.search(r"DerivedCoreProperties-(\d+\.\d+\.\d+)", f.readline())
        return m.group(1)


def runs(value):
    """A property as the code points each run of equal values starts at, and the runs' values."""
    starts, values = [0], [value[0]]
    for cp in range(1, MAX):
        if value[cp] != values[-1]:
            starts.append(cp)
            values.append(value[cp])
    return starts, values


def table(name, ty, items, per_line=12):
    lines = []
    for i in range(0, len(items), per_line):
        lines.append("  " + ", ".join(str(x) for x in items[i:i + per_line]) + ",")
    body = "\n".join(lines)
    return f"const {name}: {ty}[] = [\n{body}\n];\n"


def mapping(name, m):
    """A mapping from code points to sequences of them: the code points, sorted, where each one's
    sequence starts in the flat list of every sequence, and that list."""
    cps = sorted(m)
    at, to = [], []
    for cp in cps:
        at.append(len(to))
        to.extend(m[cp])
    at.append(len(to))
    return table(f"{name}_CP", "u32", cps) + table(f"{name}_AT", "u32", at) + table(f"{name}_TO", "u32", to)


def main(ucd):
    data = list(rows(os.path.join(ucd, "UnicodeData.txt")))
    # UnicodeData lists a range by its first and last code points.
    ccc = [0] * MAX
    decomp, upper, lower = {}, {}, {}
    i = 0
    while i < len(data):
        f = data[i]
        cps = [int(f[0], 16)]
        if f[1].endswith("First>"):
            cps = range(int(f[0], 16), int(data[i + 1][0], 16) + 1)
            i += 1
        for cp in cps:
            ccc[cp] = int(f[3])
            if f[5] and not f[5].startswith("<"):
                decomp[cp] = [int(x, 16) for x in f[5].split()]
            if f[12]:
                upper[cp] = [int(f[12], 16)]
            if f[13]:
                lower[cp] = [int(f[13], 16)]
        i += 1
    # Full case mappings, where they are unconditional, take the simple ones' place.
    for f in rows(os.path.join(ucd, "SpecialCasing.txt")):
        if len(f) > 4 and f[4]:
            continue
        cp = int(f[0], 16)
        lower[cp] = [int(x, 16) for x in f[1].split()]
        upper[cp] = [int(x, 16) for x in f[3].split()]

    # Decompositions, applied in full, as NFD does.
    def full(cp):
        if cp not in decomp:
            return [cp]
        out = []
        for x in decomp[cp]:
            out.extend(full(x))
        return out
    canonical = {cp: full(cp) for cp in decomp}
    exclusions = set()
    for f in rows(os.path.join(ucd, "DerivedNormalizationProps.txt")):
        if f[1] == "Full_Composition_Exclusion":
            exclusions.update(span(f[0]))
    compose = {}
    for cp, d in decomp.items():
        if len(d) == 2 and cp not in exclusions:
            compose[(d[0] << 21) | d[1]] = cp

    # Grapheme clusters: the break property, and the two others its rules ask about.
    codes = {"Other": 0, "CR": 1, "LF": 2, "Control": 3, "Extend": 4, "ZWJ": 5, "Regional_Indicator": 6, "Prepend": 7,
             "SpacingMark": 8, "L": 9, "V": 10, "T": 11, "LV": 12, "LVT": 13}
    grapheme = [0] * MAX
    for f in rows(os.path.join(ucd, "GraphemeBreakProperty.txt")):
        for cp in span(f[0]):
            grapheme[cp] = codes[f[1]]
    for f in rows(os.path.join(ucd, "emoji-data.txt")):
        if f[1] == "Extended_Pictographic":
            for cp in span(f[0]):
                grapheme[cp] |= 16
    incb = {"Linker": 32, "Consonant": 64, "Extend": 128}
    case = [0] * MAX
    for f in rows(os.path.join(ucd, "DerivedCoreProperties.txt")):
        if f[1] == "InCB":
            for cp in span(f[0]):
                grapheme[cp] |= incb[f[2]]
        elif f[1] == "Cased":
            for cp in span(f[0]):
                case[cp] |= 1
        elif f[1] == "Case_Ignorable":
            for cp in span(f[0]):
                case[cp] |= 2

    g_at, g_is = runs(grapheme)
    c_at, c_is = runs(ccc)
    k_at, k_is = runs(case)
    keys = sorted(compose)
    out = [
        f"{MARK} {version(ucd)}: rerun it for another.\n",
        f'const VERSION: str = "{version(ucd)}";\n',
        "// Grapheme_Cluster_Break as `kind & 15` (`Other`, `CR`, `LF`, `Control`, `Extend`, `ZWJ`, `Regional_Indicator`,\n"
        "// `Prepend`, `SpacingMark`, `L`, `V`, `T`, `LV`, `LVT`), `16` for Extended_Pictographic, and Indic_Conjunct_Break\n"
        "// as `32` `Linker`, `64` `Consonant`, `128` `Extend`: by runs of code points.\n",
        table("GRAPHEME_AT", "u32", g_at),
        table("GRAPHEME_IS", "u8", g_is),
        "// Canonical_Combining_Class, by runs.\n",
        table("CCC_AT", "u32", c_at),
        table("CCC_IS", "u8", c_is),
        "// `1` Cased, `2` Case_Ignorable, by runs: what the final sigma's rule asks.\n",
        table("CASE_AT", "u32", k_at),
        table("CASE_IS", "u8", k_is),
        "// Canonical decompositions, in full, but Hangul's, which are computed.\n",
        mapping("DECOMP", canonical),
        "// Primary composites: `first << 21 | second`, sorted, and what the two compose to.\n",
        table("COMPOSE_KEY", "u64", keys, 8),
        table("COMPOSE_TO", "u32", [compose[k] for k in keys]),
        "// Full case mappings, where they are unconditional.\n",
        mapping("LOWER", lower),
        mapping("UPPER", upper),
    ]
    path = os.path.join(os.path.dirname(__file__), "..", "std", "unicode.fly")
    with open(path, encoding="utf-8") as f:
        code = f.read()
    head = code.split(MARK, 1)[0]
    with open(path, "w", encoding="utf-8") as f:
        f.write(head + "".join(x if x.endswith("\n") else x + "\n" for x in out))


if __name__ == "__main__":
    main(sys.argv[1])
