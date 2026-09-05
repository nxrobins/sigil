"""Phase 0: the measured subset inventory.

Parses every source that `cap0_input()` composes and reports which syntactic forms the certified
surface actually uses. The parser is LOUD on anything it does not recognize, so a clean run is the
evidence that the inventory below is complete — not a grep's guess.

    python interp/census.py            # human report
    python interp/census.py --forms    # one form per line, for pinning
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

from sigil_lex import LexError
from sigil_parse import ParseError, parse

# Running `python interp/census.py` already puts `interp/` on sys.path[0], so no path
# manipulation is needed — and without it the imports sit at the top, where no lint rule has an
# opinion about them.
sys.setrecursionlimit(20000)

REPO = Path(__file__).resolve().parent.parent

# Exactly what `boot_tool` + `boot_mono_tool` + `cap0_input` compose, in that order.
CERTIFIED = [
    "selfhost/lexer.sigil",
    "selfhost/parser.sigil",
    "selfhost/name_resolution.sigil",
    "selfhost/typecheck.sigil",
    "selfhost/ring_check.sigil",
    "selfhost/effect_check.sigil",
    "selfhost/taint_check.sigil",
    "selfhost/cap_check.sigil",
    "selfhost/own_check.sigil",
    "selfhost/air.sigil",
    "selfhost/pipeline.sigil",
    "selfhost/monomorph.sigil",
    "stdlib/sigil/vec.sigil",
    "stdlib/sigil/arena.sigil",
    "stdlib/sigil/string.sigil",
    "stdlib/sigil/strings.sigil",
    "stdlib/sigil/option.sigil",
]


# `cap0_input()` EXCLUDES these stdlib leaves from the certified surface. The census must strip
# them too, or it inventories constructs (e.g. the `&[str]` slice parameter of
# `__sigil_slice_str_contains`) that the certified source does not contain — reporting a larger
# subset than the interpreter must actually support.
STRIP = {
    "stdlib/sigil/string.sigil": ["str_utoa_u64"],
    "stdlib/sigil/strings.sigil": [
        "str_contains",
        "__sigil_slice_str_contains",
        "str_parse_u64",
        "str_parse_u32",
        "str_parse_i32",
    ],
}


def strip_fn(src: str, name: str, rel: str) -> str:
    """Mirror of `cap0_strip_fn`: drop `pub fn NAME(` through the column-0 closing brace."""
    marker = f"pub fn {name}("
    start = src.find(marker)
    if start < 0:
        raise SystemExit(f"census: strip target {name} not found in {rel} (cap0 would also fail)")
    line_start = src.rfind("\n", 0, start) + 1
    end_pat = "\n}\n"
    end = src.find(end_pat, start)
    if end < 0:
        raise SystemExit(f"census: no end brace for {name} in {rel}")
    return src[:line_start] + src[end + len(end_pat):]


def count_decls(node) -> dict[str, int]:
    out: dict[str, int] = {}
    for item in node.items:
        out[item.kind] = out.get(item.kind, 0) + 1
        if item.kind == "impl":
            out["method"] = out.get("method", 0) + len(item.b)
    return out


# FENCE for the figures quoted in README.md. They were accurate but unpinned — the exact
# configuration that let claim 26 drift 57 entries behind its manifest. Floors rather than exact
# equalities: the certified surface may grow, but it may not silently SHRINK, and the form count
# may not quietly collapse (which would mean the census stopped seeing constructs).
README_FLOORS = {
    "files": 17,
    "lines": 26_000,
    "fn": 450,
    "record": 20,
    "const": 255,
    "forms": 45,
}


def check_readme_floors(totals: dict[str, int], forms: int, files: int, lines: int) -> list[str]:
    measured = {
        "files": files,
        "lines": lines,
        "fn": totals.get("fn", 0),
        "record": totals.get("record", 0),
        "const": totals.get("const", 0),
        "forms": forms,
    }
    return [
        f"{k}: measured {measured[k]:,} is below the pinned floor {v:,}"
        for k, v in README_FLOORS.items()
        if measured[k] < v
    ]


def main() -> int:
    forms_only = "--forms" in sys.argv
    all_forms: set[str] = set()
    totals: dict[str, int] = {}
    failures: list[str] = []
    total_lines = 0
    started = time.perf_counter()

    for rel in CERTIFIED:
        path = REPO / rel
        src = path.read_text(encoding="utf-8")
        for name in STRIP.get(rel, []):
            src = strip_fn(src, name, rel)
        total_lines += src.count("\n")
        try:
            program, forms = parse(src, rel)
        except (ParseError, LexError) as e:
            failures.append(str(e))
            continue
        all_forms |= forms
        for k, v in count_decls(program).items():
            totals[k] = totals.get(k, 0) + v

    elapsed = time.perf_counter() - started

    if forms_only:
        for f in sorted(all_forms):
            print(f)
        return 1 if failures else 0

    print(f"certified sources : {len(CERTIFIED)} files, {total_lines:,} lines")
    print(f"parse time        : {elapsed:.2f}s  ({total_lines / max(elapsed, 1e-9):,.0f} lines/s)")
    print()
    if failures:
        print(f"UNRECOGNIZED CONSTRUCTS ({len(failures)} file(s) failed) — this IS the inventory gap:")
        for f in failures:
            print(f"  {f}")
        print()
    print("declarations:")
    for k in sorted(totals):
        print(f"  {k:<10} {totals[k]:>5}")
    print()
    print(f"syntactic forms used ({len(all_forms)}):")
    for f in sorted(all_forms):
        print(f"  {f}")

    shrunk = check_readme_floors(totals, len(all_forms), len(CERTIFIED), total_lines)
    if shrunk:
        print()
        print("README FLOOR BREACHED — the figures quoted in interp/README.md no longer hold:")
        for s in shrunk:
            print(f"  {s}")
        return 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
