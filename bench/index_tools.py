#!/usr/bin/env python3
"""Tools-corpus indexer (scratch script for the tools-corpus-improvement loop).

Walks tools/*.sigil sorted alphabetically. Takes (start_index, count) on the
CLI; processes that batch; appends one JSON line per tool to
bench/tools-index-cursor.json. After updating the cursor, regenerates
tools/INDEX.md by grouping all cursor entries by category and sorting
alphabetically within each.

Idempotent: re-processing the same tool overwrites its cursor row.

Run from repo root:
    python bench/index_tools.py <start_index> <count>
"""

from __future__ import annotations

import json
import re
import sys
from datetime import date
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TOOLS_DIR = REPO / "tools"
CURSOR = REPO / "bench" / "tools-index-cursor.json"
INDEX_MD = REPO / "tools" / "INDEX.md"


# Categories, in the order they should appear in INDEX.md.
# Each entry: (name, detector). The detector is called with (filename, source)
# and returns True if the tool belongs to the category. A tool may belong to
# multiple categories.
def _has_effect(src: str, eff: str) -> bool:
    # Match "! { ... <eff> ... }" — effect row containing <eff>.
    return bool(re.search(r"!\s*\{[^}]*\b" + re.escape(eff) + r"\b[^}]*\}", src))


CATEGORIES: list[tuple[str, "callable"]] = [
    (
        "ffi_outer_ring",
        lambda name, src: "#[ring(outer)]" in src and 'extern "C"' in src,
    ),
    (
        "actor",
        lambda name, src: re.search(r"\bactor\s+\w+", src) is not None,
    ),
    (
        "spawn_send",
        lambda name, src: "spawn::<" in src,
    ),
    (
        "cap_typed",
        lambda name, src: re.search(r"\bcap\s+type\b", src) is not None,
    ),
    (
        "restrict_deadline",
        lambda name, src: ".restrict_deadline(" in src,
    ),
    (
        "slot",
        lambda name, src: ("Slot<" in src) or ("slot_put" in src) or ("slot_new::<" in src),
    ),
    (
        "taint",
        lambda name, src: any(t in src for t in ("@Public", "@Secret", "@Internal")),
    ),
    (
        "alloc",
        lambda name, src: _has_effect(src, "Alloc"),
    ),
    (
        "probe",
        lambda name, src: name.startswith("probe_"),
    ),
    (
        "task",
        lambda name, src: name.startswith("task"),
    ),
    (
        "manual",
        lambda name, src: name.startswith("manual_"),
    ),
    (
        "pure_compute",
        lambda name, src: (
            not re.search(r"!\s*\{", src)
            and not re.search(r"\bactor\s+\w+", src)
            and 'extern "C"' not in src
        ),
    ),
]


def _strip_comments(src: str) -> str:
    """Drop // line comments before category detection, so that words
    inside docstrings (e.g., 'actor that takes an ApiKey-style cap')
    don't trigger false-positive matches against the category regexes.
    """
    out: list[str] = []
    for line in src.splitlines():
        idx = line.find("//")
        if idx == -1:
            out.append(line)
        else:
            out.append(line[:idx])
    return "\n".join(out)


def categorize(name: str, src: str) -> list[str]:
    code = _strip_comments(src)
    cats = [n for n, det in CATEGORIES if det(name, code)]
    if not cats:
        return ["uncategorized"]
    return cats


def first_body_line(src: str) -> str:
    """Pick the most informative single-line signature for the index.

    Priority:
      1. `pub fn tool_main(...) -> ... ! { ... }` — the canonical entry
         signature; carries effect row + parameter types.
      2. `pub fn <name>(...) -> ...` — any other top-level pub function.
      3. `actor <Name> { ... }` — actor declarations.
      4. `cap type <Name> { ... }` — capability type declarations.
      5. The first non-blank, non-comment, non-`module` line.
    """
    lines = src.splitlines()

    # Reassemble multi-line signatures (rare, but tool_main occasionally spans).
    # Strategy: scan for the signature keyword, then accumulate until the line
    # ending in `{` or `;`.
    def grab_signature(start_idx: int) -> str:
        acc: list[str] = []
        for line in lines[start_idx:]:
            acc.append(line.strip())
            if acc[-1].endswith("{") or acc[-1].endswith(";"):
                break
        return " ".join(acc)[:160]

    for i, raw in enumerate(lines):
        s = raw.strip()
        if s.startswith("pub fn tool_main"):
            return grab_signature(i)
    for i, raw in enumerate(lines):
        s = raw.strip()
        if s.startswith("pub fn "):
            return grab_signature(i)
    for i, raw in enumerate(lines):
        s = raw.strip()
        if s.startswith("actor "):
            return grab_signature(i)
    for i, raw in enumerate(lines):
        s = raw.strip()
        if s.startswith("cap type "):
            return grab_signature(i)
    for raw in lines:
        s = raw.strip()
        if not s or s.startswith("//"):
            continue
        if s.startswith("module ") or s.startswith("#["):
            continue
        return s[:160]
    return "(no informative signature)"


def load_cursor() -> dict[str, dict]:
    if not CURSOR.is_file():
        return {}
    out = {}
    with CURSOR.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            entry = json.loads(line)
            out[entry["name"]] = entry
    return out


def save_cursor(rows: dict[str, dict]) -> None:
    CURSOR.parent.mkdir(parents=True, exist_ok=True)
    with CURSOR.open("w", encoding="utf-8") as f:
        for name in sorted(rows):
            f.write(json.dumps(rows[name], ensure_ascii=False))
            f.write("\n")


def regenerate_index(rows: dict[str, dict]) -> None:
    # Group by category. A tool with multiple categories appears under each.
    by_cat: dict[str, list[dict]] = {n: [] for n, _ in CATEGORIES}
    by_cat["uncategorized"] = []
    for row in rows.values():
        for cat in row["categories"]:
            by_cat.setdefault(cat, []).append(row)

    lines: list[str] = []
    lines.append("# Tools corpus index")
    lines.append("")
    lines.append(
        f"**Last updated:** {date.today().isoformat()} · "
        f"**{len(rows)} of 212 tools indexed.**"
    )
    lines.append("")
    lines.append(
        "Auto-generated by `bench/index_tools.py` during the tools-corpus-"
        "improvement loop. Each tool is classified by the SIGIL features its "
        "source exercises (effect row, capability declarations, ring tagging, "
        "actor model, etc.) plus a filename-prefix bucket (probe/task/manual)."
    )
    lines.append("")
    lines.append("A tool may appear under multiple categories.")
    lines.append("")

    # Section per category, in CATEGORIES declaration order, then uncategorized.
    order = [n for n, _ in CATEGORIES] + ["uncategorized"]
    for cat in order:
        items = sorted(by_cat.get(cat, []), key=lambda r: r["name"])
        if not items:
            continue
        lines.append(f"## {cat} ({len(items)})")
        lines.append("")
        for row in items:
            lines.append(f"- `{row['name']}` — {row['first_body_line']}")
        lines.append("")

    INDEX_MD.write_text("\n".join(lines), encoding="utf-8")


def process_batch(start: int, count: int) -> tuple[int, int]:
    files = sorted(p for p in TOOLS_DIR.iterdir() if p.suffix == ".sigil")
    total = len(files)
    end = min(start + count, total)
    batch = files[start:end]

    rows = load_cursor()
    for path in batch:
        src = path.read_text(encoding="utf-8", errors="replace")
        name = path.name
        entry = {
            "name": name,
            "categories": categorize(name, src),
            "first_body_line": first_body_line(src),
            "line_count": len(src.splitlines()),
        }
        rows[name] = entry
    save_cursor(rows)
    regenerate_index(rows)
    return end, total


def main() -> None:
    if len(sys.argv) < 3:
        # Default: continue from current cursor state.
        rows = load_cursor()
        start = len(rows)
        count = 30
    else:
        start = int(sys.argv[1])
        count = int(sys.argv[2])

    end, total = process_batch(start, count)
    print(f"Batch processed: tools[{start}:{end}] of {total}. Cursor at {end}.")


if __name__ == "__main__":
    main()
