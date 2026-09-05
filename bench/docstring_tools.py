#!/usr/bin/env python3
"""Tools-corpus docstring generator (scratch script for Phase 2).

For each tool that doesn't yet have a DEMONSTRATES/PROBE/TASK/MANUAL
header comment, infer purpose from the filename slug + signature
recorded in bench/tools-index-cursor.json and prepend a short header.

Idempotent: tools whose first non-blank line already contains one of
the marker strings are skipped.

Run from repo root:
    python bench/docstring_tools.py [count]
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TOOLS_DIR = REPO / "tools"
CURSOR = REPO / "bench" / "tools-index-cursor.json"

MARKERS = ("DEMONSTRATES:", "PROBE:", "TASK:", "MANUAL:", "UNCATEGORIZED:")


def load_cursor() -> dict[str, dict]:
    out = {}
    if not CURSOR.is_file():
        return out
    with CURSOR.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            entry = json.loads(line)
            out[entry["name"]] = entry
    return out


def already_documented(src: str) -> bool:
    for raw in src.splitlines():
        s = raw.strip()
        if not s:
            continue
        if not s.startswith("//"):
            return False  # first non-blank line is not a comment — no docstring
        if any(m in s for m in MARKERS):
            return True
    return False


def humanize_slug(slug: str) -> str:
    """task001_echo → 'echo'; probe_cast_i32_to_i64 → 'cast i32 to i64'."""
    # Strip leading prefix patterns.
    parts = slug.split(".sigil")[0]
    parts = re.sub(r"^task\d+_?", "", parts)
    parts = re.sub(r"^probe_", "", parts)
    parts = re.sub(r"^manual_", "", parts)
    return parts.replace("_", " ")


def extract_effects(signature: str) -> str:
    """Pull the effect row out of a function signature."""
    m = re.search(r"!\s*\{([^}]*)\}", signature)
    if not m:
        return ""
    raw = m.group(1).strip()
    # Normalize whitespace.
    raw = re.sub(r"\s+", " ", raw)
    return raw


def describe_io(signature: str) -> tuple[str, str]:
    """Best-effort INPUT/OUTPUT description from the signature."""
    # All tool_main signatures share the shape:
    #   pub fn tool_main(input_ptr: <i32|i64>, input_len: <i32|i64>) -> i64 ...
    # The output i64 commonly encodes either:
    #   - a packed (ptr, len) pair (high 32 bits = len, low 32 = ptr), or
    #   - a single number (e.g., row count, byte count, hash low 64 bits).
    has_i32 = "i32" in signature
    width = "i32" if has_i32 else "i64"
    return (
        f"`input_ptr`/`input_len` ({width}) point at the host-allocated input buffer.",
        "`i64` — packed result. Most tools pack `(len << 32) | ptr` for a "
        "buffer result, or return a single integer for arithmetic/counting tools. "
        "See the body for the exact encoding.",
    )


def gen_docstring(name: str, entry: dict) -> str:
    """Build a 3-4 line header comment for the tool."""
    signature = entry.get("first_body_line", "")
    effects = extract_effects(signature)
    input_desc, output_desc = describe_io(signature)
    slug = humanize_slug(name)

    if name.startswith("probe_"):
        lines = [
            f"// PROBE: {slug} — compiler/runtime scaffolding, not a pattern example.",
        ]
    elif name.startswith("manual_"):
        lines = [
            f"// MANUAL: {slug} — manual verification fixture.",
            f"// INPUT: {input_desc}",
            f"// OUTPUT: {output_desc}",
        ]
    elif name.startswith("task"):
        lines = [
            f"// TASK: {slug} — agent-targeted demonstration tool.",
            f"// INPUT: {input_desc}",
            f"// OUTPUT: {output_desc}",
        ]
    else:
        cats = entry.get("categories", ["uncategorized"])
        lines = [
            f"// DEMONSTRATES: {slug} ({', '.join(cats)}).",
            f"// INPUT: {input_desc}",
            f"// OUTPUT: {output_desc}",
        ]

    if effects:
        lines.append(f"// EFFECTS: ! {{ {effects} }}")
    return "\n".join(lines) + "\n"


def process(count: int) -> tuple[int, list[str]]:
    cursor = load_cursor()
    processed: list[str] = []
    for name in sorted(cursor):
        if len(processed) >= count:
            break
        path = TOOLS_DIR / name
        if not path.is_file():
            continue
        src = path.read_text(encoding="utf-8", errors="replace")
        if already_documented(src):
            continue
        header = gen_docstring(name, cursor[name])
        # Preserve a blank line between header and source.
        new_src = header + "\n" + src.lstrip("\n")
        path.write_text(new_src, encoding="utf-8")
        processed.append(name)
    return len(processed), processed


def main() -> None:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    n, processed = process(count)
    print(f"Documented {n} tools this batch.")
    for name in processed:
        print(f"  + {name}")


if __name__ == "__main__":
    main()
