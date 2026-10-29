"""The recipes prompt's quick-fix table must state each code's registry meaning.

`bench/src/sigil_bench/prompts/recipes.md` is composed into the model's system prompt, and its
"Common diagnostics" table drifted until six of its eight rows were wrong: it said T070 meant an
effect-row mismatch (T070 is a call arity mismatch) and R002 a missing `#[trusted]` (R002 is a
capability reference returned from an outer-ring function). A model reading that table is taught
the wrong language. This pins every row's Meaning cell to the code's title in the central registry,
`crates/sigil-compiler/src/diagnostics/registry.rs`.

What it cannot check: which code a described situation actually produces. That was measured by
compiling a probe for each row when the rows were written; the registry title is what keeps a
row's meaning from drifting afterwards.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
RECIPES_PATH = REPO_ROOT / "bench" / "src" / "sigil_bench" / "prompts" / "recipes.md"
REGISTRY_PATH = REPO_ROOT / "crates" / "sigil-compiler" / "src" / "diagnostics" / "registry.rs"
TABLE_HEADING = "## Common diagnostics"

_ENTRY = re.compile(r'code:\s*([A-Z]+\d+),\s*title:\s*"((?:[^"\\]|\\.)*)"')
_ROW = re.compile(r"^\|\s*`([A-Z]+\d+)`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*$")
_HEADER = re.compile(r"^\|\s*Code\s*\|\s*Meaning\s*\|\s*Fix\s*\|\s*$")
_RULE = re.compile(r"^\|(\s*:?-+:?\s*\|)+\s*$")


def registry_titles(text: str) -> dict[str, str]:
    """Map each registered code to its title, unescaping the Rust string literal."""
    return {
        code: raw.replace('\\"', '"').replace("\\\\", "\\")
        for code, raw in _ENTRY.findall(text)
    }


def table_rows(markdown: str) -> list[tuple[str, str]]:
    """Return (code, meaning) for each row of the "Common diagnostics" table.

    Fails closed: a missing section, a section with no code rows, or any table line in it that is
    not the header, the rule or a well-formed code row raises. Skipping a malformed row instead
    would let it carry a wrong meaning past every comparison."""
    start = markdown.find(TABLE_HEADING)
    if start < 0:
        raise AssertionError(f"no {TABLE_HEADING!r} section")
    rows = []
    for line in markdown[start:].splitlines()[1:]:
        if line.startswith("## "):
            break
        if not line.lstrip().startswith("|"):
            continue
        match = _ROW.match(line)
        if match:
            rows.append((match.group(1), match.group(2)))
        elif not (_HEADER.match(line) or _RULE.match(line)):
            raise AssertionError(f"unparseable table line in {TABLE_HEADING!r}: {line!r}")
    if not rows:
        raise AssertionError(f"the {TABLE_HEADING!r} section has no code rows")
    return rows


def mismatches(rows: list[tuple[str, str]], titles: dict[str, str]) -> list[str]:
    """Every row whose code is unregistered or whose meaning is not the registry title."""
    problems = []
    for code, meaning in rows:
        title = titles.get(code)
        if title is None:
            problems.append(f"{code}: not a registered diagnostic code")
        elif meaning != title:
            problems.append(f"{code}: table says {meaning!r}, registry says {title!r}")
    return problems


def test_registry_parse_is_not_vacuous():
    titles = registry_titles(REGISTRY_PATH.read_text(encoding="utf-8"))
    # Hundreds of codes are registered; a parse that finds a handful means the pattern broke.
    assert len(titles) >= 300, f"parsed only {len(titles)} registry entries"
    assert titles["T060"] == "Undefined local"


def test_every_quick_fix_row_states_its_registry_meaning():
    titles = registry_titles(REGISTRY_PATH.read_text(encoding="utf-8"))
    rows = table_rows(RECIPES_PATH.read_text(encoding="utf-8"))
    assert mismatches(rows, titles) == []


def test_the_comparison_detects_a_planted_wrong_row():
    """SC-P4: the check must fail on the drift it exists to catch."""
    titles = {"T060": "Undefined local", "T070": "Function call arity mismatch"}
    planted = (
        "## Common diagnostics — quick fixes\n\n"
        "| Code | Meaning | Fix |\n"
        "|---|---|---|\n"
        "| `T060` | Undefined local | Fix the typo. |\n"
        "| `T070` | Effect-row mismatch | Add the effect. |\n"
        "| `Z999` | Not a code | Nothing. |\n"
    )
    assert mismatches(table_rows(planted), titles) == [
        "T070: table says 'Effect-row mismatch', registry says 'Function call arity mismatch'",
        "Z999: not a registered diagnostic code",
    ]


def test_table_rows_fail_closed_without_rows():
    with pytest.raises(AssertionError):
        table_rows("no such section here\n")
    with pytest.raises(AssertionError):
        table_rows("## Common diagnostics\n\nprose only\n## Next section\n")


@pytest.mark.parametrize(
    "malformed",
    [
        "| T070 | Effect-row mismatch | Add the effect. |",
        "| **`T070`** | Effect-row mismatch | Add the effect. |",
        "| `T070`, `T071` | Effect-row mismatch | Add the effect. |",
        "  | `T070` | Effect-row mismatch | Add the effect. |",
        "| `T070` | Effect-row mismatch | Add the effect.",
        "| `T070` (arity) | Effect-row mismatch | Add the effect. |",
    ],
)
def test_a_malformed_row_fails_instead_of_being_skipped(malformed):
    """SC-P4: a row the parser cannot read must not silently drop out of the comparison."""
    table = (
        "## Common diagnostics — quick fixes\n\n"
        "| Code | Meaning | Fix |\n"
        "|---|---|---|\n"
        "| `T060` | Undefined local | Fix the typo. |\n"
        f"{malformed}\n"
    )
    with pytest.raises(AssertionError, match="unparseable table line"):
        table_rows(table)
