#!/usr/bin/env python3
"""Deterministic, read-only census of recurring self-host bootstrap patterns.

WHY THE GUARDS EXIST. This script GATES CI (the hygiene lane runs `--ratchet`),
and a gate that cannot see its subject passes vacuously: the original file
discovery was a non-recursive glob over `selfhost/*.sigil`, so a routine
relocation of the sources into a subdirectory would have zeroed every count and
reported "lower the pin to 0" -- maximum apparent progress at the exact moment
the census stopped measuring. Discovery is now recursive and an EMPTY file set
fails closed (exit 2) instead of reporting success over nothing.

WHAT THE GUARDS DO NOT PROVE, stated so no one rediscovers it: a PARTIAL
relocation (some files moved outside `selfhost/`) still undercounts silently --
the census has no pinned file list. The DDC lane's certified-composition digest
(`interp/certified.py`) is the instrument that screams when the module set
drifts; this census deliberately does not duplicate that pin.

Self-test (SC-P4 for tooling: an absence is only evidence if the detector can
see the construct when it IS present):

    python tools/selfhost_ergonomics_census.py --self-test

plants one instance of every censused pattern in a scratch tree and requires
each detector to report exactly it, requires a clean snippet to count zero,
and requires the empty-tree fail-closed path to actually refuse. CI runs this
as its own step before trusting the ratchet.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path

EMPTY_ELSE = re.compile(r"^\s*}\s*else\s*\{\s*$")
RETURN = re.compile(r"^\s*return\b")
IF = re.compile(r"^\s*if\s+(.+)\{\s*$")
TOKEN_COMPARE = re.compile(r"\b(?:[A-Za-z_][A-Za-z0-9_]*\.)?kind\s*==\s*T_[A-Z0-9_]+\b")
DISPATCH_COMPARE = re.compile(
    r"^\s*if\s+([A-Za-z_][A-Za-z0-9_.]*)\s*==\s*(T_[A-Z0-9_]+)\s*\{\s*$"
)


def source_files(root: Path) -> list[Path]:
    # rglob, not glob: a relocation into selfhost/src/ must move the census
    # with it, not zero it out. Flat today (12 files, none nested), so the
    # recursive spelling changes nothing now and survives the move later.
    return sorted((root / "selfhost").rglob("*.sigil"))


def location(path: Path, line: int, root: Path) -> str:
    return f"{path.relative_to(root)}:{line}"


def census(root: Path) -> dict[str, object]:
    files = source_files(root)
    # FAIL CLOSED on an empty subject: zero files would make every count zero
    # and the ratchet would praise the "progress". Exit 2 (infrastructure
    # failure), distinct from the ratchet's exit 1 (a count grew).
    if not files:
        print(
            f"census FAIL-CLOSED: found 0 .sigil files under {root / 'selfhost'} -- "
            "the census cannot vouch for sources it cannot see. If the tree moved, "
            "fix the path here; do not let the ratchet pass over nothing.",
            file=sys.stderr,
        )
        raise SystemExit(2)
    empty_else: list[str] = []
    guard_returns: list[str] = []
    nested_conditions: list[str] = []
    token_comparisons: list[str] = []
    dispatch_chains: list[dict[str, object]] = []
    overlaps: list[str] = []
    total_lines = 0

    for path in files:
        lines = path.read_text(encoding="utf-8").splitlines()
        total_lines += len(lines)
        file_token_lines: set[int] = set()
        file_guard_lines: set[int] = set()
        dispatch_run: list[tuple[int, str, str]] = []

        for index, line in enumerate(lines):
            line_no = index + 1
            if EMPTY_ELSE.match(line) and index + 1 < len(lines) and lines[index + 1].strip() == "}":
                empty_else.append(location(path, line_no, root))

            if IF.match(line):
                next_nonblank = index + 1
                while next_nonblank < len(lines) and not lines[next_nonblank].strip():
                    next_nonblank += 1
                if next_nonblank < len(lines) and RETURN.match(lines[next_nonblank]):
                    guard_returns.append(location(path, line_no, root))
                    file_guard_lines.add(line_no)

                previous_nonblank = index - 1
                while previous_nonblank >= 0 and not lines[previous_nonblank].strip():
                    previous_nonblank -= 1
                if previous_nonblank >= 0 and IF.match(lines[previous_nonblank]):
                    nested_conditions.append(location(path, line_no, root))

            if TOKEN_COMPARE.search(line):
                token_comparisons.append(location(path, line_no, root))
                file_token_lines.add(line_no)

            dispatch = DISPATCH_COMPARE.match(line)
            if dispatch:
                subject, value = dispatch.groups()
                if dispatch_run and dispatch_run[-1][1] != subject:
                    if len(dispatch_run) >= 2:
                        dispatch_chains.append(
                            {
                                "subject": dispatch_run[0][1],
                                "arms": len(dispatch_run),
                                "start": location(path, dispatch_run[0][0], root),
                                "end": location(path, dispatch_run[-1][0], root),
                            }
                        )
                    dispatch_run = []
                dispatch_run.append((line_no, subject, value))
            elif line.strip() and not line.lstrip().startswith(("//", "return", "} else", "}")):
                if len(dispatch_run) >= 2:
                    dispatch_chains.append(
                        {
                            "subject": dispatch_run[0][1],
                            "arms": len(dispatch_run),
                            "start": location(path, dispatch_run[0][0], root),
                            "end": location(path, dispatch_run[-1][0], root),
                        }
                    )
                dispatch_run = []

        if len(dispatch_run) >= 2:
            dispatch_chains.append(
                {
                    "subject": dispatch_run[0][1],
                    "arms": len(dispatch_run),
                    "start": location(path, dispatch_run[0][0], root),
                    "end": location(path, dispatch_run[-1][0], root),
                }
            )
        for line_no in sorted(file_token_lines & file_guard_lines):
            overlaps.append(location(path, line_no, root))

    return {
        "files": [str(path.relative_to(root)) for path in files],
        "total_lines": total_lines,
        "counts": {
            "exact_empty_else": len(empty_else),
            "guard_return_candidates": len(guard_returns),
            "direct_nested_if_candidates": len(nested_conditions),
            "token_kind_comparisons": len(token_comparisons),
            "dispatch_chains": len(dispatch_chains),
            "token_guard_overlap": len(overlaps),
        },
        "locations": {
            "exact_empty_else": empty_else,
            "guard_return_candidates": guard_returns,
            "direct_nested_if_candidates": nested_conditions,
            "token_kind_comparisons": token_comparisons,
            "dispatch_chains": dispatch_chains,
            "token_guard_overlap": overlaps,
        },
    }


# Ratchet ceilings: a count may FALL freely, it may not RISE.
#
# This exists because of a measured regression. The 2026-07-25 ergonomics
# course drove `exact_empty_else` to 0 after optional-`else` shipped, and by
# 2026-08-02 it had climbed back to 2103 as the self-host roughly doubled in
# size. Nothing held the line, so the cleanup measured a moment rather than
# establishing a property. Lower a ceiling whenever the real count drops --
# the script tells you when there is slack.
RATCHET_CEILINGS = {
    "exact_empty_else": 2103,
}


def run_ratchet(report: dict) -> int:
    """Return a process exit code: 0 when every count is at or under its ceiling."""
    failures = []
    slack = []
    for name, ceiling in sorted(RATCHET_CEILINGS.items()):
        actual = report["counts"][name]
        if actual > ceiling:
            failures.append(f"  {name}: {actual} exceeds ceiling {ceiling} (+{actual - ceiling})")
        elif actual < ceiling:
            slack.append(f"  {name}: {actual} is under ceiling {ceiling} -- lower the pin to {actual}")
        else:
            slack.append(f"  {name}: {actual} (at ceiling)")
    if failures:
        print("RATCHET FAILURE -- these counts grew:")
        for line in failures:
            print(line)
        print("\nEither remove the new occurrences or, if the growth is deliberate and")
        print("justified, raise the ceiling in RATCHET_CEILINGS with a reason.")
        return 1
    print("ratchet ok:")
    for line in slack:
        print(line)
    return 0


# One planted instance of every censused pattern, in the regexes' exact
# shapes. Kept next to the detectors it proves so a regex edit and its
# proof-of-detection travel together.
PLANTED = """\
if outer {
if t.kind == T_EOF {
    return 1
}
} else {
}
let after = 1
if k == T_A {
if k == T_B {
"""

# Expected counts over PLANTED, derived by hand from the detector semantics:
#   exact_empty_else          `} else {` immediately followed by `}`
#   guard_return_candidates   the token-compare `if` whose next line returns
#   direct_nested_if          the token-compare `if` directly under `if outer`
#   token_kind_comparisons    the single `.kind == T_EOF`
#   dispatch_chains           `if k == T_A` directly over `if k == T_B` --
#                             the arms must be CONSECUTIVE: any interleaved
#                             statement resets the run (this table's first
#                             draft assumed otherwise and the self-test
#                             refused it, which is the self-test working)
#   token_guard_overlap       the `if t.kind == T_EOF` line is both a token
#                             compare and a guard return
PLANTED_EXPECTED = {
    "exact_empty_else": 1,
    "guard_return_candidates": 1,
    # 2, not 1: the token-compare `if` sits under `if outer`, and the second
    # dispatch arm sits under the first (dispatch arms are also `if` lines).
    "direct_nested_if_candidates": 2,
    "token_kind_comparisons": 1,
    "dispatch_chains": 1,
    "token_guard_overlap": 1,
}

# A snippet with none of the patterns: the detectors must stay silent on it
# (the other half of SC-P4 — a detector that fires on everything is as
# useless as one that fires on nothing).
CLEAN = """\
fn plain(x: i64) -> i64 {
    let y = x
    return y
}
"""


def self_test() -> int:
    """Prove every detector detects, stays silent on clean input, and that
    the empty-tree path fails closed. Exit 0 only if all three hold."""
    failures: list[str] = []

    def counts_for(snippet: str) -> dict[str, int]:
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            (root / "selfhost" / "nested").mkdir(parents=True)
            # Nested on purpose: also proves discovery is recursive.
            (root / "selfhost" / "nested" / "probe.sigil").write_text(
                snippet, encoding="utf-8"
            )
            return dict(census(root)["counts"])

    planted = counts_for(PLANTED)
    for name, expected in sorted(PLANTED_EXPECTED.items()):
        actual = planted[name]
        if actual != expected:
            failures.append(
                f"  detector `{name}`: expected {expected} on the planted "
                f"snippet, counted {actual} — the detector cannot see (or "
                f"over-sees) the construct it censuses"
            )

    clean = counts_for(CLEAN)
    for name, actual in sorted(clean.items()):
        if actual != 0:
            failures.append(
                f"  detector `{name}`: counted {actual} on a clean snippet — "
                f"a detector that fires on everything proves nothing"
            )

    with tempfile.TemporaryDirectory() as scratch:
        empty_root = Path(scratch)
        (empty_root / "selfhost").mkdir()
        try:
            census(empty_root)
            failures.append(
                "  empty-tree path: census returned a report over 0 files "
                "instead of failing closed"
            )
        except SystemExit as refusal:
            if refusal.code != 2:
                failures.append(
                    f"  empty-tree path: refused with exit {refusal.code}, expected 2"
                )

    if failures:
        print("SELF-TEST FAILURE — the census cannot be trusted to gate:")
        for line in failures:
            print(line)
        return 1
    print("self-test ok: every detector detects, stays silent on clean input,")
    print("and the empty-tree path fails closed.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--ratchet",
        action="store_true",
        help="fail (exit 1) if any censused count has grown past its pinned ceiling",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="prove each detector on planted input before trusting the gate",
    )
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    report = census(args.root.resolve())
    if args.ratchet:
        return run_ratchet(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    print(f"self-host files: {len(report['files'])}")
    print(f"total lines: {report['total_lines']}")
    for name, count in report["counts"].items():
        print(f"{name}: {count}")
    for name, entries in report["locations"].items():
        print(f"\n[{name}]")
        for entry in entries:
            print(entry if isinstance(entry, str) else json.dumps(entry, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
