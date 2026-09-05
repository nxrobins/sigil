#!/usr/bin/env python3
"""Validate that every GitHub Actions workflow file actually parses.

WHY THIS EXISTS. On 2026-08-02 a `run:` step in `ci.yml` contained
`grep -q "test result: ok. 1 passed"`. A YAML *plain* (unquoted) scalar may not
contain ": " -- colon-space begins a mapping -- so the file stopped parsing.
GitHub's response to an unparseable workflow is not a red X on the offending
job: it refuses the whole file, so every lane defined in it never starts. Two
pull requests sat at "waiting for status" against required checks that could
never arrive. It presents as a stuck queue, not a failure.

The shell double-quotes in that command are invisible to YAML -- they sit
INSIDE a plain scalar and quote nothing as far as the parser is concerned,
which is what makes the mistake easy to write and hard to see.

THE CHICKEN-AND-EGG, AND THE WAY OUT. A check that validates workflow files
cannot protect the file it lives in: if that file fails to parse, the check
never runs. But a SIBLING workflow file is unaffected -- during the outage the
separate Lean workflow ran green the whole time. So this script is wired into
two different workflow files, and each covers the other:

  * `.github/workflows/workflow-lint.yml` runs it -- catches a broken `ci.yml`
  * `ci.yml`'s hygiene lane runs it -- catches a broken `workflow-lint.yml`

Whichever file breaks, the other one is still parseable, still runs, and turns
red with a real message instead of leaving the queue silently empty.

Exit code 0 when every workflow parses, 1 otherwise.

Self-test (SC-P4 for tooling — the validator's failure branches had never
executed before it existed, so "every workflow parses" was one dead branch
away from vacuous):

    python tools/validate_workflows.py --self-test

plants one workflow file per failure mode in a scratch tree — the 2026-08-02
colon-space break included — and requires the validator to refuse each one
with its specific message, requires the colon-space HINT to actually point at
the offending line, and requires a healthy pair of files to pass. Both CI
lanes that run the validator run the self-test first, as their fence.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import sys
import tempfile
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover - environment problem, not a lint failure
    print("validate_workflows: PyYAML is required (pip install pyyaml)", file=sys.stderr)
    raise SystemExit(2) from None

# A workflow with no jobs parses fine but does nothing; treat a missing `jobs`
# key as a failure so a truncated or half-written file cannot pass as valid.
REQUIRED_TOP_LEVEL_KEYS = ("jobs",)


def colon_space_hint(path: Path) -> list[str]:
    """Point at the specific line that most likely caused a parse failure.

    `yaml` reports a position but not a cause. Colon-space inside a plain
    scalar is by far the most common way a workflow breaks, so name it
    explicitly when present rather than leaving the reader to decode a parser
    error.
    """
    hints = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = line.lstrip()
        # `run:` appears in two spellings: as a mapping key on its own line
        # (`run: cargo test`) and as a list item (`- run: cargo test`). The
        # original detector only saw the first; its own self-test caught the
        # blindness on first execution — the hint had never run before.
        if stripped.startswith("- "):
            stripped = stripped[2:]
        for key in ("run:", "if:"):
            if not stripped.startswith(key):
                continue
            value = stripped[len(key) :].strip()
            if value[:1] in {"|", ">", "'", '"'}:
                continue  # block scalar or properly quoted
            if ": " in value:
                hints.append(f"    line {number}: plain `{key}` scalar contains \": \" -> {line.strip()}")
    return hints


def validate(root: Path) -> int:
    workflow_dir = root / ".github" / "workflows"
    if not workflow_dir.is_dir():
        print(f"validate_workflows: no such directory: {workflow_dir}", file=sys.stderr)
        return 1

    files = sorted(
        path for path in workflow_dir.iterdir() if path.suffix in {".yml", ".yaml"}
    )

    # Anti-vacuity floor. With zero files this would report success while
    # checking nothing -- the same silence it exists to prevent.
    if len(files) < 2:
        print(
            f"validate_workflows: expected at least 2 workflow files, found {len(files)}.\n"
            "  The mutual-coverage protocol needs at least two: each file's validity is\n"
            "  proven by a lane defined in the other one.",
            file=sys.stderr,
        )
        return 1

    failures = 0
    for path in files:
        try:
            document = yaml.safe_load(path.read_text(encoding="utf-8"))
        except yaml.YAMLError as error:
            failures += 1
            print(f"INVALID {path.name}: {error}", file=sys.stderr)
            for hint in colon_space_hint(path):
                print(hint, file=sys.stderr)
            continue

        if not isinstance(document, dict):
            failures += 1
            print(f"INVALID {path.name}: top level is not a mapping", file=sys.stderr)
            continue

        missing = [key for key in REQUIRED_TOP_LEVEL_KEYS if key not in document]
        if missing:
            failures += 1
            print(f"INVALID {path.name}: missing top-level key(s): {missing}", file=sys.stderr)
            continue

        jobs = document["jobs"]
        if not isinstance(jobs, dict) or not jobs:
            failures += 1
            print(f"INVALID {path.name}: `jobs` is empty or not a mapping", file=sys.stderr)
            continue

        print(f"ok {path.name} ({len(jobs)} job(s): {', '.join(sorted(jobs))})")

    if failures:
        print(
            f"\n{failures} workflow file(s) would be REFUSED by GitHub.\n"
            "A refused workflow does not report a failing check -- every lane it defines\n"
            "simply never starts, and pull requests wait forever on status that cannot\n"
            "arrive. Fix before merging.",
            file=sys.stderr,
        )
        return 1

    print(f"\nall {len(files)} workflow file(s) parse")
    return 0


# A minimal healthy workflow: enough structure to pass every check.
HEALTHY = """\
name: probe
on: push
jobs:
  probe:
    runs-on: ubuntu-latest
    steps:
      - run: echo ok
"""

# One planted file per failure branch. The colon-space case reproduces the
# 2026-08-02 incident shape: a plain `run:` scalar containing ": ".
BROKEN = {
    # Both spellings of the incident shape: `- run:` as a list item and
    # `run:` as a mapping key. The hint detector was blind to the first
    # until this self-test's first execution caught it.
    "colon_space_list_item.yml": (
        "name: probe\non: push\njobs:\n  probe:\n    runs-on: ubuntu-latest\n"
        '    steps:\n      - run: grep -q "test result: ok"\n',
        "INVALID colon_space_list_item.yml",
    ),
    "colon_space_key.yml": (
        "name: probe\non: push\njobs:\n  probe:\n    runs-on: ubuntu-latest\n"
        "    steps:\n      - name: probe\n"
        '        run: grep -q "test result: ok"\n',
        "INVALID colon_space_key.yml",
    ),
    "not_a_mapping.yml": ("- just\n- a\n- list\n", "top level is not a mapping"),
    "no_jobs.yml": ("name: probe\non: push\n", "missing top-level key(s)"),
    "empty_jobs.yml": ("name: probe\non: push\njobs:\n", "`jobs` is empty or not a mapping"),
}


def self_test() -> int:
    """Prove each refusal branch refuses (with its message), the colon-space
    hint points at the offending line, the two-file floor holds, and a
    healthy pair passes. Exit 0 only if all of it holds."""
    failures: list[str] = []

    def run_validate(files: dict[str, str]) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            workflow_dir = root / ".github" / "workflows"
            workflow_dir.mkdir(parents=True)
            for name, content in files.items():
                (workflow_dir / name).write_text(content, encoding="utf-8")
            captured = io.StringIO()
            with contextlib.redirect_stderr(captured), contextlib.redirect_stdout(captured):
                code = validate(root)
            return code, captured.getvalue()

    for name, (content, expected_marker) in sorted(BROKEN.items()):
        # Pair each broken file with a healthy sibling so the two-file floor
        # is satisfied and the refusal under test is the file's own.
        code, output = run_validate({name: content, "healthy.yml": HEALTHY})
        if code == 0:
            failures.append(f"  {name}: validator PASSED a file built to be refused")
        elif expected_marker not in output:
            failures.append(
                f"  {name}: refused, but without the expected marker "
                f"{expected_marker!r} — the refusal fired from the wrong branch"
            )

    # The hint is the part that decodes the parser error into the actual
    # cause; it must name the offending line in BOTH spellings, not merely
    # exist. (The list-item spelling is the one the original detector missed.)
    for case in ("colon_space_list_item.yml", "colon_space_key.yml"):
        _, output = run_validate({case: BROKEN[case][0], "healthy.yml": HEALTHY})
        if "plain `run:` scalar contains" not in output:
            failures.append(
                f"  {case}: the parse failure was reported without the "
                "colon-space hint — colon_space_hint() is not reaching the line"
            )

    code, output = run_validate({"lonely.yml": HEALTHY})
    if code == 0 or "at least 2 workflow files" not in output:
        failures.append(
            "  two-file floor: a single-file tree must be refused (the mutual-"
            "coverage protocol needs a sibling), got exit "
            f"{code}"
        )

    code, _ = run_validate({"a.yml": HEALTHY, "b.yml": HEALTHY})
    if code != 0:
        failures.append("  positive control: a healthy pair must pass, got exit 1")

    if failures:
        print("SELF-TEST FAILURE — the validator cannot be trusted to gate:")
        for line in failures:
            print(line)
        return 1
    print("self-test ok: every refusal branch refuses with its message, the")
    print("colon-space hint points at the line, the floor holds, healthy passes.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="prove each refusal branch on planted workflows before trusting the gate",
    )
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    return validate(args.root.resolve())


if __name__ == "__main__":
    raise SystemExit(main())
