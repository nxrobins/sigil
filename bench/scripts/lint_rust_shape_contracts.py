"""Lint Rust source-shape contracts that are enforced by CI."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
COMPILER_SRC = REPO_ROOT / "crates" / "sigil-compiler" / "src"
DIAGNOSTIC_TESTS = (
    REPO_ROOT / "crates" / "sigil-compiler" / "tests" / "diagnostic_messages.rs"
)

_TYPED_EXPR_OPEN = re.compile(r"(?<![A-Za-z0-9_:])TypedExpr\s*\{")
_REST_PATTERN = re.compile(r"\.\.\s*[A-Za-z_]")
_DIAGNOSTIC_CASE = re.compile(
    r"^    RefinementDiagnosticCase \{\n(?P<body>.*?)^    \},$",
    re.MULTILINE | re.DOTALL,
)
_CASE_LABEL = re.compile(r'^\s*label:\s*"([^"]+)",$', re.MULTILINE)
_CASE_SOLVER = re.compile(r"^\s*requires_solver:\s*(true|false),$", re.MULTILINE)
_CASE_FRAGMENTS = re.compile(
    r"evidence:\s*RefinementDiagnosticEvidence::(?:MessageShape|T226UnsupportedShape)"
    r"\(&\[(.*?)\]\)",
    re.DOTALL,
)
_QUOTED_FRAGMENT = re.compile(r'"([^"]*)"')
_SOLVER_GATED_RUNNER = re.compile(
    r'#\[cfg\(feature\s*=\s*"solver"\)\]\s*\n'
    r"\s*#\[test\]\s*\n\s*fn refinement_diagnostic_case_manifest\(",
)

_REQUIRED_DIAGNOSTIC_CASES = frozenset(
    {
        "t217_lengthof_non_array_message_names_field_and_type",
        "t220_variant_refinement_violation_names_variant",
        "t221_cross_variant_field_reference_names_variant",
        "t222_non_i64_variant_payload_names_field_and_type",
        "t223_subcase_1_positional_with_refinement",
        "t223_subcase_2_mixed_named_positional",
        "t223_subcase_3_duplicate_named_field",
        "t223_subcase_4_zero_payload_with_refinement",
        "t224_call_site_violation_names_function_and_param",
        "t225_return_refinement_violation_names_predicate",
        "t226_subcase_1_generic_function",
        "t226_subcase_2_no_return_type",
        "t224_does_not_fire_with_t225",
        "t225_does_not_fire_with_t226",
        "t226_does_not_fire_with_t224",
    }
)


def _balanced_body(text: str, open_brace: int) -> str | None:
    """Return the text inside a balanced brace pair, or None if unclosed."""
    depth = 1
    cursor = open_brace + 1
    while cursor < len(text):
        if text[cursor] == "{":
            depth += 1
        elif text[cursor] == "}":
            depth -= 1
            if depth == 0:
                return text[open_brace + 1 : cursor]
        cursor += 1
    return None


def typed_expr_rest_lines(text: str) -> list[int]:
    lines: list[int] = []
    for match in _TYPED_EXPR_OPEN.finditer(text):
        body = _balanced_body(text, match.end() - 1)
        if body is not None and _REST_PATTERN.search(body):
            lines.append(text[: match.start()].count("\n") + 1)
    return lines


def typed_expr_rest_violations(root: Path) -> list[tuple[Path, int]]:
    return [
        (path, line)
        for path in sorted(root.rglob("*.rs"))
        for line in typed_expr_rest_lines(path.read_text(encoding="utf-8"))
    ]


def diagnostic_manifest_cases(text: str) -> list[tuple[str, bool, tuple[str, ...]]]:
    try:
        manifest = text.split("// BEGIN NF_S7_DIAGNOSTIC_MANIFEST", 1)[1].split(
            "// END NF_S7_DIAGNOSTIC_MANIFEST", 1
        )[0]
    except IndexError:
        return []

    cases = []
    for match in _DIAGNOSTIC_CASE.finditer(manifest):
        body = match.group("body")
        label = _CASE_LABEL.search(body)
        solver = _CASE_SOLVER.search(body)
        fragments = _CASE_FRAGMENTS.search(body)
        if not all((label, solver)):
            continue
        cases.append(
            (
                label.group(1),
                solver.group(1) == "true",
                tuple(_QUOTED_FRAGMENT.findall(fragments.group(1)))
                if fragments
                else (),
            )
        )
    return cases


def diagnostic_backtick_violations(
    cases: list[tuple[str, bool, tuple[str, ...]]],
) -> list[tuple[str, str]]:
    return [
        (label, fragment)
        for label, _, fragments in cases
        for fragment in fragments
        if fragment.isdigit()
    ]


def diagnostic_subcase_counts(
    cases: list[tuple[str, bool, tuple[str, ...]]],
) -> tuple[int, int]:
    labels = [label for label, _, _ in cases]
    return (
        sum(label.startswith("t223_subcase_") for label in labels),
        sum(label.startswith("t226_subcase_") for label in labels),
    )


def solver_gated_diagnostic_cases(
    cases: list[tuple[str, bool, tuple[str, ...]]],
) -> list[str]:
    return [
        label
        for label, requires_solver, _ in cases
        if requires_solver and label.startswith(("t223_subcase_", "t226_subcase_"))
    ]


def _display_path(path: Path) -> Path:
    try:
        return path.relative_to(REPO_ROOT)
    except ValueError:
        return path


def _run_typed_expr_rest(root: Path) -> int:
    violations = typed_expr_rest_violations(root)
    if not violations:
        return 0
    print("V24 contract violation: rest-pattern `..` found in TypedExpr initializers:")
    for path, line in violations:
        print(f"  {_display_path(path)}:{line}")
    return 1


def _run_diagnostic_tests(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    cases = diagnostic_manifest_cases(text)
    labels = {label for label, _, _ in cases}

    if labels != _REQUIRED_DIAGNOSTIC_CASES:
        print(
            "NF-S7 manifest violation: semantic case inventory changed:",
            file=sys.stderr,
        )
        for label in sorted(_REQUIRED_DIAGNOSTIC_CASES - labels):
            print(f"  missing: {label}", file=sys.stderr)
        for label in sorted(labels - _REQUIRED_DIAGNOSTIC_CASES):
            print(f"  unexpected: {label}", file=sys.stderr)
        return 1
    if len(cases) != len(labels):
        print("NF-S7 manifest violation: duplicate case labels", file=sys.stderr)
        return 1
    print(f"NF-S7 manifest clean: {len(cases)} semantic cases pinned.")

    backtick_violations = diagnostic_backtick_violations(cases)
    if backtick_violations:
        print(
            "NF-S7-1 violation: message fragments pin bare digits without backticks:",
            file=sys.stderr,
        )
        for label, digit in backtick_violations:
            print(f'  {label}: use "`{digit}`" instead of "{digit}"', file=sys.stderr)
        return 1
    print(
        "NF-S7-1 lint clean: all T217-T226 manifest cases use "
        "backtick-quoted format pinning."
    )

    t223_count, t226_count = diagnostic_subcase_counts(cases)
    if t223_count != 4:
        print(
            "NF-S7-3 violation: T223 must have exactly 4 semantic cases; "
            f"found {t223_count}",
            file=sys.stderr,
        )
        return 1
    if t226_count != 2:
        print(
            "NF-S7-4 violation: T226 must have exactly 2 semantic cases; "
            f"found {t226_count}",
            file=sys.stderr,
        )
        return 1
    print("NF-S7-3/4 lint clean: T223 has 4 cases, T226 has 2 cases.")

    solver_gated = solver_gated_diagnostic_cases(cases)
    runner_solver_gated = bool(_SOLVER_GATED_RUNNER.search(text))
    if solver_gated or runner_solver_gated:
        print(
            "NF-S7-5 violation: T223/T226 cases and their runner must not be "
            'gated behind `#[cfg(feature = "solver")]`:',
            file=sys.stderr,
        )
        for label in solver_gated:
            print(f"  {label}", file=sys.stderr)
        if runner_solver_gated:
            print("  refinement_diagnostic_case_manifest", file=sys.stderr)
        return 1
    print("NF-S7-5 lint clean: T223/T226 evidence is not solver-gated.")
    return 0


def _run_self_test() -> int:
    manifest = """
// BEGIN NF_S7_DIAGNOSTIC_MANIFEST
    RefinementDiagnosticCase {
        label: "t217_bad",
        code: "T217",
        evidence: RefinementDiagnosticEvidence::MessageShape(&["1"]),
        requires_solver: false,
    },
// END NF_S7_DIAGNOSTIC_MANIFEST
"""
    parsed = diagnostic_manifest_cases(manifest)
    subcases = [
        *((f"t223_subcase_{index}_case", False, ()) for index in range(1, 5)),
        *((f"t226_subcase_{index}_case", False, ()) for index in range(1, 3)),
    ]
    checks = (
        typed_expr_rest_lines("let x = TypedExpr { value: 1, ..prior };\n") == [1],
        typed_expr_rest_lines("let x = TypedExpr { value: Other { inner: 1 } };\n")
        == [],
        parsed == [("t217_bad", False, ("1",))],
        diagnostic_backtick_violations(parsed) == [("t217_bad", "1")],
        diagnostic_subcase_counts(subcases) == (4, 2),
        solver_gated_diagnostic_cases([("t223_subcase_bad", True, ())])
        == ["t223_subcase_bad"],
        bool(
            _SOLVER_GATED_RUNNER.search(
                '#[cfg(feature = "solver")]\n#[test]\n'
                "fn refinement_diagnostic_case_manifest() {}\n"
            )
        ),
    )
    if not all(checks):
        print("shape-contract lint self-test failed", file=sys.stderr)
        return 2
    print("shape-contract lint self-test passed")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "contract",
        choices=("self-test", "typed-expr-rest", "diagnostic-tests"),
    )
    parser.add_argument("--path", type=Path)
    args = parser.parse_args(argv)

    if args.contract == "self-test":
        return _run_self_test()
    path = args.path
    if path is None:
        path = COMPILER_SRC if args.contract == "typed-expr-rest" else DIAGNOSTIC_TESTS
    try:
        if args.contract == "typed-expr-rest":
            if not path.is_dir():
                raise NotADirectoryError(path)
            return _run_typed_expr_rest(path)
        if not path.is_file():
            raise FileNotFoundError(path)
        return _run_diagnostic_tests(path)
    except (OSError, UnicodeDecodeError) as error:
        print(f"shape-contract lint could not read `{path}`: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
