#!/usr/bin/env python3
"""Diagnostics-axes scoreboard.

Computes a deterministic, repo-derived metric for each of the ten orthogonal
axes along which the SIGIL diagnostics ("errors-as-API") subsystem improves.
See docs/DIAGNOSTIC_COVERAGE.md for the current definitions.

This is a DIRECTIONAL gauge and a regression guard. It is intentionally
regex-based and approximate — focused tests are the real proof of any single
improvement. Where
the heuristic is known to be coarse (e.g. phantom codes that appear only inside
string literals), that is documented inline and the loop refines via tests, not
by trusting this number.

Usage:
    python tools/diag_axes_scoreboard.py                 # print the table
    python tools/diag_axes_scoreboard.py --json          # emit JSON to stdout
    python tools/diag_axes_scoreboard.py --write-baseline # write tools/diag_axes_baseline.json
    python tools/diag_axes_scoreboard.py --check          # diff vs baseline; exit 1 if any metric regressed
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "tools" / "diag_axes_baseline.json"

CODES_RS = ROOT / "crates/sigil-compiler/src/diagnostics/codes.rs"
REGISTRY_RS = ROOT / "crates/sigil-compiler/src/diagnostics/registry.rs"
JSON_RS = ROOT / "crates/sigil-compiler/src/diagnostics/json.rs"
MCP_SRC = ROOT / "crates/sigil-mcp/src"
CLI_SRC = ROOT / "crates/sigil-cli/src"
COMPILER_SRC = ROOT / "crates/sigil-compiler/src"
SELFHOST_TC = ROOT / "selfhost/typecheck.sigil"
REGISTRY_WIRED = ROOT / "crates/sigil-compiler/tests/registry_wired.rs"
FIXTURES = ROOT / "crates/sigil-compiler/tests/fixtures"
BENCH_TASKS = ROOT / "bench/tasks"
BENCH_RUNS = ROOT / "bench/runs"
DOCS_ERRORS = ROOT / "docs/errors"

CODE_TOKEN = re.compile(r"\b([A-Z]\d{3})\b")
PASTEABLE = re.compile(r"`[^`]*(?:::|->|=>|fn |let |#\[|[;{}()\[\]<])[^`]*`")
PLACEHOLDER_ONLY = re.compile(r"^`<[^`]*>`$")


def read(p: Path) -> str:
    try:
        return p.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return ""


def all_src_rs(exclude: set[Path]) -> list[Path]:
    out: list[Path] = []
    for crate in (ROOT / "crates").glob("*/src"):
        for f in crate.rglob("*.rs"):
            if f.resolve() not in exclude:
                out.append(f)
    return out


def _declared_codes_from(text: str) -> list[str]:
    """Extract live diagnostic identifiers from catalog rows."""
    live = "\n".join(
        line for line in text.splitlines() if not line.lstrip().startswith("//")
    )
    return sorted(set(re.findall(r"\bcode:\s*([A-Z]\d{3})\s*,", live)))


def declared_codes() -> list[str]:
    # The registry catalog generates both constants and metadata, so its code
    # fields are the canonical declaration surface.
    return _declared_codes_from(read(REGISTRY_RS))


def registry_hints() -> list[str]:
    """Extract every default_hint string literal from the CODES table."""
    text = read(REGISTRY_RS)
    return re.findall(r'default_hint:\s*"((?:[^"\\]|\\.)*)"', text)


def dead_codes(declared: list[str]) -> list[str]:
    """Codes with no token reference in src outside codes.rs/registry.rs.

    Coarse: a code that appears only inside a string literal in src (e.g. a
    phantom referenced in a fallback message) is NOT flagged here. The loop
    treats this number as a floor on dead codes, not an exact count.
    """
    exclude = {CODES_RS.resolve(), REGISTRY_RS.resolve()}
    corpus = "\n".join(read(f) for f in all_src_rs(exclude))
    present = set(CODE_TOKEN.findall(corpus))
    return [c for c in declared if c not in present]


def count_in_dir(directory: Path, pattern: re.Pattern[str], exclude_names: set[str] = frozenset()) -> int:
    total = 0
    if not directory.exists():
        return 0
    for f in directory.rglob("*.rs"):
        if f.name in exclude_names:
            continue
        total += len(pattern.findall(read(f)))
    return total


def diagnosticjson_fields() -> list[str]:
    text = read(JSON_RS)
    m = re.search(r"pub struct DiagnosticJson\s*\{(.*?)\}", text, re.DOTALL)
    if not m:
        return []
    return re.findall(r"pub (\w+):", m.group(1))


def contains_any(directory: Path, needles: list[str]) -> bool:
    if not directory.exists():
        return False
    for f in directory.rglob("*"):
        if f.is_file():
            t = read(f)
            if any(n in t for n in needles):
                return True
    return False


def glob_count(directory: Path, pattern: str) -> int:
    return len(list(directory.glob(pattern))) if directory.exists() else 0


def has_complete_ab_run(runs_dir: Path = BENCH_RUNS) -> bool:
    """E7: a9 `bench_runs` credits ONLY a complete, LIVE A/B — both arms,
    K≥5 repeats, max_attempts≥5, a real model. A dry-run/stub, single-arm,
    partial, or underpowered run never moves a9. Scans for a
    `runs/*/ab_summary.json` (written by `sigil-bench compare`) meeting every
    bound. Parameterized on `runs_dir` so the self-test can exercise it."""
    if not runs_dir.exists():
        return False
    for summ in sorted(runs_dir.glob("*/ab_summary.json")):
        try:
            d = json.loads(summ.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        arms = {d.get("control_arm"), d.get("treatment_arm")}
        if (
            d.get("live") is True
            and d.get("arms_complete") is True
            and isinstance(d.get("repeats"), int)
            and d["repeats"] >= 5
            and isinstance(d.get("max_attempts"), int)
            and d["max_attempts"] >= 5
            and len(arms) == 2
            and None not in arms
        ):
            return True
    return False


def _expect_error_count(dir_: Path) -> int:
    """Count *.sigil files whose first non-comment annotation is `// expect-error:`
    (mirrors tests/diagnostic_precision.rs::parse_expect_error). Missing dir -> 0."""
    if not dir_.is_dir():
        return 0
    n = 0
    for f in sorted(dir_.glob("*.sigil")):
        for line in read(f).splitlines():
            t = line.strip()
            if t.startswith("// expect-error:"):
                n += 1
                break
            if t.startswith("// expect-ok") or t.startswith("// expect-shape"):
                break
            if t and not t.startswith("//"):
                break
    return n


def a10_precision_metrics() -> tuple[int, dict]:
    """a10 single-error precision: the static count of fixtures under precision
    enforcement (mirroring `tests/diagnostic_precision.rs`'s loader), debited by
    each allowlisted multi-error extra code so that widening the escape hatch
    LOWERS the metric (and trips `--check`). The compile-based enforcement is the
    Rust test; this is only its scoreboard credit (E10 couples them in CI)."""
    tests = ROOT / "crates/sigil-compiler/tests"
    test_src = read(tests / "diagnostic_precision.rs")
    sm = re.search(r"SENTINEL_EXCLUDED:\s*&\[&str\]\s*=\s*&\[(.*?)\];", test_src, re.DOTALL)
    sentinel = set(re.findall(r'"([^"]+)"', sm.group(1))) if sm else set()
    fixtures_by_name = [f.stem for f in FIXTURES.glob("*.sigil") if f.stem not in sentinel]
    cve = _expect_error_count(tests / "cve_corpus")
    precision = _expect_error_count(tests / "precision_corpus")
    z3 = _expect_error_count(tests / "z3_corpus")
    enforced = len(fixtures_by_name) + cve + precision + z3
    am = re.search(
        r"PRECISION_MULTI_ERROR:\s*&\[\(&str, &\[&str\], &str\)\]\s*=\s*&\[(.*?)\];",
        test_src,
        re.DOTALL,
    )
    allowlisted_extras = 0
    if am:
        for slice_body in re.findall(r"&\[(.*?)\]", am.group(1), re.DOTALL):
            allowlisted_extras += len(re.findall(r'"[^"]+"', slice_body))
    metric = enforced - allowlisted_extras
    total_sigil = sum(
        glob_count(tests / sub, "*.sigil")
        for sub in ("fixtures", "cve_corpus", "precision_corpus", "z3_corpus")
    )
    return metric, {
        "fixtures_by_filename": len(fixtures_by_name),
        "cve_expect_error": cve,
        "precision_corpus_expect_error": precision,
        "z3_expect_error": z3,
        "enforced": enforced,
        "allowlisted_extras": allowlisted_extras,
        "total_sigil_glob": total_sigil,
    }


def compute() -> dict:
    declared = declared_codes()
    hints = registry_hints()
    pasteable = [h for h in hints if PASTEABLE.search(h) and not PLACEHOLDER_ONLY.match(h.strip())]
    dead = dead_codes(declared)

    # A4: context-specific hint sites (excludes the constructor definition in mod.rs).
    ewh = count_in_dir(COMPILER_SRC, re.compile(r"error_with_hint\("), exclude_names={"mod.rs"})
    dym = count_in_dir(COMPILER_SRC, re.compile(r'did you mean'))

    baseline_payload = {"severity", "code", "title", "message", "hint", "doc_url", "location"}
    fields = diagnosticjson_fields()
    rich_fields = [f for f in fields if f not in baseline_payload]

    a5 = sum([
        contains_any(MCP_SRC, ["levenshtein", "closest", "did_you_mean", "suggest"]),
        contains_any(CLI_SRC, ['"explain"', "fn explain", "Explain"]),
        DOCS_ERRORS.exists() and glob_count(DOCS_ERRORS, "*") > 0,
    ])

    a6 = sum([
        contains_any(ROOT / "crates/sigil-compiler/tests", ["code_list_snapshot", "codes_golden", "code_list_golden"]),
        bool(re.search(r"\b(deprecated|status)\b", re.search(r"pub struct CodeEntry\s*\{(.*?)\}", read(REGISTRY_RS), re.DOTALL).group(1) if re.search(r"pub struct CodeEntry\s*\{(.*?)\}", read(REGISTRY_RS), re.DOTALL) else "")),
        "schema_version" in fields,
    ])

    rfc_match = re.search(r"REQUIRED_FIXTURE_CODES\b.*?=\s*&\[(.*?)\];", read(REGISTRY_WIRED), re.DOTALL)
    required_fixture_codes = len(re.findall(r'"[A-Z]\d{3}"', rfc_match.group(1))) if rfc_match else 0
    fixtures = glob_count(FIXTURES, "*.sigil")

    selfhost = read(SELFHOST_TC)
    a8_fields = 1  # bare code only is the baseline
    # Credit each distinct code that adopts the richer code+span payload (a8
    # parity BREADTH; differential-verified per ADOPTED_SPAN_CODES). Backward
    # compatible at the first adoption: 1 + 1(T120) == the old binary value 2.
    a8_span_codes = sorted(set(re.findall(r'tc_push_diag_with_span\(diags, "([A-Z]\d{3})"', selfhost)))
    a8_fields += len(a8_span_codes)
    if "doc_url" in selfhost:
        a8_fields += 1
    if re.search(r'tc_push_diag[^\n]*hint', selfhost) or "diag_hint" in selfhost:
        a8_fields += 1
    if re.search(r'tc_push_diag[^\n]*message', selfhost) or "diag_message" in selfhost:
        a8_fields += 1

    a9 = {
        "scoreboard_exists": (ROOT / "tools/diag_axes_scoreboard.py").exists(),
        "baseline_exists": BASELINE.exists(),
        "bench_runs": has_complete_ab_run(),
        "task_count": glob_count(BENCH_TASKS, "*.yaml") + glob_count(BENCH_TASKS, "*.yml"),
    }

    a10_metric, a10_detail = a10_precision_metrics()

    return {
        "a1_coverage": {
            "codes_declared": len(declared),
            "dead_codes_floor": len(dead),
            "dead_codes": dead,
            "_metric": len(declared) - len(dead),
        },
        "a2_payload_structure": {
            "diagnosticjson_fields": len(fields),
            "rich_fields": rich_fields,
            "_metric": len(rich_fields),
        },
        "a3_hint_actionability": {
            "hints_total": len(hints),
            "pasteable": len(pasteable),
            "fraction_pasteable": round(len(pasteable) / len(hints), 4) if hints else 0.0,
            "_metric": len(pasteable),
        },
        "a4_contextualization": {
            "error_with_hint_sites": ewh,
            "did_you_mean_sites": dym,
            "_metric": ewh,
        },
        "a5_resolvability": {
            "fuzzy_mcp_lookup": contains_any(MCP_SRC, ["levenshtein", "closest", "did_you_mean", "suggest"]),
            "explain_cmd": contains_any(CLI_SRC, ['"explain"', "fn explain", "Explain"]),
            "docs_pages": DOCS_ERRORS.exists() and glob_count(DOCS_ERRORS, "*") > 0,
            "_metric": a5,
        },
        "a6_stability_contract": {
            "golden_snapshot_test": contains_any(ROOT / "crates/sigil-compiler/tests", ["code_list_snapshot", "codes_golden", "code_list_golden"]),
            "per_message_schema_version": "schema_version" in fields,
            "_metric": a6,
        },
        "a7_enforcement_rigor": {
            "required_fixture_codes": required_fixture_codes,
            "fixtures_present": fixtures,
            "dead_codes_floor": len(dead),
            # Net enforcement: hard-required fixtures, debited by registered-but-
            # dead codes (AP11 holes). Removing a dead code now raises the metric.
            "_metric": required_fixture_codes - len(dead),
        },
        "a8_implementation_parity": {
            "selfhost_fields_emitted": a8_fields,
            "span_adopted_codes": a8_span_codes,
            "_metric": a8_fields,
        },
        "a9_measured_efficacy": {
            **a9,
            "_metric": int(a9["scoreboard_exists"]) + int(a9["baseline_exists"]) + int(a9["bench_runs"]),
        },
        "a10_single_error_precision": {
            **a10_detail,
            "_metric": a10_metric,
        },
    }


def print_table(data: dict) -> None:
    names = {
        "a1_coverage": "1 coverage",
        "a2_payload_structure": "2 payload structure",
        "a3_hint_actionability": "3 hint actionability",
        "a4_contextualization": "4 contextualization",
        "a5_resolvability": "5 resolvability",
        "a6_stability_contract": "6 stability contract",
        "a7_enforcement_rigor": "7 enforcement rigor",
        "a8_implementation_parity": "8 implementation parity",
        "a9_measured_efficacy": "9 measured efficacy",
        "a10_single_error_precision": "10 single-error precision",
    }
    print(f"{'axis':<26}{'metric':>8}   detail")
    print("-" * 72)
    for k, label in names.items():
        d = data[k]
        detail = ", ".join(f"{kk}={vv}" for kk, vv in d.items() if not kk.startswith("_") and kk != "dead_codes")
        print(f"{label:<26}{d['_metric']:>8}   {detail}")


def check_against_baseline(data: dict) -> int:
    if not BASELINE.exists():
        print("no baseline; run --write-baseline first", file=sys.stderr)
        return 2
    base = json.loads(read(BASELINE))
    regressed = []
    for axis, d in data.items():
        before = base.get(axis, {}).get("_metric")
        after = d["_metric"]
        if before is not None and after < before:
            regressed.append(f"{axis}: {before} -> {after}")
    if regressed:
        print("REGRESSION — axis metric(s) went down:", file=sys.stderr)
        for r in regressed:
            print(f"  {r}", file=sys.stderr)
        return 1
    print("ok: no axis metric regressed vs baseline")
    return 0


def self_test() -> int:
    """Local verification for the scoreboard's own logic (CI does not run tools/)."""
    failures = []
    # (a) catalog parsing counts live rows but not commented-out reservations.
    parsed = _declared_codes_from(
        """
        CodeEntry { code: S001, title: "live" },
        // CodeEntry { code: N010, title: "reserved" },
        """
    )
    if parsed != ["S001"]:
        failures.append(f"catalog parser did not isolate live codes: {parsed}")
    # (b) axis-7 nets dead codes: metric == required_fixture_codes - dead_codes_floor.
    a7 = compute()["a7_enforcement_rigor"]
    if a7["_metric"] != a7["required_fixture_codes"] - a7["dead_codes_floor"]:
        failures.append(f"a7 _metric != required - dead: {a7}")
    # (c) E7: a9 bench_runs counts ONLY a complete, live A/B — never a
    #     dry-run/stub, partial, single-arm, or underpowered run.
    import tempfile

    def _summ(**kw):
        base = {
            "live": True, "arms_complete": True, "repeats": 5, "max_attempts": 5,
            "control_arm": "bare", "treatment_arm": "full",
        }
        base.update(kw)
        return json.dumps(base)

    with tempfile.TemporaryDirectory() as td:
        runs = Path(td)
        for name, summ in (
            ("dry", _summ(live=False)),           # dry-run: not live
            ("partial", _summ(arms_complete=False)),  # not finished
            ("underK", _summ(repeats=3)),         # too few repeats
            ("underA", _summ(max_attempts=1)),    # attempt cap too low
            ("onearm", _summ(treatment_arm="bare")),  # single arm
        ):
            (runs / name).mkdir()
            (runs / name / "ab_summary.json").write_text(summ, encoding="utf-8")
        if has_complete_ab_run(runs):
            failures.append("E7: a dry-run/partial/underpowered/single-arm run flipped a9")
        (runs / "good").mkdir()
        (runs / "good" / "ab_summary.json").write_text(_summ(), encoding="utf-8")
        if not has_complete_ab_run(runs):
            failures.append("E7: a complete live A/B failed to flip a9 bench_runs")
    # (d) a10: the static credit must equal enforced - allowlisted (its own
    #     identity), must NOT collapse to the raw .sigil glob count (E1), and the
    #     axis key must make no soundness/recall claim (E6 — it is precision-only).
    a10 = compute()["a10_single_error_precision"]
    if a10["_metric"] != a10["enforced"] - a10["allowlisted_extras"]:
        failures.append(f"a10 _metric != enforced - allowlisted: {a10}")
    if a10["_metric"] == a10["total_sigil_glob"]:
        failures.append("a10 _metric equals the raw .sigil glob count (must credit only enforced fixtures)")
    if any(w in "a10_single_error_precision" for w in ("soundness", "correctness", "recall")):
        failures.append("a10 axis key overclaims precision as soundness/correctness/recall")
    if failures:
        for msg in failures:
            print(f"self-test FAIL: {msg}", file=sys.stderr)
        return 1
    print("self-test ok: comment-aware declared_codes + a7 nets dead + E7 a9 gate + a10 precision credit")
    return 0


def main() -> int:
    data = compute()
    args = set(sys.argv[1:])
    if "--self-test" in args:
        return self_test()
    if "--json" in args:
        print(json.dumps(data, indent=2, sort_keys=True))
        return 0
    if "--write-baseline" in args:
        BASELINE.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote {BASELINE.relative_to(ROOT)}")
        print_table(data)
        return 0
    if "--check" in args:
        return check_against_baseline(data)
    print_table(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
