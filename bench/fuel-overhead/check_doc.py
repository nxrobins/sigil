#!/usr/bin/env python3
"""Re-derive PERFORMANCE.md's fuel-overhead tables from the committed samples.

PERFORMANCE.md's "Fuel-instrumentation runtime overhead" section quotes numbers
that are read from bench/fuel-overhead/<run>/samples.tsv, host_state.json and
summary.md. This script recomputes every one of them under the HARNESS's rule —
the rule fuel_overhead.rs applies when it writes summary.md — and checks that
(1) each run's summary.md per-block rows equal the recomputation to the digit
and (2) every table and every scalar the document quotes appears in
PERFORMANCE.md verbatim EXACTLY its expected number of times: a number the
document repeats is pinned at every occurrence, so a stale duplicate fails as
surely as a wrong one. There is one rule, so the document and the data it
links cannot disagree in the last digit again:

    median = sorted[round((n - 1) * 0.5)]     (Rust f64::round: half away from 0)
    P90    = sorted[round((n - 1) * 0.9)]
    CV     = sample standard deviation (n - 1) / mean, over all of a block's samples
    µs     = ns / 1000, printed with one decimal; ratios two decimals; A′/A three

Derived quantities are taken on NET values (a condition's statistic minus that
same condition's L=0 statistic) from the raw nanosecond statistics, never from
the rounded µs the tables print.

Bounds are rounded so that no printed bound sits below the value it bounds:
a "within X %" bound is the largest deviation rounded UP to the next tenth of
a percent (0.703 % → "within 0.8 %", never 0.7), an "under N %" bound to the
next whole percent; a range or a single value is rounded to the printed
precision.

Two clocks are in the record. The HEADLINE (absolute figures) is the full-clock
run; the five earlier 2026-09-30 runs, taken while host_state.json recorded a
capped clock, are the REPEATABILITY set and are compared with their own capped
reference, never with the headline. The clock-scaling statements compare the
two sets; every percentage in them is computed here.

What is NOT recomputed is listed, with its provenance, in SOURCE_CONSTANTS and
the SESSION_LOG_CONSTANTS lists below: settings read from the harness and
runtime source, the tool's shape, and the 2026-09-20 session's runner figures
that no committed file records. Those are pinned verbatim (so they cannot drift
silently) but are not derived from any sample.

    python bench/fuel-overhead/check_doc.py             # check PERFORMANCE.md
    python bench/fuel-overhead/check_doc.py --emit      # print the tables and pins to paste
    python bench/fuel-overhead/check_doc.py --self-test # prove the check can fail

Failure direction: any summary.md row that differs from the recomputation, any
run whose inputs, seed, module digests or recorded clock differ from what the
document states, any table or scalar whose occurrence count in PERFORMANCE.md
is not the expected one, and a self-test in which a planted change goes
undetected all exit non-zero and name the cell.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
DOC = REPO_ROOT / "PERFORMANCE.md"

CONDS = ["A", "B", "C", "D", "A'", "B'"]
PRIME = {"A'": "A′", "B'": "B′"}  # the document prints the typographic prime
LENGTHS = [0, 100, 500, 1000]
HEADLINE = ("headline", "2026-09-30-idle-fullclock")
CAPPED_RUNS = [
    ("capped reference", "2026-09-30-idle"),
    ("repeat 2", "2026-09-30-idle-repeat2"),
    ("repeat 3", "2026-09-30-idle-repeat3"),
    ("review 4", "2026-09-30-idle-review4"),
    ("review 5", "2026-09-30-idle-review5"),
]
CONTENDED = "2026-09-20-contended"
CV_CONVERGED, CV_DROP = 5.0, 20.0  # the harness's flag thresholds
LONG = (500, 1000)  # the rows the document quotes from
RATIO_KEYS = ["A/C", "B/C", "D/C", "B'/B"]
NET_KEYS = ["(A-B)/L2", "(B-C)/L2", "(A-B)/fuel", "C/L2"]
LABEL = {
    "A/C": "A/C",
    "B/C": "B/C",
    "D/C": "D/C",
    "(A-B)/L2": "(A−B)/L²",
    "(B-C)/L2": "(B−C)/L²",
    "(A-B)/fuel": "(A−B)/fuel",
    "C/L2": "C net / L²",
    "A'/A": "A′/A",
    "B'/B": "B′/B",
}
WORDS = ["none", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve"]

# How many times each pinned scalar must appear (section scalars: in the
# section; doc-wide scalars: in the whole document). Every scalar not named
# here appears exactly once. A name here that no emitted scalar carries is an
# error, so a renamed pin cannot leave a stale count behind.
OCCURRENCES = {
    # "3504 of 3504 MHz": the Results paragraph, the headline sentence that
    # names the full clock as the reason, and the clock bullet.
    "headline clock": 3,
    # "3203 of 3504 MHz": the Results paragraph and the clock bullet.
    "capped clock": 2,
    # The L ≥ 500 median-over-minimum bound: the convergence paragraph, the
    # quoting rule and the contended run's closing sentence.
    "largest gap at L ≥ 500": 3,
    # The harness's flag legend under both median tables.
    "harness flag bands": 2,
    # The runner's admission window, in Environment and in the caveats.
    "runner window (environment, caveats)": 2,
    # The within-process CV bounds, in the section and in the caveats.
    "idle CV bound at L ≥ 500": 2,
    "idle blocks over 5 % at L ≥ 500": 2,
}

# Quoted verbatim from the harness or runtime SOURCE, or from the tool: not
# derived from any sample. (name, text, where the number comes from.)
SOURCE_CONSTANTS = [
    ("tool shape", "five direct calls per DP cell (`read_u32` ×3, `min3`, `write_u32`)", "tools/task098_levenshtein_distance.sigil, read by hand"),
    ("tool calls per cell", "at six calls per cell", "the five direct calls above plus the loop back-edge, each a fuel_decrement: tools/task098_levenshtein_distance.sigil, read by hand"),
    ("tool self-check", "`kitten\\nsitting` → `3`", "the Levenshtein distance the harness asserts before timing (fuel_overhead.rs)"),
    ("backstop cap", "a 10^10-unit cap", "execute_ephemeral's consume_fuel budget, crates/sigil-runtime/src/ephemeral.rs"),
    ("CLI default budget", "the CLI's default 100,000", "sigil forge's default fuel budget, crates/sigil-cli"),
    ("memory wall", "same 16 MB wall", "ephemeral.rs"),
    ("host closures", "registers 23 host closures", "`.func_wrap(` call sites in ephemeral.rs, --no-default-features"),
    ("sigil imports", "the 9 `sigil.*` imports", "ephemeral.rs"),
    ("ffi shims", "the 14 `ffi.*` shims", "link_ffi_imports in ephemeral.rs"),
    ("grant-cloning shims", "twelve of which clone the grants", "`grants.clone()` sites inside link_ffi_imports, ephemeral.rs: 13, minus grants_for_z3's under cfg(feature = \"solver\") = 12 with --no-default-features"),
    ("solver closures", "`ffi.z3_check` for 24", "ephemeral.rs with --features solver"),
    ("statistics rule", "median = sorted[round((n−1)/2)], P90 = sorted[round(0.9 (n−1))]", "fn percentile in fuel_overhead.rs; stats() below mirrors it"),
]

# The 2026-09-20 run's runner figures. Only its summary.md is committed (it
# records the resting-load range and the wall time, both derived below); the
# rest of that paragraph comes from the session's scratch-runner log, which is
# not in the repository, and the document says so. Pinned so they cannot be
# edited silently; verifiable against nothing here. A `{wall_s}` placeholder is
# the run's wall time, filled in by session_log_scalars from the summary.md
# header — the source of "contended: wall time" — never written a second time
# here, so the two copies the section carries cannot disagree.
SESSION_LOG_CONSTANTS = [
    ("09-20 other sessions", "three other agent sessions", "2026-09-20 session log (not in the repository)"),
    ("09-20 runner gate", "waited for 5 s under 25 %", "2026-09-20 session log (not in the repository)"),
    ("09-20 attempt", "the published attempt (18 of 18)", "2026-09-20 session log (not in the repository)"),
    ("09-20 during-run load", "during-run load mean 24.1 %, max 50.4 %", "2026-09-20 session log (not in the repository)"),
    ("09-20 rustc alive", "alive for 49 of its {wall_s} s", "2026-09-20 session log (not in the repository); the wall time from the run's summary.md header"),
]

# The one session-log figure the document repeats OUTSIDE the section:
# Methodology restates the 2026-09-20 scratch runner's admission gate. Pinned
# over the whole document together with its provenance label, so neither the
# figure nor the label can change or go silently.
SESSION_LOG_CONSTANTS_DOC_WIDE = [
    ("09-20 runner gate (methodology)", "a 5 s window under 25 % — a figure from that session's scratch-runner log, which is not in the repository", "2026-09-20 session log (not in the repository)"),
]


def word(n: int) -> str:
    return WORDS[n] if 0 <= n < len(WORDS) else str(n)


def times(n: int) -> str:
    """'once', 'twice', 'three times', …: how the document counts repetitions."""
    return {1: "once", 2: "twice"}.get(n, f"{word(n)} times")


def rround(x: float) -> int:
    """Rust `f64::round`: half away from zero (Python's round is half-even)."""
    return int(math.floor(x + 0.5)) if x >= 0 else -int(math.floor(-x + 0.5))


def within(pct: float) -> str:
    """A 'within X %' bound: the value rounded UP to the next tenth of a percent.

    Round-half .1f would print 0.703 % as "0.7 %", a bound below the value it
    bounds; this prints "0.8". The tiny slack keeps a value that already sits
    on a tenth (1.3000000004 from float arithmetic) from being pushed to 1.4.
    """
    return f"{math.ceil(round(pct * 10, 6)) / 10:.1f}"


def under(pct: float) -> int:
    """An 'under N %' bound: the next whole percent above the value."""
    return int(pct) + 1


def load_samples(run: str) -> dict[tuple[str, int], dict]:
    blocks: dict[tuple[str, int], dict] = {}
    for line in (HERE / run / "samples.tsv").read_text(encoding="utf-8").splitlines():
        if line.startswith("#") or line.startswith("block"):
            continue
        cols = line.split("\t")
        cond, length, n, fuel = cols[1], int(cols[4]), int(cols[5]), int(cols[7])
        samples = [int(x) for x in cols[8].split(" ")]
        if len(samples) != n:
            sys.exit(f"{run}: block {cond} L={length} declares n={n} but has {len(samples)} samples")
        blocks[(cond, length)] = {"fuel": fuel, "s": samples}
    if set(blocks) != {(c, length) for c in CONDS for length in LENGTHS}:
        sys.exit(f"{run}: samples.tsv does not hold exactly the 24 expected blocks")
    return blocks


def load_host(run: str) -> dict:
    """The runner's record: idle window, during-run load, and the clock it saw.

    The clock is psutil's cpu_freq (WMI CurrentClockSpeed on Windows), recorded
    before the idle check and after the run; the two must agree or the run's
    clock is not one number and the document may not quote it as one.
    """
    h = json.loads((HERE / run / "host_state.json").read_text(encoding="utf-8"))
    before, after = h["host"]["cpu_freq_mhz_before_idle_check"], h["host"]["cpu_freq_mhz_after_run"]
    if before != after:
        sys.exit(f"{run}: cpu_freq before {before} != after {after}; the run has no single recorded clock")
    thr = h["thresholds"]
    return {
        "idle_mean": h["idle_window_accepted"]["mean_pct"],
        "idle_max": h["idle_window_accepted"]["max_pct"],
        "idle_s": h["idle_window_accepted"]["seconds"],
        "run_mean": h["during_run"]["mean_pct"],
        "run_max": h["during_run"]["max_pct"],
        "wall_s": h["during_run"]["wall_s"],
        "over_15": h["during_run"]["samples_over_15_pct"],
        "n_samples": h["during_run"]["n_samples"],
        "procs": h["during_run"]["compiler_procs_seen"],
        "mhz": int(before["current"]),
        "mhz_max": int(before["max"]),
        "logical": int(h["host"]["logical_cpus"]),
        "sha256": h["harness"]["sha256"],
        "exit": h["harness"]["exit_code"],
        "started": h["started_utc"],  # ISO-8601, UTC
        # The admission thresholds the runner USED, so a relaxed run cannot
        # pass as strict: (window seconds, mean below, peak below). The
        # patience setting is kept apart: the reviewer's runs passed
        # --max-wait 300 (README), which admits nothing a default run refuses.
        "thresholds": (int(thr["idle_seconds"]), float(thr["idle_mean_pct_below"]), float(thr["idle_max_pct_below"])),
        "max_wait_s": int(thr["max_wait_s"]),
    }


def hhmm(iso: str) -> str:
    """'2026-09-30T14:11:08+00:00' → '14:11'."""
    return iso[11:16]


def check_inputs(runs: list[str]) -> list[str]:
    """Every run must have timed the same bytes: input_L*.txt digests equal per L."""
    errors = []
    for length in LENGTHS:
        digests = {run: hashlib.sha256((HERE / run / f"input_L{length}.txt").read_bytes()).hexdigest() for run in runs}
        if len(set(digests.values())) != 1:
            errors.append(f"input_L{length}.txt differs between runs: {digests}")
    return errors


def module_facts(run: str) -> dict:
    """What the harness recorded about the modules and its own settings, from summary.md.

    A0's size and digest, A1's re-encoding census, the seed, the lengths and the
    convergence rule are the harness's own record of what it timed; the
    document quotes them, so they are read here rather than trusted.
    """
    lines = (HERE / run / "summary.md").read_text(encoding="utf-8").splitlines()
    a0 = next(line for line in lines if line.startswith("- A0: "))
    a1 = next(line for line in lines if line.startswith("- A1: "))
    harness = next(line for line in lines if line.startswith("Harness "))
    m0 = re.match(r"- A0: (\d+) bytes, sha256 `([0-9a-f]{64})`.*?imports: (.*)\.$", a0)
    m1 = re.search(r"(\d+) `call 0` sites replaced by `drop`.*?(\d+) non-code sections copied byte-for-byte", a1)
    mh = re.search(r"seed (\d+)", harness)
    ml = re.search(r"lengths \[([^\]]+)\]", harness)
    mc = re.search(r"convergence trailing-(\d+) CV < (\d+)% or (\d+) samples", harness)
    if not (m0 and m1 and mh and ml and mc):
        sys.exit(f"{run}: summary.md does not carry the A0/A1/Harness lines in the expected form")
    return {
        "a0_bytes": int(m0.group(1)),
        "a0_sha": m0.group(2),
        "imports": [x.strip() for x in m0.group(3).split(",")],
        "call_sites": int(m1.group(1)),
        "sections": int(m1.group(2)),
        "seed": int(mh.group(1)),
        "lengths": [int(x) for x in ml.group(1).split(",")],
        "trailing": int(mc.group(1)),
        "cv": float(mc.group(2)),
        "ceiling": int(mc.group(3)),
    }


def contended_header() -> dict:
    """The 2026-09-20 summary.md's own record: its resting-load range and wall time."""
    text = (HERE / CONTENDED / "summary.md").read_text(encoding="utf-8")
    m_load = re.search(r"resting load (\S+?)%", text)
    m_wall = re.search(r"wall time (\d+) s", text)
    if not (m_load and m_wall):
        sys.exit(f"{CONTENDED}: summary.md does not record the resting load and wall time")
    return {"resting": m_load.group(1), "wall_s": int(m_wall.group(1))}


def stats(samples: list[int]) -> dict:
    srt = sorted(samples)
    n = len(srt)
    mean = sum(srt) / n
    var = sum((x - mean) ** 2 for x in srt) / (n - 1) if n > 1 else 0.0
    return {
        "n": n,
        "min": srt[0],
        "max": srt[-1],
        "med": srt[min(n - 1, rround((n - 1) * 0.5))],
        "p90": srt[min(n - 1, rround((n - 1) * 0.9))],
        "cv": math.sqrt(var) / mean * 100 if mean else 0.0,
    }


def flag(cv: float) -> str:
    return "✓" if cv < CV_CONVERGED else ("⚠" if cv < CV_DROP else "✗")


def us(ns: float) -> str:
    return f"{ns / 1000.0:.1f}"


def dev(a: float, b: float) -> float:
    """Percent deviation of a from b."""
    return (a / b - 1) * 100


def rng(values: list[float], fmt: str) -> str:
    """'lo–hi' in fmt, or one value when both print alike."""
    lo, hi = fmt.format(min(values)), fmt.format(max(values))
    return lo if lo == hi else f"{lo}–{hi}"


def derived(blocks: dict, key: str) -> dict[int, dict]:
    """Net derived quantities per L ≥ 100 on `key` ('min' or 'med'), from raw ns."""
    stat = {k: stats(b["s"])[key] for k, b in blocks.items()}
    out: dict[int, dict] = {}
    for length in LENGTHS[1:]:
        net = {c: stat[(c, length)] - stat[(c, 0)] for c in CONDS}
        cells = length * length
        fuel = blocks[("A", length)]["fuel"]
        out[length] = {
            "A/C": net["A"] / net["C"],
            "B/C": net["B"] / net["C"],
            "D/C": net["D"] / net["C"],
            "(A-B)/L2": (net["A"] - net["B"]) / cells,
            "(B-C)/L2": (net["B"] - net["C"]) / cells,
            "(A-B)/fuel": (net["A"] - net["B"]) / fuel,
            "fuel": fuel,
            "A'/A": net["A'"] / net["A"],
            "B'/B": net["B'"] / net["B"],
            "C/L2": net["C"] / cells,
            "A/L2": net["A"] / cells,
            "(A-C)/L2": (net["A"] - net["C"]) / cells,
            "C net": net["C"],
        }
    return out


# --- summary.md agreement -----------------------------------------------------


def check_summary(run: str, blocks: dict) -> list[str]:
    """Every per-block row the harness wrote must equal the recomputation."""
    errors = []
    seen = 0
    for line in (HERE / run / "summary.md").read_text(encoding="utf-8").splitlines():
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) != 14 or cells[0] not in CONDS:
            continue
        seen += 1
        cond, length = cells[0], int(cells[4])
        st = stats(blocks[(cond, length)]["s"])
        want = [
            str(st["n"]),
            us(st["min"]),
            us(st["med"]),
            us(st["p90"]),
            us(st["max"]),
            f"{st['cv']:.1f}",
            flag(st["cv"]),
            str(blocks[(cond, length)]["fuel"]),
        ]
        got = [cells[5], cells[7], cells[8], cells[9], cells[10], cells[11], cells[12], cells[13]]
        if got != want:
            errors.append(f"{run} summary.md {cond} L={length}: summary {got} != recomputed {want}")
    if seen != 24:
        errors.append(f"{run} summary.md: expected 24 per-block rows, found {seen}")
    return errors


# --- the document's tables ----------------------------------------------------


def table(header: list[str], rows: list[list[str]], align: str) -> str:
    lines = ["| " + " | ".join(header) + " |", "|" + "|".join(align) + "|"]
    lines += ["| " + " | ".join(r) + " |" for r in rows]
    return "\n".join(lines)


def minima_table(blocks: dict) -> str:
    rows = [[str(length)] + [us(stats(blocks[(c, length)]["s"])["min"]) for c in CONDS] for length in LENGTHS]
    return table(["L"] + [PRIME.get(c, c) for c in CONDS], rows, ["---:"] * 7)


def medians_table_idle(blocks: dict) -> str:
    """Median with n, P90, CV and the harness's flag, so a ⚠ block is visible in the document."""
    rows = []
    for length in LENGTHS:
        cells = [str(length)]
        for c in CONDS:
            st = stats(blocks[(c, length)]["s"])
            cells.append(f"{us(st['med'])} ({st['n']}; {us(st['p90'])}; {st['cv']:.1f} {flag(st['cv'])})")
        rows.append(cells)
    return table(["L"] + [PRIME.get(c, c) for c in CONDS], rows, ["---:"] * 7)


def medians_table_contended(blocks: dict) -> str:
    rows = []
    for length in LENGTHS:
        cells = [str(length)]
        for c in CONDS:
            st = stats(blocks[(c, length)]["s"])
            cells.append(f"{us(st['med'])} ({st['n']} {flag(st['cv'])})")
        rows.append(cells)
    return table(["L"] + [PRIME.get(c, c) for c in CONDS], rows, ["---:"] * 7)


def derived_table(blocks: dict, key: str, with_fuel: bool) -> str:
    d = derived(blocks, key)
    header = ["L", "A/C", "B/C", "D/C", "(A−B)/L²", "(B−C)/L²", "(A−B)/fuel"]
    if with_fuel:
        header.append("fuel (A)")
    header += ["A′/A", "B′/B"]
    rows = []
    for length, r in d.items():
        row = [
            str(length),
            f"{r['A/C']:.2f}",
            f"{r['B/C']:.2f}",
            f"{r['D/C']:.2f}",
            f"{r['(A-B)/L2']:.1f} ns",
            f"{r['(B-C)/L2']:.1f} ns",
            f"{r['(A-B)/fuel']:.2f} ns",
        ]
        if with_fuel:
            row.append(f"{r['fuel']:,}")
        a_agree, b_agree = r["A'/A"], r["B'/B"]
        row += [f"{a_agree:.3f}", f"{b_agree:.3f}"]
        rows.append(row)
    return table(header, rows, ["---:"] * len(header))


def repeatability_table(runs: list[tuple[str, dict]]) -> str:
    ds = [derived(b, "min") for _, b in runs]
    quantities = [
        ("A/C", "A/C", "{:.2f}"),
        ("B/C", "B/C", "{:.2f}"),
        ("D/C", "D/C", "{:.2f}"),
        ("(A−B)/L²", "(A-B)/L2", "{:.1f} ns"),
        ("(B−C)/L²", "(B-C)/L2", "{:.1f} ns"),
        ("(A−B)/fuel", "(A-B)/fuel", "{:.2f} ns"),
        ("C net / L²", "C/L2", "{:.1f} ns"),
        ("A′/A", "A'/A", "{:.3f}"),
        ("B′/B", "B'/B", "{:.3f}"),
    ]
    rows = []
    for label, key, fmt in quantities:
        row = [label]
        for length in LONG:
            vals = [fmt.format(d[length][key]) for d in ds]
            if fmt.endswith(" ns"):  # one unit per cell, not one per value
                vals = [v[:-3] for v in vals]
                row.append(" / ".join(vals) + " ns")
            else:
                row.append(" / ".join(vals))
        rows.append(row)
    return table(["quantity", "L = 500", "L = 1000"], rows, ["---", "---", "---"])


def cold_calls(run: str) -> tuple[list[float], list[float], list[float]]:
    """(cold first calls, from_binary fuel off, from_binary fuel on), in µs, from summary.md."""
    cold, off, on = [], [], []
    section = None
    for line in (HERE / run / "summary.md").read_text(encoding="utf-8").splitlines():
        if line.startswith("## Cold first call"):
            section = "cold"
        elif line.startswith("Mirror `Module::from_binary`"):
            section = "bin"
        elif line.startswith("## "):
            section = None
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if section == "cold" and len(cells) == 3 and cells[0].isdigit():
            cold.append(float(cells[2]))
        elif section == "bin" and len(cells) == 3 and cells[1] in ("on", "off"):
            (on if cells[1] == "on" else off).append(float(cells[2]))
    if len(cold) != 6 or len(off) != 6 or len(on) != 6:
        sys.exit(f"{run}: expected 6 cold calls and 6+6 from_binary timings in summary.md")
    return cold, off, on


def flagged(blocks: dict) -> list[tuple[str, int, float, int]]:
    """Blocks the harness did not mark ✓, in table order: (cond, L, CV, n)."""
    out = []
    for length in LENGTHS:
        for c in CONDS:
            st = stats(blocks[(c, length)]["s"])
            if st["cv"] >= CV_CONVERGED:
                out.append((c, length, st["cv"], st["n"]))
    return out


# --- the document's prose numbers ---------------------------------------------


def module_scalars(facts: dict) -> list[tuple[str, str]]:
    """What the harness recorded about the modules and its settings, as the document words them."""
    lengths = ", ".join(str(x) for x in facts["lengths"])
    imports_ok = all(x.startswith("sigil.") for x in facts["imports"])
    return [
        ("A0 size and digest", f"{facts['a0_bytes']} bytes, sha256 `{facts['a0_sha'][:8]}…`"),
        ("A1 call sites", f"{facts['call_sites']} `call 0` sites"),
        ("A1 copied sections", f"the other {facts['sections']} sections are copied byte-for-byte"),
        # Fails closed by wording: a non-`sigil.*` import makes the emitted text one the document does not carry.
        ("A0 imports", f"imports only `sigil.*` ({word(len(facts['imports']))} of them)" if imports_ok else f"imports {', '.join(facts['imports'])}"),
        ("seed", f"seed `0x{facts['seed']:016x}`"),
        ("lengths", "L ∈ {" + lengths + "}"),
        ("convergence rule", f"(trailing-{facts['trailing']} CV < {facts['cv']:.0f} % or {facts['ceiling']} samples)"),
        ("sample ceiling", f"n = {facts['ceiling']} means the block hit the ceiling"),
        ("harness flag bands", f"✓ CV < {CV_CONVERGED:.0f} %, ⚠ < {CV_DROP:.0f} %"),
        # The contended legend's third band (the idle legend lists ✓ and ⚠ only).
        ("harness drop band", f"✗ ≥ {CV_DROP:.0f} %"),
        ("cold module size", f"the {rround(facts['a0_bytes'] / 1024)} KB module"),
    ]


def headline_scalars(head: dict, host: dict, facts: dict) -> list[tuple[str, str]]:
    """The full-clock run's own numbers: host state, convergence, per-cell costs, fixed and cold costs."""
    hs = {k: stats(b["s"]) for k, b in head.items()}
    d1000 = derived(head, "min")[1000]
    dmin, dmed = derived(head, "min"), derived(head, "med")
    cvs = [st["cv"] for st in hs.values()]
    gap = {k: (st["med"] - st["min"]) / st["min"] * 100 for k, st in hs.items()}
    gap_long = max(v for (_, length), v in gap.items() if length >= 500)
    fl = flagged(head)
    at_floor = sum(st["n"] == facts["trailing"] for st in hs.values())
    share = [hs[(c, 0)]["min"] / hs[(c, 100)]["min"] * 100 for c in CONDS]
    fuel_per_cell = {length: head[("A", length)]["fuel"] / (length * length) for length in LENGTHS[1:]}
    f100, f500, f1000 = (f"{fuel_per_cell[length]:.2f}" for length in LENGTHS[1:])
    # The document says "6.01 at L=500 and L=1000" only while both print alike;
    # otherwise the emitted text names both and the document must change.
    fuel_text = f"{f100} at L=100, {f500} at L=500 and L=1000" if f500 == f1000 else f"{f100} at L=100, {f500} at L=500, {f1000} at L=1000"
    decrement_share = d1000["(A-B)/L2"] / d1000["(A-C)/L2"] * 100
    out = [
        ("harness sha256 prefix", f"`{host['sha256'][:8]}…`"),
        ("headline start time", f"taken at {hhmm(host['started'])} UTC"),
        ("headline clock", f"{host['mhz']} of {host['mhz_max']} MHz"),
        # The reason the document gives for the headline choice must itself hold in the record.
        ("headline is the full clock", f"the one run whose recorded clock equals the processor's recorded maximum ({host['mhz']} of {host['mhz_max']} MHz)" if host["mhz"] == host["mhz_max"] else "NOT-AT-MAXIMUM"),
        ("headline idle window", f"{host['idle_s']} s window mean {host['idle_mean']:.1f} %, peak {host['idle_max']:.1f} %"),
        ("headline during-run load", f"during the {host['wall_s']:.0f} s run mean {host['run_mean']:.1f} %, peak {host['run_max']:.1f} %"),
        ("headline samples over threshold", "no sample at or above 15 %" if host["over_15"] == 0 else f"{host['over_15']} of {host['n_samples']} samples at or above 15 %"),
        ("headline blocks at the floor", f"{at_floor} of the 24 blocks converged at the {facts['trailing']}-sample floor"),
        ("headline flagged count", f"the other {word(len(fl))} ran to n = {min(n for *_, n in fl)}–{max(n for *_, n in fl)}"),
        ("headline flagged CV range", "closed with a CV of " + rng([cv for _, _, cv, _ in fl], "{:.1f}") + " %"),
        ("headline flagged list", "(" + ", ".join(f"{PRIME.get(c, c)}:L{length} {cv:.1f}" for c, length, cv, _ in fl) + ")"),
        ("headline flagged at L ≥ 500", f"{word(sum(1 for _, length, _, _ in fl if length >= 500))} of them at L ≥ 500"),
        ("headline CV range", f"Over all {len(hs)} blocks CV {min(cvs):.1f}–{max(cvs):.1f} %"),
        ("largest median-over-minimum gap", f"gap in any block is {max(gap.values()):.1f} %"),
        ("largest gap at L ≥ 500", f"{within(gap_long)} % at L ≥ 500"),
        ("gap bound in the quoting rule", f"the two statistics agree to {within(gap_long)} %"),
        ("L=100 subtraction share", f"{min(share):.0f}–{max(share):.0f} % of the value"),
        ("fuel per cell", f"fuel consumed ÷ L² = {fuel_text}"),
        ("decrements per cell, rounded", f"about {word(rround(fuel_per_cell[1000]))} host-call decrements per cell"),
        ("C net at L=1000", f"{d1000['C net'] / 1000:.0f} µs net over 10⁶ cells"),
        ("fuel-free per cell", f"costs {d1000['C/L2']:.1f} ns"),
        ("backstop per cell", f"adds {d1000['(B-C)/L2']:.1f} ns"),
        ("decrements per cell", f"add {d1000['(A-B)/L2']:.1f} ns"),
        ("per decrement", f"**{d1000['(A-B)/fuel']:.1f} ns per"),
        ("per decrement at the full clock", f"{d1000['(A-B)/fuel']:.1f} ns per decrement at the full clock"),
        ("metered cell total", f"costs {d1000['A/L2']:.1f} ns"),
        ("metered over fuel-free", f"**{d1000['A/L2'] / d1000['C/L2']:.1f}× the fuel-free time**"),
        ("metered over fuel-free, rounded", f"pays ~{d1000['A/C']:.0f}× for metering"),
        ("metering cost per cell", f"metering is {d1000['(A-C)/L2']:.1f} ns"),
        ("metering adds up", f"A − C = {d1000['(A-C)/L2']:.1f} ns ≈ {d1000['(A-B)/L2']:.1f} + {d1000['(B-C)/L2']:.1f}"),
        ("decrement share of metering", f"decrements are {decrement_share:.0f} % of the metering cost"),
        ("quotable ratios", f"({d1000['A/C']:.1f}×, {d1000['B/C']:.1f}×, {d1000['D/C']:.1f}×"),
        ("headline D/C range", "D/C = " + rng([dmin[length]["D/C"] for length in LONG], "{:.2f}")),
        ("headline B/C range", "B/C = " + rng([dmin[length]["B/C"] for length in LONG], "{:.2f}")),
        ("headline A′/A on minima", "A′/A is " + rng([dmin[length]["A'/A"] for length in LONG], "{:.3f}")),
        ("headline B′/B on minima", "B′/B " + rng([dmin[length]["B'/B"] for length in LONG], "{:.3f}") + " on net minima"),
        ("headline A′/A, B′/B on medians", rng([dmed[length]["A'/A"] for length in LONG], "{:.3f}") + " and " + rng([dmed[length]["B'/B"] for length in LONG], "{:.3f}") + " on net medians"),
        ("headline fixed cost shipped", rng([hs[(c, 0)]["min"] / 1000 for c in ("A", "B")], "{:.0f}") + " µs through `execute_ephemeral`"),
        ("headline fixed cost mirror", rng([hs[(c, 0)]["min"] / 1000 for c in ("C", "D", "A'", "B'")], "{:.0f}") + " µs on the mirror"),
    ]
    cold, off, on = cold_calls(HEADLINE[1])
    out.append(("headline cold first call", rng([x / 1000 for x in cold], "{:.1f}") + f" ms over its {len(cold)} calls"))
    out.append(("headline from_binary fuel off", rng([x / 1000 for x in off], "{:.1f}") + " ms with fuel off"))
    out.append(("headline from_binary fuel on", rng([x / 1000 for x in on], "{:.1f}") + " ms with fuel on"))
    return out


def idle_bounds(head: dict, capped: list[tuple[str, dict]]) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    """Within-process spread over all six idle runs: (section scalars, doc-wide scalars).

    The two CV bounds are stated in the section and again in the caveats, so
    they are pinned over the whole document at two occurrences each.
    """
    runs = [("full-clock", head)] + list(capped)
    cvs = [(stats(b["s"])["cv"], name, c, length) for name, blocks in runs for (c, length), b in blocks.items()]
    long = [x for x in cvs if x[3] >= 500]
    over_long = [x for x in long if x[0] >= CV_CONVERGED]
    over_long_capped = [x for x in over_long if x[1] != "full-clock"]
    if over_long_capped:
        sys.exit(f"a capped-clock run has a block over {CV_CONVERGED} % CV at L ≥ 500; the document's wording assumes none: {over_long_capped}")
    top = max(cvs)
    short_max = max(length for length in LENGTHS if length < LONG[0])
    # The document places the largest idle-run CV at L ≤ 100; if it ever moves
    # to a long row the emitted text names that row and the document fails.
    where = f"at L ≤ {short_max}" if top[3] <= short_max else f"at L = {top[3]}"
    section = [
        ("idle largest CV", f"{where} the largest CV in any idle-run block is {top[0]:.1f} % ({PRIME.get(top[2], top[2])} at L = {top[3]} in {top[1]})"),
    ]
    doc_wide = [
        ("idle CV bound at L ≥ 500", f"every block at L ≥ 500 has a CV under {under(max(x[0] for x in long))} %"),
        ("idle blocks over 5 % at L ≥ 500", f"under 5 % in all but {word(len(over_long))} blocks of the full-clock run"),
    ]
    return section, doc_wide


def executor_drifts(head: dict, capped: list[tuple[str, dict]]) -> list[tuple[str, str]]:
    """How many of the six idle runs show one executor sitting off the others.

    Within a run the shipped path and its mirror time the same module twice
    (A against A′, B against B′), so a drifted executor shows as that pair's
    net-minima ratio at L ≥ 500 sitting off 1 by at least CV_CONVERGED
    percent — the harness's own convergence band, the noise the document
    already accepts inside a block. The record separates cleanly: the two
    drifts the section names (the capped reference's A′, review 4's A) sit
    6–18 % off, every other pair under 1 %. A run with both pairs off would
    not be "one executor at a time"; the emitted text then says so and the
    document fails.
    """
    runs = [("full-clock", head)] + list(capped)
    drifted, both = [], []
    for name, blocks in runs:
        d = derived(blocks, "min")
        off = [pair for pair in ("A'/A", "B'/B") if max(abs(d[length][pair] - 1) * 100 for length in LONG) >= CV_CONVERGED]
        if off:
            drifted.append(name)
        if len(off) > 1:
            both.append(name)
    if both:
        return [("executor drifts", f"BOTH-PAIRS-OFF in {', '.join(both)}")]
    return [("executor drifts", f"{times(len(drifted))} in {word(len(runs))} runs")]


def capped_scalars(capped: list[tuple[str, dict]], hosts: dict[str, dict]) -> list[tuple[str, str]]:
    """The repeatability set: five capped-clock runs against their own capped reference."""
    by = dict(capped)
    ref, r4 = by["capped reference"], by["review 4"]
    dref = derived(ref, "min")
    mhz = {hosts[run]["mhz"] for _, run in CAPPED_RUNS}
    mhz_max = {hosts[run]["mhz_max"] for _, run in CAPPED_RUNS}
    if len(mhz) != 1 or len(mhz_max) != 1:
        sys.exit(f"the capped runs do not share one recorded clock: {mhz} of {mhz_max}")
    starts = sorted(hosts[run]["started"] for _, run in CAPPED_RUNS)
    ref_start = hosts[CAPPED_RUNS[0][1]]["started"]
    out = [
        ("capped clock", f"{mhz.pop()} of {mhz_max.pop()} MHz"),
        ("capped run window", f"between {hhmm(starts[0])} and {hhmm(starts[-1])} UTC"),
        # The reference is called the first of the set: true only while its start is the earliest.
        ("capped reference start", f"the first of the set, taken at {hhmm(ref_start)} UTC" if ref_start == starts[0] else "NOT-THE-FIRST-RUN"),
    ]
    # Convergence flags in the capped set, by run.
    fl = {name: flagged(b) for name, b in capped}
    others = [len(v) for name, v in fl.items() if name != "capped reference"]
    all_others = [x for name, v in fl.items() if name != "capped reference" for x in v]
    out.append(("capped reference flags", f"the capped-clock reference flagged {word(len(fl['capped reference']))} of its {len(ref)} blocks"))
    out.append(("capped other runs' flags", f"the other four flagged {min(others)}–{max(others)} blocks each, {sum(others)} in all, every one at L ≤ {max(length for _, length, _, _ in all_others)}"))
    # P1: repeats 2 and 3 and review 5 against the reference, every derived cell at L ≥ 500.
    worst = (0.0, "", 0, "")
    apa = []
    for name in ("repeat 2", "repeat 3", "review 5"):
        d = derived(by[name], "min")
        for length in LONG:
            for key in RATIO_KEYS + NET_KEYS + ["A'/A"]:
                x = dev(d[length][key], dref[length][key])
                if key == "A'/A":
                    apa.append(x)
                elif abs(x) > abs(worst[0]):
                    worst = (x, name, length, key)
    out.append(("P1 largest deviation except A′/A", f"every derived cell except A′/A within {under(abs(worst[0]))} % (largest {abs(worst[0]):.1f} %, {LABEL[worst[3]]} at L = {worst[2]} in {worst[1]})"))
    out.append(("P1 A′/A below reference", rng([-x for x in apa], "{:.1f}") + " % below it"))

    # P2: review 4's other blocks against the reference, by L, on minima and medians.
    def block_devs(conds: tuple, lengths: tuple) -> list[float]:
        return [
            dev(stats(r4[(c, length)]["s"])[key], stats(ref[(c, length)]["s"])[key])
            for c in conds
            for length in lengths
            for key in ("min", "med")
        ]

    others = ("B", "C", "D", "B'")
    worst_long = max(abs(x) for x in block_devs(others, LONG))
    out.append(("P2 review-4 other blocks at L ≥ 500", f"reproduced the reference within {within(worst_long)} % at L ≥ 500"))
    out.append(("P2 review-4 other blocks at L=100", "at L = 100 they were " + rng(block_devs(others, (100,)), "{:.1f}") + " % above it"))
    out.append(("P2 review-4 all blocks at L=0", "at L = 0 every one of the six blocks was " + rng(block_devs(tuple(CONDS), (0,)), "{:.0f}") + " % above it"))
    # The two drifts, as the document names them.
    a_ratio = [dev(stats(r4[("A", length)]["s"])["med"], stats(ref[("A", length)]["s"])["med"]) for length in LENGTHS[1:]]
    d4 = derived(r4, "min")
    out.append(("capped reference A′/A drift", "A′/A " + rng([dref[length]["A'/A"] for length in LENGTHS[1:]], "{:.2f}")))
    out.append(("capped reference A′ slower", rng([(dref[length]["A'/A"] - 1) * 100 for length in LENGTHS[1:]], "{:.0f}") + " % slower than the shipped path"))
    out.append(("capped reference A CV at L=1000", f"outside the {stats(ref[('A', 1000)]['s'])['cv']:.1f} % within-run CV"))
    out.append(("capped reference per decrement", f"{dref[1000]['(A-B)/fuel']:.1f} ns at the capped clock"))
    out.append(("review-4 A median offset", rng(a_ratio, "{:.1f}") + " % slower"))
    out.append(("review-4 L=1000 medians", f"{us(stats(r4[('A', 1000)]['s'])['med'])} vs {us(stats(ref[('A', 1000)]['s'])['med'])} µs"))
    out.append(("review-4 A/C at L=1000", f"A/C {d4[1000]['A/C']:.2f}"))
    out.append(("review-4 per cell", f"{d4[1000]['(A-B)/L2']:.1f} ns per cell"))
    out.append(("review-4 per decrement", rng([d4[length]["(A-B)/fuel"] for length in LONG], "{:.2f}") + " ns per decrement"))
    # The quoting consequence: four runs against one, at L ≥ 500.
    four = [derived(by[n], "min") for n in ("capped reference", "repeat 2", "repeat 3", "review 5")]
    out.append(("A/C in four runs", "A/C is " + rng([d[length]["A/C"] for d in four for length in LONG], "{:.2f}") + " in four runs and " + rng([d4[length]["A/C"] for length in LONG], "{:.2f}") + " in one"))
    out.append(("per-decrement in four runs", rng([d[length]["(A-B)/fuel"] for d in four for length in LONG], "{:.2f}") + " ns in four and " + rng([d4[length]["(A-B)/fuel"] for length in LONG], "{:.2f}") + " ns in one"))
    all5 = [derived(b, "min") for _, b in capped]
    out.append(("B/C in all five", "B/C (" + rng([d[length]["B/C"] for d in all5 for length in LONG], "{:.2f}") + ")"))
    out.append(("D/C in all five", "D/C (" + rng([d[length]["D/C"] for d in all5 for length in LONG], "{:.2f}") + ")"))
    out.append(("B′/B in all five", "B′/B is " + rng([d[length]["B'/B"] for d in all5 for length in LONG], "{:.3f}") + " at L ≥ 500 in all five"))
    # Fixed and cold costs across the capped set.
    shipped = [stats(b[(c, 0)]["s"])["min"] / 1000 for _, b in capped for c in ("A", "B")]
    mirror = [stats(b[(c, 0)]["s"])["min"] / 1000 for _, b in capped for c in ("C", "D", "A'", "B'")]
    out.append(("capped fixed cost", rng(shipped, "{:.0f}") + " µs and " + rng(mirror, "{:.0f}") + " µs in the five capped-clock runs"))
    # Which run carries the top of both fixed-cost ranges, on every executor.
    top = {
        name
        for name, b in capped
        if all(stats(b[(c, 0)]["s"])["min"] == max(stats(o[(c, 0)]["s"])["min"] for _, o in capped) for c in CONDS)
    }
    out.append(("capped fixed cost maximum", (top.pop() if len(top) == 1 else "NO-SINGLE-RUN") + " alone carries the top of both ranges, on every executor"))
    cold, off, on = [], [], []
    for _, run in CAPPED_RUNS:
        c, o, n = cold_calls(run)
        cold += c
        off += o
        on += n
    out.append(("capped cold first call", rng([x / 1000 for x in cold], "{:.1f}") + f" ms over the five capped-clock runs' {len(cold)} calls"))
    out.append(("capped from_binary", rng([x / 1000 for x in off], "{:.1f}") + " ms off / " + rng([x / 1000 for x in on], "{:.1f}") + " ms on"))
    return out


def net_factors(head: dict, capped: list[tuple[str, dict]]) -> list[float]:
    """Capped ÷ full-clock on every absolute net column at L ≥ 500, net minima,
    excluding review 4's two A-bearing cells (that run's A drift is stated apart)."""
    dh = derived(head, "min")
    out = []
    for name, blocks in capped:
        d = derived(blocks, "min")
        for length in LONG:
            for key in NET_KEYS:
                if not (name == "review 4" and key in ("(A-B)/L2", "(A-B)/fuel")):
                    out.append(d[length][key] / dh[length][key])
    return out


def clock_scalars(head: dict, capped: list[tuple[str, dict]], hosts: dict[str, dict], contended: dict) -> list[tuple[str, str]]:
    """What changed between the two clocks, and what did not, at L ≥ 500 on net minima."""
    dh = derived(head, "min")
    by = dict(capped)
    ratio_devs, apa = [], []
    net_fac = net_factors(head, capped)
    for name, blocks in capped:
        d = derived(blocks, "min")
        for length in LONG:
            for key in RATIO_KEYS:
                if not (name == "review 4" and key == "A/C"):
                    ratio_devs.append(dev(d[length][key], dh[length][key]))
            if name in ("repeat 2", "repeat 3", "review 5"):
                apa.append(dev(d[length]["A'/A"], dh[length]["A'/A"]))
    r4 = derived(by["review 4"], "min")
    r4_ac = [dev(r4[length]["A/C"], dh[length]["A/C"]) for length in LONG]
    r4_fac = [r4[length][k] / dh[length][k] for length in LONG for k in ("(A-B)/L2", "(A-B)/fuel")]
    hc, ho, hn = cold_calls(HEADLINE[1])
    cc = []
    for _, run in CAPPED_RUNS:
        cc += cold_calls(run)[0]
    mhz_head, mhz_capped = hosts[HEADLINE[1]]["mhz"], hosts[CAPPED_RUNS[0][1]]["mhz"]
    wmi = mhz_head / mhz_capped
    # Which of the six idle runs carry an A/C that, to two significant figures,
    # reads differently from the headline's L ≥ 500 rows; the document says one.
    quotable = {f"{dh[length]['A/C']:.1f}" for length in LONG}
    outliers = [(name, [derived(b, "min")[length]["A/C"] for length in LONG]) for name, b in [("full-clock", head)] + list(capped) if any(f"{derived(b, 'min')[length]['A/C']:.1f}" not in quotable for length in LONG)]
    outlier_text = "A/C read " + (rng(outliers[0][1], "{:.1f}") if len(outliers) == 1 else "/".join(rng(v, "{:.1f}") for _, v in outliers)) + f"× in {word(len(outliers))} of six runs"
    out = [
        ("clock: ratio columns agree", f"agree with the full-clock run within {within(max(abs(x) for x in ratio_devs))} %"),
        ("clock: review-4 A/C against full clock", "A/C in review 4, +" + rng(r4_ac, "{:.1f}") + " %"),
        ("clock: A′/A agrees where neither drifted", f"A′/A within {within(max(abs(x) for x in apa))} % in the three runs"),
        ("clock: net columns scale", "scale by " + rng(net_fac, "{:.2f}") + "×"),
        ("clock: review-4 A-bearing cells scale", "read " + rng(r4_fac, "{:.2f}") + "×"),
        # The two ENDS of the cold-first-call ranges (fastest over fastest,
        # slowest over slowest), not a per-call scaling.
        ("clock: cold compile range ends scale", "the ends of the cold-first-call range " + rng([min(cc) / min(hc), max(cc) / max(hc)], "{:.2f}") + "×"),
        ("clock: recorded figures differ by", f"differ by {wmi:.2f}× ({mhz_head} / {mhz_capped}), not by " + rng(net_fac, "{:.1f}") + "×"),
        ("quotable A/C outlier", outlier_text),
    ]
    # The 2026-09-20 contended run's minima against the full-clock headline.
    dc = derived(contended, "min")
    devs = [dev(dc[length][key], dh[length][key]) for length in LONG for key in RATIO_KEYS + NET_KEYS + ["A'/A"]]
    raw = [dev(stats(contended[(c, length)]["s"])["min"], stats(head[(c, length)]["s"])["min"]) for length in LONG for c in CONDS]
    derived_bound = within(max(abs(x) for x in devs))
    out.append(("contended: derived cells agree", f"all nine derived columns within {derived_bound} %"))
    # The 2026-09-20 subsection's closing paragraph states the same bound in
    # other words; same derivation, pinned again so neither copy can go stale.
    out.append(("contended: derived cells agree (closing)", f"agree on every derived column within {derived_bound} %"))
    out.append(("contended: raw minima agree", f"every per-block minimum within {within(max(abs(x) for x in raw))} %"))
    out.append(("contended: A/C", "A/C " + rng([dc[length]["A/C"] for length in LONG], "{:.2f}") + " against " + rng([dh[length]["A/C"] for length in LONG], "{:.2f}")))
    out.append(("contended: (A−B)/L²", "(A−B)/L² " + rng([dc[length]["(A-B)/L2"] for length in LONG], "{:.1f}") + " against " + rng([dh[length]["(A-B)/L2"] for length in LONG], "{:.1f}") + " ns"))
    # The per-decrement figure "reads the same on both" only at a stated L and
    # only while both print alike there; otherwise the text names both values.
    per_dec = []
    for length in reversed(LONG):
        c, h = f"{dc[length]['(A-B)/fuel']:.1f}", f"{dh[length]['(A-B)/fuel']:.1f}"
        per_dec.append(f"{c} ns on both at L = {length}" if c == h else f"{c} ns against {h} ns at L = {length}")
    out.append(("contended: per decrement on both", f"the per-decrement figure reads {per_dec[0]} ({per_dec[1]})"))
    a_prime_n = [stats(contended[("A'", length)]["s"])["n"] for length in LONG]
    out.append(("contended: A′ converged at", "A′ blocks converged at " + rng(a_prime_n, "{:.0f}") + " samples"))
    dcm = derived(contended, "med")
    out.append(("contended: A/C on net medians", " / ".join(f"{dcm[length]['A/C']:.2f}" for length in LENGTHS[1:]) + " for A/C"))
    cgap = max((stats(b["s"])["med"] - stats(b["s"])["min"]) / stats(b["s"])["min"] * 100 for b in contended.values())
    out.append(("contended: median-over-minimum gap", f"up to {cgap:.0f} % above its minima"))
    return out


def contended_scalars(contended: dict, header: dict, hosts: dict[str, dict], facts: dict) -> list[tuple[str, str]]:
    """What the 2026-09-20 run records about its own host and convergence, as the section words it."""
    logical = {h["logical"] for h in hosts.values()}
    if len(logical) != 1:
        sys.exit(f"the 2026-09-30 runs do not record one logical-CPU count: {logical}")
    # The shipped-path blocks at L ≥ 500 that the medians paragraph says ran to
    # the harness's sample ceiling: counted, not asserted (B at L = 1000
    # converged, so the record says three of the four).
    shipped_long = [stats(contended[(c, length)]["s"])["n"] for c in ("A", "B") for length in LONG]
    at_ceiling = sum(n == facts["ceiling"] for n in shipped_long)
    return [
        ("contended: resting load", f"a resting load of {header['resting']} % (of the host's {logical.pop()} logical CPUs)"),
        ("contended: wall time", f"a {header['wall_s']} s wall time"),
        ("contended: shipped blocks at the ceiling", f"{word(at_ceiling)} of the {word(len(shipped_long))} shipped A and B blocks at L ≥ 500 ran to the {facts['ceiling']}-sample ceiling"),
    ]


def session_log_scalars(header: dict) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    """The 2026-09-20 session-log figures as the document words them: (in the section, document-wide).

    A `{wall_s}` placeholder is the run's wall time from its summary.md header.
    Fails closed by wording: a placeholder left unfilled (or misspelled) is text
    the document does not carry, so the check fails rather than pin a template.
    """

    def render(text: str) -> str:
        return text.replace("{wall_s}", str(header["wall_s"]))

    return (
        [(name, render(text)) for name, text, _ in SESSION_LOG_CONSTANTS],
        [(name, render(text)) for name, text, _ in SESSION_LOG_CONSTANTS_DOC_WIDE],
    )


def doc_wide_scalars(head: dict, capped: list[tuple[str, dict]], hosts: dict[str, dict], header: dict) -> list[tuple[str, str]]:
    """Numbers the document repeats outside the section (header, environment, methodology, caveats)."""
    dh = derived(head, "min")
    all5 = [derived(b, "min") for _, b in capped]
    by = dict(capped)
    ref, r4 = by["capped reference"], by["review 4"]
    dref = derived(ref, "min")
    held = [
        abs(dev(stats(blocks[(c, length)]["s"])[key], stats(ref[(c, length)]["s"])[key]))
        for name, blocks in capped
        if name != "capped reference"
        for c in ("B", "C", "D", "B'")
        for length in LONG
        for key in ("min", "med")
    ]
    a_ratio = [dev(stats(r4[("A", length)]["s"])["med"], stats(ref[("A", length)]["s"])["med"]) for length in LENGTHS[1:]]
    a_prime_slow = [(dref[length]["A'/A"] - 1) * 100 for length in LENGTHS[1:]]
    thresholds = {h["thresholds"] for h in hosts.values()}
    if len(thresholds) != 1:
        sys.exit(f"the 2026-09-30 runs were not admitted under one set of runner thresholds: {thresholds}")
    idle_s, mean_below, peak_below = thresholds.pop()
    max_wait = hosts[HEADLINE[1]]["max_wait_s"]  # the runner's default patience; the headline run passed no override
    mhz_head, mhz_capped, mhz_max = hosts[HEADLINE[1]]["mhz"], hosts[CAPPED_RUNS[0][1]]["mhz"], hosts[HEADLINE[1]]["mhz_max"]
    fuel_per_cell_1000 = head[("A", 1000)]["fuel"] / (1000 * 1000)
    return [
        ("caveat: other blocks held", f"the other blocks held to {under(max(held))} % at L ≥ 500"),
        ("caveat: clock factor", "differ by about " + rng(net_factors(head, capped), "{:.1f}") + "×"),
        ("caveat: A/C across the capped runs", "A/C " + rng([d[length]["A/C"] for d in all5 for length in LONG], "{:.2f}") + " across the five capped-clock runs"),
        ("caveat: A/C in the headline", rng([dh[length]["A/C"] for length in LONG], "{:.2f}") + " in the full-clock headline"),
        ("caveat: run count", f"Each of the {word(len(capped) + 1)} was"),
        ("caveat: clocks recorded", f"record {mhz_capped} of {mhz_max} MHz and the full-clock headline {mhz_head} of {mhz_max} MHz"),
        ("caveat: executor drift range", f"{min(a_ratio):.0f}–{max(a_prime_slow):.0f} % off the others"),
        ("caveat: reference A′ drift", "capped-clock reference, " + rng(a_prime_slow, "{:.0f}") + " % slow"),
        ("caveat: review-4 A drift", "review 4, " + rng(a_ratio, "{:.1f}") + " % slow"),
        ("caveat: decrements per cell", f"~{rround(fuel_per_cell_1000)} host-call decrements per DP cell"),
        ("caveat: 09-20 resting load", f"{header['resting']} % resting load"),
        ("runner window (environment, caveats)", f"{idle_s} s window under {mean_below:.0f} % mean / {peak_below:.0f} % peak load"),
        ("runner window (methodology)", f"a full {idle_s} s window with mean < {mean_below:.0f} % and peak < {peak_below:.0f} %"),
        ("runner max wait (methodology)", f"retrying up to {max_wait // 60} min"),
    ]


def with_counts(scalars_: list[tuple[str, str]]) -> list[tuple[str, str, int]]:
    """Attach the expected occurrence count (1 unless OCCURRENCES says otherwise)."""
    return [(name, text, OCCURRENCES.get(name, 1)) for name, text in scalars_]


def build(head: dict, capped: list[tuple[str, dict]], contended: dict, hosts: dict[str, dict], facts: dict, header: dict):
    tables = [
        ("headline minima", minima_table(head)),
        ("headline medians", medians_table_idle(head)),
        ("headline derived on net minima", derived_table(head, "min", with_fuel=True)),
        ("headline derived on net medians", derived_table(head, "med", with_fuel=False)),
        ("repeatability, five capped-clock runs", repeatability_table(capped)),
        ("contended minima", minima_table(contended)),
        ("contended medians", medians_table_contended(contended)),
        ("contended derived on net minima", derived_table(contended, "min", with_fuel=False)),
    ]
    idle_section, idle_doc = idle_bounds(head, capped)
    log_section, log_doc = session_log_scalars(header)
    scalars_ = (
        module_scalars(facts)
        + headline_scalars(head, hosts[HEADLINE[1]], facts)
        + idle_section
        + executor_drifts(head, capped)
        + capped_scalars(capped, hosts)
        + clock_scalars(head, capped, hosts, contended)
        + contended_scalars(contended, header, hosts, facts)
        + [(name, text) for name, text, _ in SOURCE_CONSTANTS]
        + log_section
    )
    doc_wide = doc_wide_scalars(head, capped, hosts, header) + idle_doc + log_doc
    names = {name for name, _ in scalars_} | {name for name, _ in doc_wide}
    unknown = set(OCCURRENCES) - names
    if unknown:
        sys.exit(f"OCCURRENCES names scalars that are not emitted: {sorted(unknown)}")
    if len(names) != len(scalars_) + len(doc_wide):
        sys.exit("two emitted scalars share a name; counts would be ambiguous")
    return tables, with_counts(scalars_), with_counts(doc_wide)


def check_doc(doc: str, tables, scalars_, doc_wide) -> list[str]:
    start = doc.find("## Fuel-instrumentation runtime overhead")
    end = doc.find("## Compilation determinism")
    if start < 0 or end < start:
        return ["PERFORMANCE.md: the fuel-overhead section boundaries were not found"]
    section = doc[start:end]
    # Tables are one row per line and must match verbatim, once. Prose is
    # hard-wrapped at ~72 columns, so a scalar is matched with runs of
    # whitespace collapsed; every digit, unit and dash must still match
    # exactly, and the number of occurrences must be the expected one — a
    # repeated number that is updated in one place and not the other fails.
    prose = " ".join(section.split())
    whole = " ".join(doc.split())
    errors = []
    for name, text in tables:
        if text not in section:
            # Name the first row that is missing so the fix is one line, not a table.
            missing = next((row for row in text.splitlines() if row not in section), text.splitlines()[0])
            errors.append(f"table '{name}' is not in PERFORMANCE.md verbatim; first missing row: {missing}")
        elif section.count(text) != 1:
            errors.append(f"table '{name}' appears {section.count(text)} times in the section, expected once")
    for name, text, expected in scalars_:
        got = prose.count(" ".join(text.split()))
        if got != expected:
            errors.append(f"scalar '{name}' expected exactly {expected}× verbatim in the section, found {got}: {text!r}")
    for name, text, expected in doc_wide:
        got = whole.count(" ".join(text.split()))
        if got != expected:
            errors.append(f"scalar '{name}' expected exactly {expected}× verbatim in PERFORMANCE.md, found {got}: {text!r}")
    return errors


def self_test(head: dict, capped: list[tuple[str, dict]], contended: dict, hosts: dict[str, dict], facts: dict, header: dict, doc: str) -> int:
    """SC-P4: the detector must fire on a planted change, or it proves nothing."""
    tables, scalars_, doc_wide = build(head, capped, contended, hosts, facts, header)
    if check_doc(doc, tables, scalars_, doc_wide):
        print("self-test needs a document that passes first; run without --self-test", file=sys.stderr)
        return 1
    failures = 0
    planted_count = 0

    def expect_caught(what: str, errors: list[str]) -> None:
        nonlocal failures, planted_count
        planted_count += 1
        if not errors:
            print(f"self-test: {what} was not caught", file=sys.stderr)
            failures += 1

    def bump(text: str) -> str:
        """The text with one digit changed: a decimal's digit where one exists, else the first digit."""
        m = re.search(r"\d(?=\.\d)", text) or re.search(r"\d", text)
        i = m.start()
        return text[:i] + str((int(text[i]) + 1) % 10) + text[i + 1 :]

    def bump_last_digit(text: str) -> str:
        """The text with the last digit of its first number incremented: '3203 of…' → '3204 of…', '1.3 %' → '1.4 %'."""
        m = re.search(r"\d+(?:\.\d+)?", text)
        i = m.end() - 1
        return text[:i] + str((int(text[i]) + 1) % 10) + text[i + 1 :]

    section_start = doc.find("## Fuel-instrumentation runtime overhead")
    section_end = doc.find("## Compilation determinism")

    def occurrences(document: str, text: str) -> list[re.Match]:
        """Every place the SECTION's (hard-wrapped) prose carries `text`.

        Scoped to the section because that is where section scalars are
        counted; the caveats repeat some of them under their own pins.
        """
        pattern = r"\s+".join(re.escape(tok) for tok in text.split())
        return [m for m in re.finditer(pattern, document) if section_start <= m.start() < section_end]

    def bump_last_number(text: str) -> str:
        """The text with the last digit of its LAST number incremented: 'alive for 49 of its 79 s' → '… 80 s'."""
        m = list(re.finditer(r"\d+(?:\.\d+)?", text))[-1]
        i = m.end() - 1
        return text[:i] + str((int(text[i]) + 1) % 10) + text[i + 1 :]

    def bump_word(text: str) -> str:
        """The text with its first number word moved to a neighbour: 'six' → 'seven', 'twelve' → 'eleven'."""
        m = re.search(r"\b(" + "|".join(WORDS) + r")\b", text)
        i = WORDS.index(m.group(1))
        return text[: m.start()] + (WORDS[i + 1] if i + 1 < len(WORDS) else WORDS[i - 1]) + text[m.end() :]

    def plant(document: str, text: str, mutate=bump) -> str:
        """The document with `text` changed by `mutate` (one digit, by default), wherever the prose wraps it.

        Prose is hard-wrapped, so the scalar is located with any run of
        whitespace matching; the returned document differs from the input, or
        equals it when the scalar is absent (the caller treats that as a failure).
        """
        m = re.search(r"\s+".join(re.escape(tok) for tok in text.split()), document)
        if not m:
            return document
        return document[: m.start()] + mutate(document[m.start() : m.end()]) + document[m.end() :]

    def plant_last_occurrence(document: str, text: str) -> str:
        """Change ONLY the last in-section occurrence of a repeated scalar: a stale duplicate."""
        found = occurrences(document, text)
        if len(found) < 2:
            return document
        m = found[-1]
        return document[: m.start()] + bump_last_digit(document[m.start() : m.end()]) + document[m.end() :]

    # 1. One sample in the headline moves by 1 ms → summary.md and the document must disagree.
    mutated = copy.deepcopy(head)
    mutated[("A", 1000)]["s"][0] += 1_000_000
    expect_caught("a planted +1 ms headline sample (summary.md)", check_summary(HEADLINE[1], mutated))
    expect_caught("a planted +1 ms headline sample (PERFORMANCE.md)", check_doc(doc, *build(mutated, capped, contended, hosts, facts, header)))
    # 2. One converged headline block gains an outlier → its CV crosses 5 %, the
    #    flagged-block count, list and medians table all change → caught. The
    #    block is chosen ✓ so the plant is a real change of the count.
    mutated = copy.deepcopy(head)
    target = next((c, length) for length in LONG for c in CONDS if stats(head[(c, length)]["s"])["cv"] < CV_CONVERGED)
    mutated[target]["s"][-1] = int(mutated[target]["s"][-1] * 1.6)
    if stats(mutated[target]["s"])["cv"] < CV_CONVERGED:
        print(f"self-test: the planted outlier in {target} did not cross the flag threshold", file=sys.stderr)
        failures += 1
    expect_caught("a planted outlier that flags one more block", check_doc(doc, *build(mutated, capped, contended, hosts, facts, header)))
    # 3. One capped run's samples all slow by 5 % → the clock-scaling factor and
    #    the repeatability table change → caught.
    mutated_capped = copy.deepcopy(capped)
    for b in mutated_capped[1][1].values():
        b["s"] = [int(x * 1.05) for x in b["s"]]
    expect_caught("a planted 5 % slowdown of repeat 2 (clock factor)", check_doc(doc, *build(head, mutated_capped, contended, hosts, facts, header)))
    # 4. The recorded clock of the headline changes → the clock scalar changes → caught.
    mutated_hosts = copy.deepcopy(hosts)
    mutated_hosts[HEADLINE[1]]["mhz"] -= 1
    expect_caught("a planted change to the headline's recorded MHz", check_doc(doc, *build(head, capped, contended, mutated_hosts, facts, header)))
    # 5. One digit of one table cell in the document changes → caught.
    row = tables[0][1].splitlines()[-1]  # headline minima, L=1000
    planted = doc.replace(row, row.replace("| 1000 |", "| 1000 | 0.0 |", 1), 1)
    if planted == doc:
        print("self-test: the table plant was a no-op", file=sys.stderr)
        failures += 1
    expect_caught("a planted table edit in PERFORMANCE.md", check_doc(planted, tables, scalars_, doc_wide))
    # 6. One digit of one prose number changes, once per claim family → caught.
    #    Each scalar is chosen by name; the edit must be a real edit (a no-op
    #    replacement would pass vacuously), so the document is checked to differ.
    for what in (
        "C net at L=1000",  # the headline's per-cell family
        "clock: net columns scale",  # the clock-scaling factor
        "P1 largest deviation except A′/A",  # the between-process spread percentage
        "P2 review-4 other blocks at L ≥ 500",  # the second spread percentage
        "headline flagged count",  # the flagged-block count
        "headline flagged list",  # a flagged block's CV
        "contended: derived cells agree",  # the contended-run agreement
        "capped other runs' flags",  # the capped set's flag census
        "idle largest CV",  # the within-process CV bound over the six idle runs
        "fuel per cell",  # fuel ÷ L², derived from samples.tsv's fuel_consumed
        "A0 size and digest",  # read from summary.md, not from samples
        "quotable A/C outlier",  # the one run whose A/C reads differently
        "09-20 during-run load",  # a session-log constant: pinned verbatim, not derived
        "09-20 rustc alive",  # the session-log 49 s, measured against the summary.md wall time
        "contended: derived cells agree (closing)",  # the contended bound's second wording
        "harness drop band",  # the contended legend's ✗ band, from CV_DROP
        "contended: shipped blocks at the ceiling",  # which shipped blocks hit the harness's ceiling
    ):
        text = next(t for n, t, _ in scalars_ if n == what)
        planted = plant(doc, text)
        if planted == doc:
            print(f"self-test: the plant for scalar '{what}' was a no-op (scalar not found)", file=sys.stderr)
            failures += 1
        expect_caught(f"a planted change to scalar '{what}'", check_doc(planted, tables, scalars_, doc_wide))
    # 6b. A WORD-FORM number ("six", "twelve", "twice in six runs") changes →
    #     caught: these carry no digit, so the plant moves the word to its neighbour.
    for what in (
        "tool calls per cell",  # a source constant: "at six calls per cell"
        "grant-cloning shims",  # a source constant: "twelve of which clone the grants"
        "executor drifts",  # derived: how many idle runs show an executor off the others
    ):
        text = next(t for n, t, _ in scalars_ if n == what)
        planted = plant(doc, text, bump_word)
        if planted == doc:
            print(f"self-test: the word plant for scalar '{what}' was a no-op (scalar not found)", file=sys.stderr)
            failures += 1
        expect_caught(f"a planted change to word-form scalar '{what}'", check_doc(planted, tables, scalars_, doc_wide))
    # 6c. The 2026-09-20 wall time is quoted twice in the section ("a 79 s wall
    #     time" from the summary.md header, and "alive for 49 of its 79 s" in the
    #     session-log sentence). The second copy changed alone → caught; the
    #     header's wall time changed → BOTH pins move, because the second copy
    #     is rendered from the header, not written a second time.
    text = next(t for n, t, _ in scalars_ if n == "09-20 rustc alive")
    planted = plant(doc, text, bump_last_number)
    if planted == doc:
        print("self-test: the wall-time copy plant was a no-op", file=sys.stderr)
        failures += 1
    expect_caught("a stale copy of the 2026-09-20 wall time in the session-log sentence", check_doc(planted, tables, scalars_, doc_wide))
    mutated_header = dict(header, wall_s=header["wall_s"] + 1)
    _, mutated_scalars, _ = build(head, capped, contended, hosts, facts, mutated_header)
    if next(t for n, t, _ in mutated_scalars if n == "09-20 rustc alive") == text:
        print("self-test: the session-log sentence's wall time did not follow the summary.md header", file=sys.stderr)
        failures += 1
    expect_caught("a planted change to the 2026-09-20 summary.md wall time", check_doc(doc, *build(head, capped, contended, hosts, facts, mutated_header)))
    # 6d. The derived word-form counts follow the data: a third executor drift
    #     (repeat 2's A′ blocks 20 % slow) → "three times in six runs"; one
    #     contended shipped block a sample short of the ceiling → "two of the four".
    mutated_capped = copy.deepcopy(capped)
    for length in LENGTHS:
        b = mutated_capped[1][1][("A'", length)]
        b["s"] = [int(x * 1.2) for x in b["s"]]
    drift_text = next(t for n, t, _ in scalars_ if n == "executor drifts")
    _, mutated_scalars, _ = build(head, mutated_capped, contended, hosts, facts, header)
    if next(t for n, t, _ in mutated_scalars if n == "executor drifts") == drift_text:
        print("self-test: a planted third executor drift did not change the drift count", file=sys.stderr)
        failures += 1
    expect_caught("a planted third executor drift (repeat 2's A′ 20 % slow)", check_doc(doc, *build(head, mutated_capped, contended, hosts, facts, header)))
    mutated = copy.deepcopy(contended)
    mutated[("A", 500)]["s"] = mutated[("A", 500)]["s"][:-1]
    ceiling_text = next(t for n, t, _ in scalars_ if n == "contended: shipped blocks at the ceiling")
    _, mutated_scalars, _ = build(head, capped, mutated, hosts, facts, header)
    if next(t for n, t, _ in mutated_scalars if n == "contended: shipped blocks at the ceiling") == ceiling_text:
        print("self-test: a contended block one sample short of the ceiling did not change the ceiling count", file=sys.stderr)
        failures += 1
    expect_caught("a contended shipped block one sample short of the ceiling", check_doc(doc, *build(head, capped, mutated, hosts, facts, header)))
    # 7. A doc-wide scalar outside the section changes → caught.
    text = next(t for n, t, _ in doc_wide if n == "caveat: A/C across the capped runs")
    planted = plant(doc, text)
    if planted == doc:
        print("self-test: the doc-wide plant was a no-op", file=sys.stderr)
        failures += 1
    expect_caught("a planted change to a caveat outside the section", check_doc(planted, tables, scalars_, doc_wide))
    # 7b. The Methodology copy of the 2026-09-20 runner gate: its figure changed
    #     → caught; its provenance label dropped → caught (the label is part of
    #     the pin, so the sentence cannot lose it silently).
    text = next(t for n, t, _ in doc_wide if n == "09-20 runner gate (methodology)")
    planted = plant(doc, text)
    if planted == doc:
        print("self-test: the Methodology runner-gate plant was a no-op", file=sys.stderr)
        failures += 1
    expect_caught("a planted change to the Methodology copy of the 2026-09-20 runner gate", check_doc(planted, tables, scalars_, doc_wide))
    m = re.search(r"\s+".join(re.escape(tok) for tok in text.split()), doc)
    figure = text.split(" — ")[0]  # the figure without its provenance label
    planted = doc[: m.start()] + figure + doc[m.end() :] if m else doc
    if planted == doc:
        print("self-test: the label-drop plant was a no-op", file=sys.stderr)
        failures += 1
    expect_caught("the provenance label dropped from the Methodology runner-gate sentence", check_doc(planted, tables, scalars_, doc_wide))
    # 8. A STALE DUPLICATE: a repeated number changed in its last occurrence only
    #    (the two misses the P2-BENCH-FINAL review planted against the
    #    one-match-suffices checker: "3203 of 3504 MHz" → 3204 in one of its
    #    occurrences, and the L ≥ 500 gap bound → one tenth higher in one of
    #    its three). Every other occurrence still matches, so only an exact
    #    occurrence count catches them.
    for what in ("capped clock", "largest gap at L ≥ 500"):
        text = next(t for n, t, _ in scalars_ if n == what)
        expected = OCCURRENCES[what]
        if len(occurrences(doc, text)) != expected or expected < 2:
            print(f"self-test: scalar '{what}' is not a repeated pin ({expected} expected); the stale-duplicate plant needs one", file=sys.stderr)
            failures += 1
        planted = plant_last_occurrence(doc, text)
        if planted == doc:
            print(f"self-test: the stale-duplicate plant for '{what}' was a no-op", file=sys.stderr)
            failures += 1
        expect_caught(f"a stale duplicate of repeated scalar '{what}' (last occurrence changed to {bump_last_digit(text)!r})", check_doc(planted, tables, scalars_, doc_wide))
    # 9. An EXTRA copy of a once-only number pasted into the section → the count
    #    is 2, not 1 → caught (the over-count direction).
    text = next(t for n, t, _ in scalars_ if n == "per decrement")
    heading = "## Fuel-instrumentation runtime overhead"
    planted = doc.replace(heading, heading + "\n\n" + text, 1)
    expect_caught("an extra copy of a once-only scalar in the section", check_doc(planted, tables, scalars_, doc_wide))
    print(f"self-test: {planted_count} planted changes, " + ("all caught" if failures == 0 else f"{failures} MISSED"))
    return 1 if failures else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--emit", action="store_true", help="print every table and scalar the document must contain, with its expected count")
    ap.add_argument("--self-test", action="store_true", help="plant changes and require the check to fail")
    args = ap.parse_args()

    all_runs = [HEADLINE[1]] + [run for _, run in CAPPED_RUNS] + [CONTENDED]
    head = load_samples(HEADLINE[1])
    capped = [(name, load_samples(run)) for name, run in CAPPED_RUNS]
    contended = load_samples(CONTENDED)
    hosts = {run: load_host(run) for run in [HEADLINE[1]] + [run for _, run in CAPPED_RUNS]}
    facts_by_run = {run: module_facts(run) for run in all_runs}
    header = contended_header()
    errors = check_inputs(all_runs)
    errors += check_summary(HEADLINE[1], head)
    for (_, run), (_, blocks) in zip(CAPPED_RUNS, capped):
        errors += check_summary(run, blocks)
    errors += check_summary(CONTENDED, contended)
    if len({h["sha256"] for h in hosts.values()}) != 1 or any(h["exit"] != 0 for h in hosts.values()):
        errors.append("the 2026-09-30 runs do not share one harness SHA-256 with exit code 0")
    # Every run must have timed the same modules with the same seed, lengths and
    # convergence rule, or the document's one A0/A1 description does not cover them all.
    if len({json.dumps(f, sort_keys=True) for f in facts_by_run.values()}) != 1:
        errors.append(f"the runs' summary.md files do not record one A0/A1/seed/lengths/convergence record: {facts_by_run}")
    facts = facts_by_run[HEADLINE[1]]
    if facts["lengths"] != LENGTHS or facts["cv"] != CV_CONVERGED:
        errors.append(f"the harness's recorded lengths/CV threshold {facts['lengths']} / {facts['cv']} differ from this script's {LENGTHS} / {CV_CONVERGED}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"summary.md agrees with samples.tsv under the harness rule in all {len(capped) + 2} runs (24 blocks each); inputs, modules, seed and harness identical across runs")

    doc = DOC.read_text(encoding="utf-8")
    if args.self_test:
        return self_test(head, capped, contended, hosts, facts, header, doc)
    tables, scalars_, doc_wide = build(head, capped, contended, hosts, facts, header)
    if args.emit:
        for name, text in tables:
            print(f"\n### {name}\n\n{text}")
        print("\n### scalars (in the section; ×n = expected occurrences)\n")
        for name, text, n in scalars_:
            print(f"{name} ×{n}: {text}")
        print("\n### scalars (anywhere in the document)\n")
        for name, text, n in doc_wide:
            print(f"{name} ×{n}: {text}")
        print("\n### constants not derived from any sample (pinned verbatim; provenance)\n")
        log_section, log_doc = session_log_scalars(header)
        rendered = dict(log_section + log_doc)  # the session-log texts as the document carries them
        for name, text, source in SOURCE_CONSTANTS + SESSION_LOG_CONSTANTS + SESSION_LOG_CONSTANTS_DOC_WIDE:
            print(f"{name}: {rendered.get(name, text)}  — {source}")
        return 0
    errors = check_doc(doc, tables, scalars_, doc_wide)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    pins = sum(n for _, _, n in scalars_) + sum(n for _, _, n in doc_wide)
    print(f"PERFORMANCE.md quotes all {len(tables)} tables and {len(scalars_) + len(doc_wide)} prose numbers verbatim, each exactly its expected number of times ({pins} occurrences in all)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
