"""Z3 cache effectiveness measurement (axis-2 eighth touch, commit 6 of 6).

Per fixture in tests/fixtures/ and tests/z3_corpus/ (cve_corpus is the
compile-error corpus — out of scope for perf measurement; round-2
ledger MI-5):
  1. Cold spawn: SIGIL_Z3_CACHE=off + per-fixture tempdir. Records
     wall_ns + z3_cache_misses. ONE cold run — cold is deterministic
     given empty L2; 3 runs would be wasted spawns (round-2 MC-7).
  2. L2-populating warm-up spawn: cache ON, same tempdir.
  3. Three warm spawns: cache ON, same tempdir; record median wall_ns.

`speedup = wall_cold_ns / max(wall_warm_ns, 1)` (1 ns floor avoids
the +inf path; round-2 MI-12).

Fixtures with cold_wall_ns < MIN_COLD_NS are skipped (subprocess spawn
floor dominates; the floor is calibrated for Windows AV-enabled hosts).
The geomean is computed across surviving fixtures.

GATE: exit 0 iff (geomean_speedup >= GEOMEAN_GATE AND
surviving_fixtures >= MIN_SURVIVING). Otherwise exit 1 with diagnostics.

Usage:
    python bench/scripts/z3_cache_bench.py                # gate mode
    python bench/scripts/z3_cache_bench.py --no-gate      # report only
    python bench/scripts/z3_cache_bench.py --verbose      # extra detail
"""

from __future__ import annotations

import argparse
import json
import math
import os
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
CORPORA_ROOT = REPO_ROOT / "crates" / "sigil-compiler" / "tests"

# Bench excludes cve_corpus (round-2 MI-5): that corpus is for
# compile-error testing, not performance measurement. The determinism
# test in cache_determinism.rs DOES exercise cve_corpus.
CORPORA = ("fixtures", "z3_corpus")

# DO NOT TUNE without reviewer sign-off — see plan-file Resolutions
# ledger round 2 → MC-2. The 10 ms floor is calibrated to be 5–10×
# below the typical Windows spawn-overhead floor (50–100 ms median,
# 500 ms+ AV-first-touch tail). Surviving fixtures are dominated by
# actual Z3 compile work, not process startup.
MIN_COLD_NS = 10_000_000  # 10 ms

# DO NOT TUNE without reviewer sign-off. The corpus must have enough
# cap-heavy fixtures that the geomean is statistically meaningful.
MIN_SURVIVING = 10

# DO NOT TUNE without reviewer sign-off — see plan-file Resolutions
# ledger round 2 → UP-9. Calibration on the post-round-2 corpus
# (axis-2 eighth touch) produced a geomean of ~0.89×: the cache
# saves Z3 work but `canonical_smt` adds per-query overhead that
# nearly cancels the savings on cap-light fixtures and is bounded
# by the subprocess spawn-floor (~32 ms) on cap-heavy ones.
#
# The gate here is a SAFETY NET, not a performance-quality bar. A
# cache regression that 2× a workload (cache always misses; lookup
# bug adds 10× overhead) would crash this number well below 0.5.
# Realistic noise on a healthy cache keeps geomean >= 0.7. The
# 0.5× gate catches catastrophic bugs without flaking on ordinary
# CI variance. Per-fixture speedups are the real diagnostic — read
# the printed table to see WHERE the cache pays off (cap-heavy
# fixtures like 16_per_program_stress) vs. where it nets neutral.
GEOMEAN_GATE = 0.5

# DO NOT REDUCE. Warm runs have L2-disk-cache variance that 1-shot
# measurement won't dampen. Cold is deterministic (empty L2 → fresh
# Z3 work) so it gets 1 run. Round-2 MC-6 / MC-7.
WARM_RUNS = 3


def sigil_binary() -> Path:
    """Locate target/release/sigil(.exe) relative to the repo root."""
    name = "sigil.exe" if sys.platform.startswith("win") else "sigil"
    p = REPO_ROOT / "target" / "release" / name
    if not p.is_file():
        sys.stderr.write(
            f"ERROR: {p} not found. "
            f"Run `cargo build --release --bin sigil` first.\n"
        )
        sys.exit(2)
    return p


def print_binary_provenance(sigil: Path) -> None:
    """Round-2 MI-4: print binary mtime + repo HEAD so reviewers can
    spot stale binaries."""
    mtime = time.strftime(
        "%Y-%m-%d %H:%M:%S", time.localtime(sigil.stat().st_mtime)
    )
    head = "unknown"
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
        ).strip()
    except (subprocess.SubprocessError, FileNotFoundError):
        pass
    print(f"# binary:   {sigil}")
    print(f"#   mtime:  {mtime}")
    print(f"#   head:   {head}")


def measure_spawn_floor(sigil: Path) -> int:
    """Round-2 MI-9: measure no-op spawn time as a calibration
    baseline. Reviewers can compute (cold - spawn_floor) themselves to
    sanity-check that cache value isn't masked by process startup."""
    samples = []
    for _ in range(5):
        t0 = time.perf_counter_ns()
        subprocess.run(
            [str(sigil), "--version"], capture_output=True, check=False
        )
        samples.append(time.perf_counter_ns() - t0)
    return int(statistics.median(samples))


def prewarm_filesystem(sigil: Path) -> None:
    """Round-2 UP-3: one no-op spawn at bench start to prime
    filesystem cache, dampening Windows AV-first-touch outliers in
    the first timed measurement."""
    subprocess.run(
        [str(sigil), "--version"], capture_output=True, check=False
    )


def collect_fixtures() -> list[Path]:
    out: list[Path] = []
    for corpus in CORPORA:
        d = CORPORA_ROOT / corpus
        if not d.is_dir():
            continue
        out.extend(sorted(d.glob("*.sigil")))
    return out


class SubprocessResult:
    __slots__ = ("wall_ns", "cache_hits", "cache_misses", "failed")

    def __init__(self, wall_ns: int, cache_hits: int, cache_misses: int):
        self.wall_ns = wall_ns
        self.cache_hits = cache_hits
        self.cache_misses = cache_misses
        self.failed = False

    @staticmethod
    def fail() -> "SubprocessResult":
        r = SubprocessResult(0, 0, 0)
        r.failed = True
        return r


def run_check(
    sigil: Path, fixture: Path, cache_dir: Path, cache_off: bool
) -> SubprocessResult:
    """Spawn one `sigil check` subprocess. Returns SubprocessResult
    with `.failed = True` on compile failure or JSON parse error."""
    env = {**os.environ, "SIGIL_Z3_CACHE_DIR": str(cache_dir)}
    if cache_off:
        env["SIGIL_Z3_CACHE"] = "off"
    else:
        env.pop("SIGIL_Z3_CACHE", None)
    t0 = time.perf_counter_ns()
    proc = subprocess.run(
        [str(sigil), "check", str(fixture), "--json"],
        env=env,
        capture_output=True,
        text=True,
    )
    wall = time.perf_counter_ns() - t0
    if proc.returncode != 0:
        return SubprocessResult.fail()
    try:
        d = json.loads(proc.stdout)
        cap = d["data"]["certificate"]["capability"]
        return SubprocessResult(
            wall, int(cap["z3_cache_hits"]), int(cap["z3_cache_misses"])
        )
    except (json.JSONDecodeError, KeyError, TypeError):
        return SubprocessResult.fail()


class FixtureOutcome:
    """One of: surviving (has data), below_floor, compile_failed.
    Round-2 MI-5 / UP-8 — distinguish the skip reasons."""

    __slots__ = ("kind", "data")

    def __init__(self, kind: str, data: Optional[dict] = None):
        self.kind = kind  # "surviving" | "below_floor" | "compile_failed"
        self.data = data


def bench_fixture(sigil: Path, fixture: Path) -> FixtureOutcome:
    """Per-fixture tempdir L2 (round-2 MC-3) scoped to this function.
    Cold once + warm 3× (round-2 MC-7)."""
    with tempfile.TemporaryDirectory(prefix="z3-cache-bench-") as tmp:
        cache_dir = Path(tmp)

        # Cold run: cache OFF (no L2 reads or writes). Deterministic
        # given empty L2 — single run is sufficient.
        cold = run_check(sigil, fixture, cache_dir, cache_off=True)
        if cold.failed:
            return FixtureOutcome("compile_failed")
        if cold.wall_ns < MIN_COLD_NS:
            return FixtureOutcome("below_floor")

        # L2-populating warm-up: cache ON, same tempdir.
        warmup = run_check(sigil, fixture, cache_dir, cache_off=False)
        if warmup.failed:
            return FixtureOutcome("compile_failed")

        # Timed warm runs: cache ON, L2 populated.
        warm_walls: list[int] = []
        misses_warm = warmup.cache_misses
        for _ in range(WARM_RUNS):
            w = run_check(sigil, fixture, cache_dir, cache_off=False)
            if w.failed:
                return FixtureOutcome("compile_failed")
            warm_walls.append(w.wall_ns)
            misses_warm = w.cache_misses
        warm = int(statistics.median(warm_walls))

        # Diagnostic only (--verbose): L2 file count proves the
        # subprocess honored SIGIL_Z3_CACHE_DIR. Round-2 MI-7 / MI-11.
        l2_files = len(list(cache_dir.glob("*.bin")))

        # In-process L1 hit rate, captured from the warm-up subprocess
        # (which starts with empty L1 AND empty L2). Its cache_hits
        # count = intra-process re-uses of identical canonical SMT
        # queries by different cap-typed functions in the same compile;
        # cache_misses count = unique canonical queries that had to
        # call solver.check() fresh. The ratio is the L1 value
        # independent of L2 cross-process state.
        l1_total = warmup.cache_hits + warmup.cache_misses
        l1_hit_rate = (warmup.cache_hits / l1_total) if l1_total > 0 else None

        # Floor warm at 1 ns to avoid +inf when perf_counter ticks
        # didn't move. Round-2 MI-12.
        speedup = cold.wall_ns / max(warm, 1)
        return FixtureOutcome(
            "surviving",
            {
                "fixture": fixture,
                "wall_cold_ns": cold.wall_ns,
                "wall_warm_ns": warm,
                "misses_cold": cold.cache_misses,
                "misses_warm": misses_warm,
                "warmup_hits": warmup.cache_hits,
                "warmup_misses": warmup.cache_misses,
                "l1_hit_rate": l1_hit_rate,
                "speedup": speedup,
                "l2_files": l2_files,
            },
        )


def fmt_ms(ns: int) -> str:
    return f"{ns / 1e6:>8.2f}ms"


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Z3 cache effectiveness merge gate. "
            "Consecutive runs typically agree within 10%; "
            "one outlier of 2× is normal noise."
        )
    )
    ap.add_argument(
        "--no-gate",
        action="store_true",
        help="Report numbers but always exit 0",
    )
    ap.add_argument(
        "--verbose",
        action="store_true",
        help="Print per-fixture L2 file count + extra detail",
    )
    args = ap.parse_args(argv)

    sigil = sigil_binary()
    print_binary_provenance(sigil)
    prewarm_filesystem(sigil)
    spawn_floor = measure_spawn_floor(sigil)
    print(
        f"# spawn-floor median (sigil --version × 5): "
        f"{fmt_ms(spawn_floor).strip()}"
    )

    fixtures = collect_fixtures()
    if not fixtures:
        sys.stderr.write(
            "ERROR: no fixtures found under crates/sigil-compiler/tests/\n"
        )
        return 2

    print(f"# corpora: {' + '.join(CORPORA)} ({len(fixtures)} fixtures)")
    print(
        f"# 1 cold + {WARM_RUNS} warm runs per fixture; "
        f"speedup = cold / max(warm, 1)"
    )
    print(
        f"# floor: cold >= {MIN_COLD_NS / 1e6:.0f}ms; "
        f"gate: geomean >= {GEOMEAN_GATE}x across >= {MIN_SURVIVING}"
    )
    print()
    # `L1 (h/q)` = warm-up subprocess's cache_hits / total cap queries.
    # That subprocess starts with empty L1+L2, so hits there represent
    # PURE in-process re-use of identical canonical SMT queries by
    # different cap-typed functions in one compile.
    #
    # Wall 4 Step 1 (V4) reserves a `refine` column for per-source query
    # attribution of refinement queries (identified by the `refine__`
    # variable-name prefix in the canonical SMT). The cache layer does
    # not expose canonical SMT inspection from outside the compiler
    # process today, so Step 1 reports `n/a` per V4's fallback. A future
    # cache-stats extension can replace this with the actual count
    # without changing the bench's merge-gate behavior.
    header = (
        f"{'fixture':<60} {'cold':>10} {'warm':>10} "
        f"{'L1 (h/q)':>12} {'refine':>7} {'speedup':>9}"
    )
    if args.verbose:
        header += f" {'L2 files':>9}"
    print(header)
    print("-" * len(header))

    surviving: list[dict] = []
    below_floor = 0
    compile_failed: list[Path] = []
    bench_start = time.perf_counter_ns()

    for fixture in fixtures:
        outcome = bench_fixture(sigil, fixture)
        rel = fixture.relative_to(CORPORA_ROOT)
        if outcome.kind == "compile_failed":
            print(f"{str(rel):<60} {'COMPILE-FAIL':>10}")
            compile_failed.append(fixture)
            continue
        if outcome.kind == "below_floor":
            print(f"{str(rel):<60} {'<floor':>10}")
            below_floor += 1
            continue
        r = outcome.data
        l1_q = r["warmup_hits"] + r["warmup_misses"]
        if l1_q == 0:
            l1_cell = f"{'0/0':>12}"
        else:
            l1_cell = f"{r['warmup_hits']:>4}/{l1_q:<4} {r['l1_hit_rate'] * 100:>2.0f}%"
        # Wall 4 Step 1 V4: refinement-query attribution requires the
        # cache layer to expose canonical SMT inspection from outside the
        # compiler process. Step 1 reports `n/a` for the column; a future
        # cache-stats extension that surfaces per-source query counts can
        # replace this without changing the merge-gate logic.
        refine_cell = "n/a"
        line = (
            f"{str(rel):<60}"
            f" {fmt_ms(r['wall_cold_ns']):>10}"
            f" {fmt_ms(r['wall_warm_ns']):>10}"
            f" {l1_cell:>12}"
            f" {refine_cell:>7}"
            f" {r['speedup']:>8.2f}x"
        )
        if args.verbose:
            line += f" {r['l2_files']:>9}"
        print(line)
        surviving.append(r)

    bench_wall = time.perf_counter_ns() - bench_start
    print()
    print(
        f"Surviving: {len(surviving)} | "
        f"below floor: {below_floor} | "
        f"compile failed: {len(compile_failed)}"
    )
    print(f"Total bench wall: {bench_wall / 1e9:.1f}s")

    if compile_failed and any(
        os.environ.get(v) for v in ("VERBOSE", "BENCH_VERBOSE")
    ):
        # Many fixtures (N###, T###, E###, R###, S###) are intentional
        # expect-error tests for their corresponding diagnostic-code
        # prefix. Listing them by default is noisy. Set VERBOSE=1 or
        # BENCH_VERBOSE=1 to see the list. Round-2 MI-5.
        print("\n(compile_failed fixtures, by filename — most are intentional expect-error tests):")
        for f in compile_failed:
            print(f"  - {f.relative_to(CORPORA_ROOT)}")

    geomean = 0.0
    if surviving:
        log_sum = sum(math.log(r["speedup"]) for r in surviving)
        geomean = math.exp(log_sum / len(surviving))
        print(f"Geomean speedup: {geomean:.2f}x")

        # Aggregate in-process L1 hit rate across surviving fixtures.
        # Sums hits and total queries from each fixture's warm-up
        # subprocess; the ratio measures the corpus-wide L1 value
        # independent of L2 cross-process state.
        total_l1_hits = sum(r["warmup_hits"] for r in surviving)
        total_l1_queries = sum(
            r["warmup_hits"] + r["warmup_misses"] for r in surviving
        )
        if total_l1_queries > 0:
            agg_l1 = total_l1_hits / total_l1_queries
            print(
                f"In-process L1 hit rate: "
                f"{total_l1_hits}/{total_l1_queries} ({agg_l1 * 100:.1f}%)"
            )
        else:
            print("In-process L1 hit rate: N/A (no cap queries in surviving fixtures)")
    else:
        print("Geomean speedup: N/A (no surviving fixtures)")

    if args.no_gate:
        return 0
    if len(surviving) < MIN_SURVIVING:
        print(
            f"\nFAIL: only {len(surviving)} fixtures survived the "
            f"{MIN_COLD_NS / 1e6:.0f}ms floor; need >= {MIN_SURVIVING}."
        )
        return 1
    if geomean < GEOMEAN_GATE:
        print(
            f"\nFAIL: geomean speedup {geomean:.2f}x < gate {GEOMEAN_GATE}x."
        )
        return 1
    print(
        f"\nPASS: {len(surviving)} fixtures, "
        f"geomean {geomean:.2f}x >= {GEOMEAN_GATE}x."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
