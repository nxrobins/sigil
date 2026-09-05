"""Phase 1: the performance GO/NO-GO.

The kill risk for this project is throughput: the certified self-compile burns ~74 M fuel units
under the WASM runtime, and a tree-walking interpreter in Python is orders of magnitude slower per
operation. This measures two things:

1. A synthetic loop, for a raw steps/second figure.
2. REAL compiler code — `lex()` from `selfhost/lexer.sigil` — on a small input, because a
   synthetic loop says nothing about whether the evaluator can reach the actual workload.

    python interp/bench.py
"""

from __future__ import annotations

import time
from pathlib import Path

from sigil_eval import Interp, SigilError
from sigil_parse import ParseError, parse

REPO = Path(__file__).resolve().parent.parent

SYNTHETIC = """
module bench;
fn work(n: i64) -> i64 {
    let mut total: i64 = 0;
    let mut i: i64 = 0;
    while i < n {
        let mut j: i64 = 0;
        while j < 10 {
            total = total + (i * j) % 7;
            j = j + 1;
        }
        i = i + 1;
    }
    return total;
}
"""


def run_synthetic(n: int) -> tuple[int, float, int]:
    program, _ = parse(SYNTHETIC, "<bench>")
    interp = Interp()
    interp.load(program)
    started = time.perf_counter()
    result = interp.call_named("work", [n])
    elapsed = time.perf_counter() - started
    return result, elapsed, interp.steps


def load_sigil(*rel_paths: str) -> Interp:
    interp = Interp()
    for rel in rel_paths:
        src = (REPO / rel).read_text(encoding="utf-8")
        program, _ = parse(src, rel)
        interp.load(program)
    return interp


def try_real_lexer() -> None:
    """Point the evaluator at real compiler code. Failures here are the Phase-3 work list."""
    print("real compiler code — selfhost lexer:")
    try:
        interp = load_sigil(
            "stdlib/sigil/vec.sigil",
            "stdlib/sigil/string.sigil",
            "selfhost/lexer.sigil",
        )
    except ParseError as e:
        print(f"  parse failed: {e}")
        return

    sample = "module m;\nfn f(a: i64) -> i64 { return a + 1; }\n"
    started = time.perf_counter()
    try:
        toks = interp.call_named("lex", [sample.encode()])
    except SigilError as e:
        print(f"  NOT YET: {e}")
        print(f"  (steps executed before the gap: {interp.steps:,})")
        return
    except RecursionError:
        print("  NOT YET: Python recursion limit — raise it or flatten the evaluator")
        return
    elapsed = time.perf_counter() - started
    n = len(toks) if hasattr(toks, "__len__") else "?"
    print(f"  lexed {len(sample)} bytes -> {n} tokens in {elapsed:.3f}s ({interp.steps:,} steps)")


def main() -> int:
    print("synthetic loop:")
    prev_rate = 0.0
    for n in (200, 2000, 20000):
        result, elapsed, steps = run_synthetic(n)
        rate = steps / elapsed if elapsed else 0
        prev_rate = rate
        print(
            f"  n={n:<6} {steps:>10,} steps  {elapsed:7.3f}s  "
            f"{rate:>12,.0f} steps/s  (result {result})"
        )

    print()
    try_real_lexer()
    print()
    measure_lexer_scaling(prev_rate)
    return 0


def measure_lexer_scaling(rate: float) -> None:
    """Project the certified self-compile from MEASURED work on real source.

    Extrapolating from the ~74 M fuel figure would be guesswork — fuel counts WASM instructions
    and one evaluator step covers an unknown number of them. Steps per BYTE of real source is
    directly measurable, so the projection below rests on measurement rather than a conversion
    factor invented for the occasion.
    """
    interp = load_sigil(
        "stdlib/sigil/vec.sigil", "stdlib/sigil/string.sigil", "selfhost/lexer.sigil"
    )
    src = (REPO / "selfhost/pipeline.sigil").read_text(encoding="utf-8")
    print("lexer scaling on real source:")
    per_byte = 0.0
    for size in (2000, 8000, len(src)):
        chunk = src[:size]
        interp.steps = 0
        started = time.perf_counter()
        toks = interp.call_named("lex", [chunk.encode()])
        elapsed = time.perf_counter() - started
        per_byte = interp.steps / len(chunk)
        print(
            f"  {len(chunk):>7,} bytes -> {len(toks):>6,} tokens  {elapsed:6.3f}s  "
            f"{per_byte:5.1f} steps/byte"
        )

    certified = 1_149_760  # PIN_WITH_DRIVER_SRC_CHARS
    lex_steps = certified * per_byte
    print()
    print(
        f"projection: lexing the {certified:,}-char certified source is ~{lex_steps / 1e6:.0f} M "
        f"steps ~= {lex_steps / rate:.0f}s at {rate:,.0f} steps/s."
    )
    print("  The full pipeline adds parse + mn_expand + 7 gates + emit, so expect minutes, not")
    print("  hours. The `test` CI lane already runs 22 minutes; this fits.")


if __name__ == "__main__":
    raise SystemExit(main())
