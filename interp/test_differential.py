"""Phase 2: the differential harness.

Both sides execute the SAME SIGIL source — `selfhost/lexer.sigil`'s `encode(lex(src))`. Only the
machine underneath differs: wasmtime on the Rust side, this tree-walking evaluator here. So a
disagreement is an interpreter-semantics bug, which is exactly what this exists to surface.

The answer key is `corpus/golden.json`, produced and kept current by
`crates/sigil-runtime/tests/interp_corpus.rs` — this side only ever reads it, because an
implementation that computed its own reference answers would be grading its own homework.

    python interp/test_differential.py           # report + ratchet check
    python interp/test_differential.py --verbose # show each mismatch
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from sigil_eval import Interp, SigilError
from sigil_parse import ParseError, parse

sys.setrecursionlimit(20000)

REPO = Path(__file__).resolve().parent.parent
GOLDEN = Path(__file__).resolve().parent / "corpus" / "golden.json"

# The interpreter must reproduce at least this many golden checks. RATCHET: raise it as coverage
# grows; lowering it means a regression and must be argued for, not typed.
# 15 -> 30 (PARSE) -> 45 (NAME RESOLUTION) -> 60 (the WHOLE COMPILER, `sh_compile`, emitted WASM
# bytes included). 15 fixtures x lex+parse+nr+compile.
PASS_FLOOR = 60

# Everything except `Vec` runs as real SIGIL — including `Arena`, whose record-over-Vec storage
# is what the parser builds its node tree in.
SOURCES = (
    "stdlib/sigil/vec.sigil",
    "stdlib/sigil/arena.sigil",
    "stdlib/sigil/string.sigil",
    "stdlib/sigil/strings.sigil",
    "stdlib/sigil/option.sigil",
    "selfhost/lexer.sigil",
    "selfhost/parser.sigil",
    "selfhost/name_resolution.sigil",
    "selfhost/typecheck.sigil",
    "selfhost/ring_check.sigil",
    "selfhost/effect_check.sigil",
    "selfhost/taint_check.sigil",
    "selfhost/cap_check.sigil",
    "selfhost/own_check.sigil",
    "selfhost/air.sigil",
    "selfhost/monomorph.sigil",
    "selfhost/pipeline.sigil",
)


def build() -> Interp:
    interp = Interp()
    for rel in SOURCES:
        program, _ = parse((REPO / rel).read_text(encoding="utf-8"), rel)
        interp.load(program)
    return interp


def main() -> int:
    verbose = "--verbose" in sys.argv
    if not GOLDEN.exists():
        print(f"missing {GOLDEN}", file=sys.stderr)
        print("generate it: cargo test -p sigil-runtime --test interp_corpus regenerate "
              "-- --ignored --nocapture", file=sys.stderr)
        return 1

    fixtures = json.loads(GOLDEN.read_text(encoding="utf-8"))
    if not fixtures:
        print("the golden corpus is EMPTY — it would grade nothing", file=sys.stderr)
        return 1

    # THE SHAPE OF THE KEY MUST NOT DECIDE THE WORKLOAD. Each layer below skips when its expected
    # value is absent, and the denominator is computed from those same keys — so a generator that
    # emitted no `compiled` fields would silently drop the most expensive comparison and still
    # print a clean "N/N reproduce the oracle". Require every fixture to carry every layer, with
    # the layer list fixed HERE rather than read from the data.
    REQUIRED = ("source", "encoded", "parsed", "resolved", "compiled")
    thin = [
        f"{fx.get('name', '?')}: missing {sorted(set(REQUIRED) - set(fx))}"
        for fx in fixtures
        if not set(REQUIRED).issubset(fx)
    ]
    # `empty` legitimately has no parse/nr/compile output — it is the one fixture with no program.
    thin = [t for t in thin if not t.startswith("empty:")]
    if thin:
        print(
            "the golden corpus is THIN — these fixtures would silently skip layers:",
            file=sys.stderr,
        )
        for t in thin:
            print(f"  {t}", file=sys.stderr)
        return 1

    interp = build()
    passed: list[str] = []
    failed: list[tuple[str, str]] = []

    for fx in fixtures:
        name, source = fx["name"], fx["source"]
        # LEX half.
        try:
            interp.steps = 0
            toks = interp.call_named("lex", [source.encode()])
            got = interp.call_named("encode", [toks]).decode()
        except (SigilError, ParseError, RecursionError) as e:
            failed.append((f"{name}:lex", f"{type(e).__name__}: {e}"))
            continue
        if got == fx["encoded"]:
            passed.append(f"{name}:lex")
        else:
            failed.append(
                (f"{name}:lex", f"differs\n      want {fx['encoded']!r}\n      got  {got!r}")
            )

        # PARSE half — the layer every checker consumes, so agreement here is what makes the
        # later phases meaningful.
        if "parsed" not in fx or not fx["parsed"]:
            continue
        try:
            arena = interp.call_fn(interp.methods["Arena"]["new"], [])
            kids: list = []
            root = interp.call_named("parser_parse", [source.encode(), toks, arena, kids])
            got_parse = interp.call_named("parser_encode", [arena, kids, root]).decode()
        except (SigilError, ParseError, RecursionError) as e:
            failed.append((f"{name}:parse", f"{type(e).__name__}: {e}"))
            continue
        if got_parse == fx["parsed"]:
            passed.append(f"{name}:parse")
        else:
            failed.append(
                (
                    f"{name}:parse",
                    f"differs\n      want {fx['parsed'][:160]!r}\n      got  {got_parse[:160]!r}",
                )
            )

        # NAME-RESOLUTION half — the first checker GATE, where the interpreter starts reproducing
        # verdicts rather than syntax.
        if not fx.get("resolved"):
            continue
        try:
            got_nr = interp.call_named("nr_encode", [arena, kids, root]).decode()
        except (SigilError, ParseError, RecursionError) as e:
            failed.append((f"{name}:nr", f"{type(e).__name__}: {e}"))
            continue
        if got_nr == fx["resolved"]:
            passed.append(f"{name}:nr")
        else:
            failed.append(
                (
                    f"{name}:nr",
                    f"differs\n      want {fx['resolved'][:160]!r}\n      got  {got_nr[:160]!r}",
                )
            )

        # THE WHOLE COMPILER — `sh_compile`'s frozen protocol (`OK:<hex>` / `REJECT:<stage>:...`).
        # Agreement here means the interpreter reproduces the compiler's OUTPUT BYTES, which is
        # the comparison the Phase-5 DDC argument rests on.
        if not fx.get("compiled"):
            continue
        try:
            interp.call_named("mn_expand", [arena, kids, root])
            got_c = interp.call_named("sh_compile", [arena, kids, root]).decode()
        except (SigilError, ParseError, RecursionError) as e:
            failed.append((f"{name}:compile", f"{type(e).__name__}: {e}"))
            continue
        if got_c == fx["compiled"]:
            passed.append(f"{name}:compile")
        else:
            failed.append(
                (
                    f"{name}:compile",
                    f"differs\n      want {fx['compiled'][:120]!r}\n      got  {got_c[:120]!r}",
                )
            )

    # SC-P4. A differential that reports 45/45 is only evidence if it CAN report a failure. Feed
    # the interpreter a deliberately perturbed source and require the comparison to notice: if a
    # changed program still matched its golden, this harness would be grading nothing.
    probe = fixtures[0]
    perturbed = probe["source"] + "\nfn interp_antistub_probe() -> i64 { return 0; }\n"
    try:
        toks = interp.call_named("lex", [perturbed.encode()])
        probe_enc = interp.call_named("encode", [toks]).decode()
    except SigilError as e:
        print(f"anti-stub probe failed to run: {e}", file=sys.stderr)
        return 1
    if probe_enc == probe["encoded"]:
        print(
            "ANTI-STUB FAILED: a perturbed source produced the golden encoding, so this "
            "differential cannot distinguish anything.",
            file=sys.stderr,
        )
        return 1

    layers = ("parsed", "resolved", "compiled")
    total = sum(1 + sum(1 for k in layers if fx.get(k)) for fx in fixtures)
    print(
        f"differential: {len(passed)}/{total} checks reproduce the oracle "
        f"({len(fixtures)} fixtures x lex+parse+nr+compile)"
    )
    if failed:
        print()
        for name, why in failed:
            print(f"  FAIL {name}: {why if verbose else why.splitlines()[0]}")

    # ANY failure fails the run. The floor alone is not enough: it is an absolute count against a
    # GROWING denominator, so once the corpus gains fixtures it would tolerate exactly as many
    # broken checks as were added — silently, while the ledger says every check passes.
    if failed:
        print()
        print(f"{len(failed)} check(s) FAILED — the interpreter disagrees with the oracle.")
        return 1

    # The floor stays as the COVERAGE ratchet: it catches checks that vanish (a shrunken corpus,
    # a skipped layer) rather than checks that fail.
    if len(passed) < PASS_FLOOR:
        print()
        print(
            f"RATCHET: {len(passed)} passing is below the floor of {PASS_FLOOR}. Coverage "
            f"shrank — a fixture or a whole layer stopped being compared."
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
