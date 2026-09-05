"""THE DDC COMPARISON — `interpret(S)` applied to `S` versus the committed seed.

This is what `interp/` was built for. `docs/CLAIMS.md`'s HB-3 named the residue it could not
close: the second compiler judging the trusting-trust comparison was the Rust oracle itself, so a
backdoor in the oracle sat on both sides of every equality. This script replaces that second
compiler with one whose binary lineage does not pass through the oracle at all.

    S      = the certified with-driver source (digest-pinned; see certified.py)
    seed   = seed/sigil-seed.wasm, the committed compiler binary
    claim  = interpret(S) applied to S  ==  seed

If the seed's BINARY contained logic absent from `S` — Thompson's attack — an interpreter that
only ever does what `S` says would emit different bytes, and this fails.

WHAT IT DOES NOT PROVE, stated here so no one has to rediscover it:

* Authorship independence is not claimed. This was written by reading SIGIL's sources; the threat
  model is logic present in a binary and absent from source, so that is sufficient — but a SHARED
  MISUNDERSTANDING of the language would make both implementations agree and both be wrong. DDC
  never addressed that class; the differential corpus does.
* `Vec` is SUBSTITUTED, not executed (see README). That part of `S` is therefore not run here.
* CPython is itself a toolchain with its own Thompson question. The regress does not terminate;
  what changes is that a successful attack now needs two independently-derived toolchains
  compromised in mutually consistent ways.

    python interp/ddc.py            # the comparison (several minutes)
    python interp/ddc.py --quick    # skip the compile; check wiring and the anti-vacuity witness
"""

from __future__ import annotations

import hashlib
import sys
import time
from pathlib import Path

from certified import verify
from sigil_eval import Interp, SigilError
from sigil_parse import parse

sys.setrecursionlimit(20000)

REPO = Path(__file__).resolve().parent.parent
SEED = REPO / "seed" / "sigil-seed.wasm"

# (No module list here on purpose. `build()` parses `S` itself, so a list of source paths would be
# dead weight that LOOKS load-bearing — editing it would change nothing, silently. The
# identical-looking constant in `test_differential.py` IS load-bearing, which makes the confusion
# easy.)


def build(src: str) -> Interp:
    """Load the program from `S` ITSELF, not from the 17 files it was composed out of.

    Loading the on-disk modules was subtly wrong: it produced 460 functions where `S` has 454,
    because the six strip-list functions are absent from `S` but present in their source files. So
    the program being executed was a strict SUPERSET of the one the digest pinned — the pin covered
    the input TEXT and never the program the interpreter loaded. All six happen to be unreachable
    today, but nothing enforced that, and "interpret(S) applied to S" was not literally what ran.

    Parsing `S` closes the gap by construction: the loaded program is exactly the verified bytes.
    """
    interp = Interp()
    program, _ = parse(src, "<certified>")
    interp.load(program)
    return interp


def compile_with(interp: Interp, source: str) -> str:
    """Drive the loaded compiler over `source`, returning its frozen-protocol output."""
    raw = source.encode()
    toks = interp.call_named("lex", [raw])
    arena = interp.call_fn(interp.methods["Arena"]["new"], [])
    kids: list = []
    root = interp.call_named("parser_parse", [raw, toks, arena, kids])
    interp.call_named("mn_expand", [arena, kids, root])
    return interp.call_named("sh_compile", [arena, kids, root]).decode()


def input_mutation_probe(emitted: bytes, src: str) -> tuple[bool, str]:
    """THE ANTI-VACUITY WITNESS: prove the emission DEPENDS ON THE INPUT.

    Two earlier attempts at this were both vacuous, and the way they failed is worth keeping:

      1. Hashing a tampered copy of the seed against the untampered one. That proved SHA-256
         distinguishes two byte strings — the interpreter's output appeared nowhere in it.
      2. Comparing the emission against a TAMPERED seed. Better, but still vacuous *with respect
         to the verdict*: `tamper(seed) != seed` by construction and the verdict passes only when
         `emitted == seed`, so the check could never fire on a run that was otherwise passing.

    The settling test both failed: stub the interpreter to return the seed's bytes regardless of
    input. Verdict green, witness green, interpreter entirely fake.

    So the witness must vary the INPUT. Feed the compiler a perturbed `S` — the certified source
    plus one extra function, the same append-a-mutant pattern the Rust capstone suite uses — and
    require a different module. An implementation that replays stored bytes emits the same thing
    for both and fails here. The perturbation is applied AFTER the digest check, so it cannot
    disturb the verified input.

    A FRESH interpreter, which is the whole point of taking `src` rather than an `Interp`. Reusing
    the verdict's instance left the input as only ONE of the differences between the two compiles:
    the verdict always ran on a cold interpreter (`bump == 8`, empty const cache, 64 KiB memory)
    and the probe always second on a warm one, so a stub keyed on allocator state or a call
    counter — `if self.bump == 8: return seed_hex` — passed every check while never reading its
    input. Building a second interpreter makes the input the ONLY thing that differs.
    """
    perturbed = src + "\npub fn ddc_input_mutation_probe() -> i64 { return 0; }\n"
    probe_interp = build(perturbed)
    out = compile_with(probe_interp, perturbed)
    if not out.startswith("OK:"):
        return False, f"the perturbed source was REJECTED ({out[:120]}) — the probe is inconclusive"
    produced = bytes.fromhex(out[3:])
    # Not merely DIFFERENT: a real module. Otherwise an implementation that emits garbage for
    # anything that is not `S` would satisfy an inequality test.
    if not produced.startswith(b"\x00asm"):
        return False, "the perturbed source did not produce a WASM module — the emission is not "
    if produced == emitted:
        return False, "a PERTURBED source produced identical bytes — the emission does not depend "
    if probe_interp.steps < 1_000_000:
        return False, (
            f"the probe compile ran only {probe_interp.steps:,} steps, far too few to have "
            f"compiled 1.15 MB — the emission is not "
        )
    return True, ""


def main() -> int:
    quick = "--quick" in sys.argv

    # The seed is checked for EXISTENCE here but deliberately NOT read yet. "The artifact under
    # test is never an input to the compile" was true before, but only by review — the bytes sat
    # in scope for the whole function and every use had to be traced to confirm none reached the
    # interpreter. Reading it after the compile makes that property structural: there is no
    # variable to misuse, so the guarantee holds by construction rather than by audit.
    if not SEED.exists():
        print(f"missing committed seed: {SEED}", file=sys.stderr)
        return 1

    src = verify()
    print(f"source : {len(src.encode()):,} bytes, digest verified against the pin")
    if quick:
        # Exit NON-ZERO on purpose. This flag exists to check wiring while developing, and the
        # contract of this script is one comparison; returning 0 for having skipped it would make
        # `python interp/ddc.py --quick` a green CI step that proves nothing.
        print("--quick: wiring checked, comparison SKIPPED — not a pass", file=sys.stderr)
        return 2

    interp = build(src)
    started = time.perf_counter()
    try:
        out = compile_with(interp, src)
    except (SigilError, RecursionError) as e:
        print(f"the interpreter could not compile the certified source: {e}", file=sys.stderr)
        return 1
    elapsed = time.perf_counter() - started

    if not out.startswith("OK:"):
        print(f"the interpreter REJECTED the certified source: {out[:200]}", file=sys.stderr)
        return 1
    emitted = bytes.fromhex(out[3:])
    emitted_digest = hashlib.sha256(emitted).hexdigest()
    print(
        f"emitted: {len(emitted):,} bytes, sha256 {emitted_digest} "
        f"({elapsed:.0f}s, {interp.steps:,} steps)"
    )

    # ONLY NOW is the artifact under test read — after the bytes it is compared against already
    # exist. Nothing above this line could have consulted it.
    seed = SEED.read_bytes()
    print(f"seed   : {len(seed):,} bytes, sha256 {hashlib.sha256(seed).hexdigest()}")

    # SC-P4 on the VERDICT ITSELF — see `input_mutation_probe` for the two vacuous witnesses this
    # replaces and the stub that defeated both.
    probe_started = time.perf_counter()
    ok, why = input_mutation_probe(emitted, src)
    if not ok:
        print(f"ANTI-VACUITY FAILED: {why}on its input.", file=sys.stderr)
        return 1
    print(
        f"witness: a perturbed source emits DIFFERENT bytes — the output depends on the input "
        f"({time.perf_counter() - probe_started:.0f}s)"
    )

    if emitted != seed:
        print()
        print("DDC MISMATCH — the interpreter's emission differs from the committed seed.")
        print("  This is a trusting-trust ALARM if the source is unchanged: either the seed's")
        print("  binary contains logic absent from its source, or this interpreter disagrees")
        print("  with the compiler about the language. Do not overwrite the seed; find which.")
        first = next(
            (i for i, (a, b) in enumerate(zip(emitted, seed, strict=False)) if a != b), None
        )
        print(f"  sizes {len(emitted):,} vs {len(seed):,}; first differing offset: {first}")
        return 1

    print()
    print("DDC HOLDS: interpret(S) applied to S reproduces the committed seed byte-for-byte.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
