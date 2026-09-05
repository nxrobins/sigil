# Seed provenance

`sigil-seed.wasm` is the SIGIL compiler as a committed binary: the certified with-driver
artifact whose `tool_main` drives the full seven-gate `sh_compile` chain (claims 36–38 in
[docs/CLAIMS.md](../docs/CLAIMS.md)). This file is the one record the CI lane cannot carry:
WHICH run produced WHICH seed. The agreement checks themselves are tests
(`seed_is_the_oracle_emit_of_the_certified_source`, `seed_self_regenerates`); the regeneration
ritual is documented on `seed_regenerate` in
`crates/sigil-runtime/tests/pipeline_differential.rs`.

Rules:

- A **succession** row's seed is the OLD seed's own output on the new certified source,
  committed only after byte-agreement with the Rust oracle's emit. A divergence is a
  trusting-trust alarm — never commit it; find which compiler changed meaning.
- An **emitter-rule succession** row is a two-stage succession: the certified source changed
  what the compiler EMITS (here: export hygiene, only externally callable functions are
  exported), so the old seed's own output on the new source applies the OLD rule and cannot
  agree with the oracle, while the compiler it built implements the new one. That compiler's
  output on the certified source is asserted byte-equal to the oracle's emit AND its own fixed
  point, and only then committed. Lineage is preserved through the stage-one compiler, whose
  digest the row records.
- The **genesis** row is oracle-built. That is HB-1's permanent caveat, stated rather than
  hidden: nothing in the bytes can distinguish seed-built from oracle-built while the two
  agree.

| date (UTC) | event | with-driver source sha256 | seed sha256 | bytes | produced by |
|---|---|---|---|---|---|
| 2026-08-01 | genesis | `4d1bce13cd0e01aeb545f9c5704972f7a1b58cccc774e0de79ae1b5a58085c2a` | `6fe4bc0fbe2e7cc38746225bc9e3275383f5d09a57d85a8f3e34cdd73c9fb914` | 464377 | Rust oracle emit (no prior seed existed) |
| 2026-08-03 | source-only | `48d087cbb183691d56e988047042e0c4bde0156376d9906caac2478c6293e444` | `6fe4bc0fbe2e7cc38746225bc9e3275383f5d09a57d85a8f3e34cdd73c9fb914` | 464377 | unchanged — comment-only source edit, no succession run |
| 2026-09-02 | succession (emitter rule, two stages) | `fa69ab5fc7bbd58dba180432fc49d8cc7b7eff29cfdfa48b9ffe38c00d0cdc94` | `4062f4e19707f9dcaa51c71bb11f9cec73ddbfa2d12c8e38f127c8a3e705ac39` | 454798 | the compiler the old seed built (`ed2d006c4337f199ec34ee0f3dd84b2e8d37f1a782b0de0e7d9e509144c41b23`, 464600 bytes) compiling the certified source; oracle-agreed and its own fixed point |

**On the `source-only` row.** Two comments in `stdlib/sigil/strings.sigil` described `str ==` as
pointer-identity; that stopped being true when `==` began comparing bytes, so they were corrected.
Comments are stripped at lex, so the *source* digest moved while the emitted module did not: the
seed sha and byte count are byte-identical to the genesis row, and `seed_is_the_oracle_emit_of_the_certified_source`
passes against the new source without regeneration.

No succession ritual was run, and none was owed — there was no new seed to produce. The row exists
because the table's second column pins the source the committed seed corresponds to, and that
source changed. Recording it keeps the correspondence auditable instead of leaving a seed whose
stated provenance names a file state that no longer exists.

**On the 2026-09-02 emitter-rule row.** The oracle's `wasm::emit` stopped exporting functions that
are not externally callable (a non-`pub` free function keeps its type, code, and index but has no
export entry), and `selfhost/air.sigil` was taught the same rule. The old seed compiles the new
certified source with the old rule (464600 bytes, every free function exported); that compiler,
which implements the new rule, compiles the same source to 454798 bytes, byte-equal to the oracle's
emit, and reproduces itself. `seed_regenerate` performs exactly this second stage when the first
disagrees and refuses if the second does too.
