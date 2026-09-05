# The SIGIL Lexer, in SIGIL — Implemented

**Status:** ✅ Implemented (Stage 0 shipped, PR-0 … PR-3b) — the first self-hosting stage.
The SIGIL lexer (`selfhost/lexer.sigil`) tokenizes every `stdlib/sigil/*.sigil` file — and
its own lexical errors — **token-for-token, value-for-value, and diagnostic-for-diagnostic**
identically to the Rust `lex_with_id` oracle, proven by `crates/sigil-runtime/tests/lexer_differential.rs`.
**Date:** 2026-06-09 (design) · 2026-06-10 (implemented)
**Authors:** Nigel Robinson
**Shape decision:** batch — `lex(src: str) -> Vec<Token>` (not the streaming iterator form).

---

## 1. Context & Goal

Every COMPLETENESS prerequisite the self-hosted compiler named is now shipped — strings
(borrowing + owned), `Vec`/`Map`, records/enums, traits, iteration, `break`/`continue`, and
tuples (`(token, pos)` multi-return). The next concrete step is **Stage 0: write the SIGIL
lexer as a SIGIL program**, compiled by the current Rust compiler to wasm.

> **Goal.** A SIGIL function `lex(src: str) -> Vec<Token>` whose output, on every `.sigil`
> source in a corpus, is **token-for-token identical** to the Rust lexer's
> (`crate::lexer::lex_with_id`). The Rust lexer is the differential oracle — not a fuzzy
> spec but the exact, executable definition of "correct."

This is the marquee dogfood: it proves SIGIL can express a real compiler stage, and it
stress-tests strings/`Vec`/enums/`match` against a non-toy program. It does **not** replace
the Rust lexer in the pipeline yet (that's a later bootstrap stage); it runs alongside it as
a tested artifact.

**Why batch (`-> Vec<Token>`), not the iterator form.** A batch lexer is a pure function of
its input — trivially differential-testable (run both lexers, compare the two `Vec`s), no
cursor state to thread, and it sidesteps the iterator's `@Mut self` cursor ergonomics. The
streaming `next(self @Mut) -> Option<Token>` form is a clean follow-on once the batch lexer
is byte-correct (it would wrap the same scan logic), but the batch shape is the right first
target.

---

## 2. The Target (the token model to reproduce)

The Rust lexer (`crates/sigil-compiler/src/lexer.rs`, ~518 lines) emits ~**92 `TokenKind`
variants**:

- **Literals (carry data):** `IntLit(i64)`, `FloatLit(f64)`, `StrLit(String)`, `BoolLit(bool)`.
- **Identifier (carries data):** `Ident(String)`.
- **Keywords (~45 unit variants):** `actor ask cap const declassify declassify_ct distinct
  else effect entry enum extern fn for handle if impl in init let match module mut on break
  continue pub grant ring record region return send spawn state supervision trait type use
  while with` (+ `true`/`false` → `BoolLit`).
- **Operators / punctuation / delimiters (~40 unit variants):** the single-char set (`+ - *
  / % = < > & | . ? ! : ; , ( ) { } [ ] # @`), the compound set (`+= -= *= /= %= == != <= >=
  << <<= >> >>= &= |= -> => :: .. ..=`).
- **`Eof`** — always the final token.

`Token { kind: TokenKind, span: Span }`; `Span { start: usize, end: usize, source: SourceId }`
(byte offsets). Lexer behavior to mirror exactly:

- **Whitespace** (space/`\t`/`\r`/`\n`) skipped, no token.
- **Line comments** `// … \n` skipped; **no block comments**.
- **Numbers:** decimal + `0x` hex → `IntLit`; a digit run followed by `.` **and another
  digit** → `FloatLit` (so `1.0` is a float but `1.method` / `1..2` keep the `.` separate —
  the same `.0`-disambiguation SIGIL tuples deferred).
- **Strings:** `"…"` with escapes `\" \\ \n \t`; UTF-8 bytes preserved; unterminated → error.
- **Diagnostics:** L001 (int parse/overflow), L002 (float parse), L003 (unterminated string),
  L004 (unexpected char). (L010 invalid-UTF-8 is pre-lexing — out of scope; `from_bytes`
  already enforces UTF-8 at the boundary.)

---

## 3. The SIGIL Representation

```sigil
// Token kinds. Data-carrying variants hold their payload; the rest are unit.
// NOTE: keywords and operators can ALSO be modeled as data on one `Kw(i64)` /
// `Op(i64)` variant carrying a tag — see §5 on enum-arity pragmatics.
enum TokenKind {
    Ident(str),       // a substr VIEW into the source (zero-copy)
    IntLit(i64),
    FloatLit(f64),
    StrLit(str),      // the literal's text (see §6 on escapes)
    BoolLit(bool),
    Kw(i64),          // keyword id (a stable enumeration; see §5)
    Op(i64),          // operator/punctuation id
    Eof,
}

record Token {
    kind: TokenKind,
    start: i64,       // byte offset, inclusive
    end: i64,         // byte offset, exclusive  (src.substr(start, end) recovers the lexeme)
}

fn lex(src: str) -> Vec<Token> ! { Alloc } {
    let mut toks: Vec<Token> = Vec::new();
    let mut i: i64 = 0;
    let n: i64 = src.len();
    while i < n {
        let b: i64 = src.byte_at(i);
        // dispatch on b: whitespace / comment / digit / quote / ident-start / operator
        // … push Token { kind, start, end } ; advance i …
    }
    toks.push(Token { kind: TokenKind::Eof, start: n, end: n });
    return toks;
}
```

- **`Vec<Token>` is proven.** The L0 spike (`crates/sigil-runtime/tests/lexer_spike.rs`, on
  main) already pinned that a multi-field `Token` record round-trips through `Vec<Token>`
  push/get with every field intact, across reallocs. No runtime gap.
- **Lexemes are `substr` views.** `Ident`/`StrLit` payloads and every token's `[start, end)`
  are zero-copy views into `src` — the lexer allocates only the `Vec<Token>` spine.
- **The scan loop is the proven `str_find` shape** — `while i < n { let b = src.byte_at(i);
  … }` with sentinel/`break` exits. (The stdlib's own `str_find` is exactly this style.)

---

## 4. The differential-test harness (the north star)

The Rust lexer IS the spec. The test, per corpus source `S`:

1. **Reference:** `let (ref_tokens, _) = lex_with_id(SourceFile::from(S), id);`
2. **Subject:** compile + run the SIGIL `lex(S)` tool; recover its token stream.
3. **Compare:** assert the two streams are equal (kind tag + start + end, token-by-token),
   reporting the **first divergent index** on mismatch.

The bottleneck is the i64 tool-return. Two tiers:

- **Tier 1 — full-fidelity decode (primary).** The tool serializes its `Vec<Token>` into a
  byte buffer — `[count, (tag, start, end) × count]` as i64s — and returns the **positive
  packed pointer** (`ptr<<32 | byte_len`) that `execute_ephemeral` already memory-reads into
  `ToolResult.output`. The host decodes the buffer and compares each `(tag, start, end)`
  against `lex_with_id`'s tokens (via a `TokenKind → tag` map). Pinpoints the first
  divergence — essential for a useful lexer diff. Uses the EXISTING positive-return path, no
  new harness machinery.
- **Tier 2 — checksum smoke gate (fast).** The tool folds the stream into one i64
  (`count * P ⊕ Σ fold(tag, start, end)`) and returns `0 - checksum`; the host recomputes the
  same fold over `lex_with_id`'s tokens. Cheap per-fixture verdict; the Tier-1 decode runs on
  mismatch (and in CI) for the actual diff.

**Corpus.** A curated `tests/lexer_corpus/` (keywords, every operator, ints/hex/floats incl.
the `.0` edge, strings with each escape, line comments, mixed whitespace, the empty source,
an unterminated string for the error path) PLUS the real `stdlib/sigil/*.sigil` files (the
ultimate "lex what we actually write" test). Optionally fold into `workload_snapshots`'
corpus-walk infra for golden snapshots.

---

## 5. The keyword-equality problem (the load-bearing decision)

> **Since shipped (PR #699):** AG-S1-M is closed — `str ==` now byte-compares
> (`emit_str_bytes_eq`: length check + fuel-metered scan), so the constraint this section
> designs around no longer exists. The section stands as the record of WHY the lexer uses
> `bytes_eq`; the helper is behaviorally identical to today's `==`, and the certified source
> is fenced to zero `str ==` uses, so nothing below needed to change.

**At the time, `str ==` and `match` on a `str` literal compared `data_ptr`, NOT bytes**
(`air.rs` `emit_str_data_ptr_eq`; the byte-compare fallback was the deferred **AG-S1-M**).
Two `"fn"` literals at distinct sites were unequal, and — fatally for a lexer — a `substr`
**view** of an identifier was never `==` a keyword literal even when the bytes matched. So
keyword recognition **could not** be `if lexeme == "fn"`. The L0 spike proved this and the
workaround:

> `lexeme.len() == klen && lexeme.starts_with(kw)` ⟺ byte-equality. `starts_with` byte-compares
> (it scans via `byte_at`), and the length guard rejects a proper prefix (`"fnx"` vs `"fn"`).

**Decision — wrap it once as `str.bytes_eq`.** Add a stdlib helper (pure SIGIL, **zero
compiler change**, built on the proven primitives):

```sigil
pub fn str_bytes_eq(self: str @ReadOnly, other: str @ReadOnly) -> bool {
    if self.len() == other.len() { return self.starts_with(other); } else { return false; }
}
```

Keyword recognition is then a chain over a **named-constant table** (`const KW_FN: i64 = 1;
const KW_LET: i64 = 2; …`), bucketed by **first byte and length** before any `bytes_eq` call:

```sigil
// dispatch on the lexeme's first byte + length BEFORE the byte-compares, so a
// non-keyword identifier fails in O(1) and never pays for ~45 bytes_eq calls.
if klen == 2 {
    if b0 == 102 { if lexeme.bytes_eq("fn") { return TokenKind::Kw(KW_FN); } else { } } else { }
    if b0 == 105 { if lexeme.bytes_eq("if") { return TokenKind::Kw(KW_IF); } else { } } else { }
    …
} else { }
return TokenKind::Ident(lexeme);
```

The bucketing is **not** a premature optimization — per R7 each `bytes_eq` is a *fuel-charged
function call*, and the dominant runtime term is keyword matching; a flat 45-way scan would pay
~45 calls for every identifier. First-byte/length dispatch makes the common case (a plain
identifier) O(1). The `KW_*`/`OP_*` constants are a **named table, never raw numbers** — and
they are the **contract** between the SIGIL lexer's output encoding (§4) and the Rust
differential harness's `TokenKind → tag` map, so they get a drift-guard (R6).

**Alternative (deferred then; since shipped as PR #699) — fix `str ==` to byte-compare**
(close AG-S1-M in the compiler). Cleaner long-term (it also makes `Map<str, V>` work with
constructed/view keys, and lets the lexer use a `match`/`Map` keyword table), but it is a
compiler change with its own byte-identity gate. v1 took the stdlib-helper path; the compiler
fix landed later, with a fence pinning the certified source to zero `str ==` — so the lexer's
`bytes_eq` path, and its emitted bytes, were untouched by it.

**This makes `str.bytes_eq` Prerequisite PR-0** of the lexer epic.

---

## 6. Mechanism details & SIGIL constraints

The scan dispatches on the lead byte `b = src.byte_at(i)`:

- **Whitespace** (`32`/`9`/`10`/`13`) → advance, no token.
- **`/` then `/`** → line comment: advance to the next `10` (`\n`) or EOF.
- **digit** (`48..=57`) → number scan: consume digits; `0x` → hex; a `.` followed by a digit
  → consume the fraction into a `FloatLit`, else stop (the `.` is a separate `Op`). Recover
  the lexeme with `substr`, `parse_i64` for the int value. (Float value parsing has no
  stdlib `parse_f64` yet — see Risks.)
- **`"`** → string scan: advance to the closing `"`, honoring `\` escapes; unterminated → the
  L003-equivalent error path.
- **ident-start** (`A..=Z`/`a..=z`/`_`) → consume ident bytes; `substr` the lexeme; keyword
  table via `bytes_eq` (§5), else `Ident`.
- **operator/punctuation** → maximal-munch with 1–2 byte lookahead (`src.byte_at(i+1)`),
  mirroring the Rust lexer's `double_or_single` + the `.`/`<`/`>` three-way chains.

**SIGIL constraints that shape the code** (all confirmed; the scan style is the stdlib's own
`str_find`):

- **No method-chaining on a method result** — bind a `let` first (`let p = s.find(x);` then
  use `p`). Pervasive in the operator/number branches.
- **`if` needs an explicit `else { }`**; a value-returning helper must `return` on every path.
- **No `&&`/`||`** — multi-byte operator checks and the keyword `len && starts_with` use
  nested `if`. (`bytes_eq` hides the keyword case behind one call.)
- **`break`/`continue` ARE available** (shipped #228) — the inner scans (comment/string/number
  runs) can `break` on the terminator rather than the older sentinel-counter trick.
- **Tuples have no `.0`** — internal `(value, new_pos)` helpers destructure with
  `let (v, j) = …`; never `pair.0`.
- **`Vec<T>` element type comes from the binding** — `let mut toks: Vec<Token> = Vec::new();`.

---

## 7. Staging plan (the PR ladder)

Each stage is a shippable PR; each grows the differential corpus it must pass.

- **PR-0 — `str.bytes_eq` + the L0 spike gates.** ✅ shipped (#232) — the stdlib helper (§5)
  + the L0 spike's `bytes_eq` gates. *No lexer — just the byte-eq enabler.*
- **PR-1a — the transfer + a minimal lexer + the differential pipeline.** ✅ shipped — the
  `s.as_output()` inner-ring intrinsic (the token-stream transfer, see findings below), a
  minimal `lex(src) -> Vec<Token>` (`selfhost/lexer.sigil`: idents, decimal ints, single-char
  operators/delimiters, whitespace, Eof), and the differential harness — the tool returns
  `encode(lex(src)).as_output()` (`tag,start,end;…`) and the host compares token-by-token
  (tag + start + end) against the Rust `lex` oracle (ET-2), on a curated keyword-free corpus.
  The "self-hosting mechanics proven end-to-end" milestone.
- **PR-1b — broaden the core.** ✅ shipped — the full 41-keyword set (length-bucketed
  `bytes_eq` dispatch) + BoolLit, all 24 single-char operators/delimiters, and line comments;
  tags named via `const`. The ET property suite landed: **ET-1** coverage manifest (every
  emitted tag hit by the corpus), **ET-4** span-tiling (oracle-independent), **ET-7** fuzz
  no-trap, **ET-8** determinism, and **ET-9** the TOTAL `tag_of` (no `_` arm — a new Rust
  `TokenKind` fails to compile until mapped). The corpus grew to keyword-rich SIGIL-ish soup
  (operator bytes kept non-adjacent, since multi-char munch is PR-2).
- **PR-2 — literals & multi-char operators.** Split into three shipped slices:
  - **PR-2a** ✅ (#236) — multi-char operator maximal munch (`scan_op` returning a `(tag, len)`
    tuple, dogfooding tuples): all 20 compound operators `-> => :: == != <= >= << <<= >> >>= &=
    |= += -= *= /= %= .. ..=`, tested both space-separated and packed against idents/ints.
  - **PR-2b** ✅ (#237) — numeric literals: decimal + hex `IntLit` (decoded i64 value) and
    `FloatLit` (span only, AG-L3). Introduced **ET-3 value equality** — the differential now
    compares the decoded `value` (the i64; `1`/`0` for `BoolLit`), not just the span.
  - **PR-2c** ✅ (#238) — string literals + the four escapes (`\" \\ \n \t`) + the
    unknown-escape-keeps-char rule; the decoded value is shipped via a length-prefixed pool
    channel and compared byte-for-byte (ET-3 for `StrLit`), including non-ASCII content. After
    2c the `tag_of` map is total with no `UNHANDLED` — the whole token vocabulary is covered.
- **PR-3 — the stdlib corpus & diagnostics.** Split into two shipped slices:
  - **PR-3a** ✅ (#239) — the **full `stdlib/sigil/*.sigil` differential corpus** (the "done"
    line): all 17 real files lex identically. Surfaced + fixed an O(tokens²) harness encoder
    (rewritten to `Vec<str>` + one ambient `join`, O(n); ~127 s → ~5 s).
  - **PR-3b** ✅ (#240) — the L001/L003/L004 lexer diagnostics as in-stream **error-tokens**
    (`T_ERR`, `value` = L-code, oracle-matching span); the host splits them out and asserts both
    error recovery (the real-token stream still matches) and the diagnostics (code + span,
    AG-L4). The int/hex-overflow + invalid-float (L002) sub-cases are deferred (AG-L6).
- **PR-N — docs + roadmap flip** ✅ — Status: Design → Implemented; the Tier 8-10 lexer row.

Streaming `next()`-iterator form and actually swapping the SIGIL lexer into the pipeline are
**post-v1** (the Arc Beyond).

### PR-1a findings (the transfer, the ring wall, the const gap)

- **Transfer = `s.as_output()`, an inner-ring intrinsic.** §4's "serialize + return a packed
  pointer" is realized by a new compiler intrinsic that packs a built `str`'s header into the
  forge ABI's positive return `(data_ptr << 32) | len`; the host reads the bytes via the
  existing positive-return memory path. WHY an intrinsic and not the FFI shim first attempted:
  the lexer needs **inner**-ring stdlib (`Vec`/strings), FFI is **outer**-ring, and a tool
  can't be both (`R004` cross-ring). `as_output` is inner-ring, FFI-free, and exposes no
  dereferenceable pointer to user code (only the packed return). The tool builds its encoding
  with inner-ring `concat`/`itoa`.
- **`const` is now usable as a value (gap closed).** A module-level `const NAME: T = LIT;` was
  previously declaration-only — a reference was `undefined local` (T060: `ConstDef` was
  type-checked but never bound). It now inlines its declared literal: `collect_type_universe`
  populates `universe.consts`, and `infer_path_expr` resolves a bare reference to the literal
  (no new AIR — a literal lowers normally). The lexer **dogfoods** it — named token tags
  (`T_LPAREN` …) instead of magic numbers; the tag values are the harness contract
  (drift-guarded in PR-1b/ET-9). A real self-hosting gap (the compiler will want named tags /
  node-kinds throughout), surfaced by writing real SIGIL and closed here.

### PR-2/3 findings (string building, the encoder, the diagnostic channel)

- **`substr` is char-boundary-checked — build strings a codepoint at a time (PR-2c).** The AIR
  enforces UTF-8 boundaries on `substr`: a slice whose start/end lands inside a multi-byte
  codepoint traps. So a string scanner can't assemble a non-ASCII value byte-by-byte; it must
  read the lead byte, compute the codepoint length (`utf8_len`), and `substr` the whole
  codepoint. This is the general rule for any hand-written SIGIL that copies arbitrary source
  text — slice on boundaries, never mid-codepoint.
- **Immutable-string `concat` is O(n²) — accumulate in a `Vec<str>` and `join` once (PR-3a).**
  Building a large string by repeated `out = out.concat(piece)` recopies the growing buffer
  every step; the stdlib corpus exposed it as a 127 s test. `str_join` (ambient as `.join`)
  pre-sums the total length and allocates exactly once, so collecting records into a `Vec<str>`
  and joining is O(total) — 127 s → 5 s. The lesson generalizes to the parser's output builders.
- **The error-token diagnostic channel (PR-3b).** A lexer must report errors, but the oracle
  emits a diagnostic and NO token where SIGIL's `lex` returns only `Vec<Token>`. Rather than
  change the signature, an error becomes an in-stream **error-token** (`T_ERR`, `value` = L-code,
  span = the error span); the host splits error-tokens out, so the real-token stream still
  matches the oracle's tokens (error recovery) and the error-tokens match its diagnostics. The
  same trick (a sentinel node carrying a code + span) will carry the parser's syntax errors.
- **Overflow / invalid-float deferred (AG-L6).** The structural lexer errors have
  deterministic spans; the value-overflow sub-cases (int/hex literal exceeding i64) and the
  essentially-unreachable invalid-float (L002) would require reproducing Rust's exact
  `parse`/`from_str_radix` overflow boundary, so they are deferred — the SIGIL accumulators
  wrap rather than diagnosing, and such literals never appear in real source.

---

## 8. Constraints & Fallbacks (the hardened constraint set)

The adversarial pass produced one meta-thesis — **correctness = oracle-fidelity ×
comparison-completeness × corpus-coverage** — and turned the open risks into nine
**Existential Threats**, each a strict negative constraint with a dumb physical bound (the
*Boring Limit*) and a non-swallowing *Fail-Fast*. The two under-specified factors the design
had leaned past (what fields are compared; what inputs are covered) are closed by ET-3 and
ET-1.

### Existential threats → strict negative constraints

- **ET-1 — Total corpus coverage.** A coverage-manifest test MUST assert every `TokenKind`
  tag + every lexer branch appears ≥1× in the corpus's reference (`lex_with_id`) output —
  every keyword, every operator/punctuation, each literal form (decimal, hex, float, each
  string escape, bool), line comments, whitespace runs, the empty source, EOF, each error path
  L001–L004. The corpus MUST include the largest stdlib file. "Done" is BLOCKED until coverage
  is total.
- **ET-2 — Full-decode is authoritative.** The Tier-1 token-by-token decoded comparison (tag,
  start, end, value) is THE verdict. The Tier-2 checksum MAY ONLY be a fast pre-filter; never
  the sole gate, and a checksum match is not equality without the decode confirming it.
- **ET-3 — Value equality, not span-proxy.** The comparison MUST check the decoded VALUE of
  every value-carrying kind — `IntLit` (incl. hex), `StrLit` (escapes applied), `BoolLit`.
  Span-only is forbidden EXCEPT the deferred `FloatLit` value (AG-L3).
- **ET-4 — Span tiling (oracle-independent).** A property test MUST assert the stream
  PARTITIONS the source: spans non-overlapping, gap-free over non-skipped bytes, `Eof.start ==
  src.len()`. Runs independently of the oracle.
- **ET-5 — Monotone progress + EOF-safe lookahead.** Every scan iteration MUST advance ≥1 byte
  (incl. the unknown-byte path); all multi-byte lookahead MUST guard `i+k < len` before
  `byte_at` — never trap at EOF. A zero-advance iteration is a rejected ICE.
- **ET-6 — Bounded, host-validated encoding; fail-fast.** The encoding MUST be size-bounded;
  the host decoder MUST validate `count`+`byte_len` against actual wasm memory size BEFORE
  decode; a source whose buffer exceeds the packable bound MUST fail-fast with a distinct
  sentinel — NEVER a wrapped/truncated/stale pointer.
- **ET-7 — No trap on oracle-accepted input.** The lexer MUST NOT trap (`substr`/`byte_at` OOB
  or mid-codepoint) on any byte sequence the Rust lexer accepts; spans are valid byte
  boundaries; non-ASCII in strings/comments matched byte-for-byte.
- **ET-8 — Deterministic purity.** `lex` MUST be a pure deterministic function of src bytes —
  identical `Vec<Token>` + identical encoding every run; no token value encodes a heap address.
- **ET-9 — Tag table total, injective, drift-locked.** The `KW_*`/`OP_*`/kind tag table MUST be
  total (every Rust `TokenKind` mapped) + injective, and a host test MUST assert it against the
  Rust `TokenKind` enum so ANY Rust-lexer change BREAKS the test until the SIGIL lexer + tags +
  corpus re-sync.

### Constraint Matrix (a Boring Limit + a Fail-Fast per ET)

| ET | Boring Limit (exact bound) | Fail-Fast (reject, never swallow) |
|----|----------------------------|-----------------------------------|
| ET-1 Coverage | Manifest = 100% of the N-tag set (N = `TokenKind` variant count) + 4/4 error codes L001–L004. | `corpus_coverage` test enumerates tags hit in the reference output; any uncovered tag → FAIL listing the misses; "done" blocked. |
| ET-2 Decode authority | Equality decided by exactly one fn — the decoded token-by-token compare; the checksum carries 0 authority. | Checksum-vs-decode disagreement → FAIL at the first divergent index; the decode always runs on the corpus, so a checksum-only pass is unreachable. |
| ET-3 Value equality | Compared tuple is exactly `(tag, start, end, value)`; `value` = i64 (Int/Bool) or decoded byte-span (Str). `FloatLit` value is the only elidable field. | A value mismatch on any non-Float kind → decode compare FAILS at that index (expected vs actual). |
| ET-4 Tiling | `t[k].start ==` previous non-skipped `end` (no gap/overlap); `Eof.start == Eof.end == src.len()`. | Oracle-independent `assert_tiling` panics on the first gap/overlap/bad-Eof, reporting offsets; every fixture. |
| ET-5 Progress | Each iteration advances `i` by ≥1; total iterations ≤ `src.len()`; lookahead reads `byte_at(j)` only for `j < len`. | Zero-advance (or iterations > len) → `LEX_NO_PROGRESS` sentinel / trap, never a hang; fuel is the runtime backstop. |
| ET-6 Encoding | `count ≤ COUNT_MAX = 2^24` (16.7M tokens; buffer ≤ ~400 MB, `byte_len < 2^32`). | `count > COUNT_MAX` → return `0 - LEX_TOO_LARGE`, never a wrapped pointer; host asserts `byte_len == 8 + 24·count` AND `ptr+byte_len ≤ memory.size()` before reading, else hard error. |
| ET-7 No-trap | Every `substr(a,b)`/`byte_at(i)` satisfies `0≤a≤b≤len`, `0≤i<len` by construction. | Fuzz test feeds adversarial bytes (truncated UTF-8, lone high bytes, NUL, unterminated string); asserts `lex` returns (stream or error token), never traps — a trap fails it. |
| ET-8 Purity | `lex` reads only `src`'s bytes (no clock/heap-addr/random); encoding is a pure fn of the stream. | Determinism test runs `lex` twice (+ across two compiles); asserts byte-identical encodings; any diff fails (SHADOW/snapshot infra). |
| ET-9 Tag table | Exactly one tag per Rust `TokenKind` variant (count == variant count); fixed enumeration, no duplicates. | The `TokenKind → tag` map is a `match` with no `_` arm — a new Rust variant fails to compile; a host test asserts no-dup + SIGIL `KW_*`/`OP_*` consts == the map. |

### Design notes that survived the pass

- **The `.0` meta-hazard.** The SIGIL lexer must itself correctly lex `1.0` (float) vs `x.0`
  (which the Rust lexer tokenizes as `x` `.` `0`-as-float — the very ambiguity that blocked
  SIGIL tuple `.0`). It reproduces the Rust lexer's exact rule, whatever it is — not trying to
  be "right," only **identical**.
- **Fuel (measured).** `byte_at`/`len`/`substr` are inlined intrinsics (no fuel site), so the
  per-byte scan costs only one back-edge decrement per iteration; the dominant term is
  keyword-matching calls (`bytes_eq`→`starts_with`→`len`). The `recommended_budget` (`128 + 8×WCC`
  since SH-FUEL F2; the lexer's while-loops are unbounded to the static model, so its budget is
  still the un-multiplied floor) is far too small — so the differential harness **passes an
  explicit generous budget set from a one-shot `lex string.sigil` measurement**, not a guess
  (ET-5/ET-6 context), and §5's first-byte/length dispatch is the fuel control.
- **`str ==` (R1 resolution).** Pointer-equality (not bytes) at the time; `bytes_eq` was the
  steer, documented in `docs/specs/strings.md`; **no lint** (`literal == literal` is
  legitimate, a targeted lint needs provenance the compiler lacks); **AG-S1-M** (make `==`
  byte-compare) retires the footgun entirely (AG-6). *Since shipped: PR #699 made `==`
  byte-compare, closing AG-S1-M/AG-6.*

---

## 9. Anti-Goals (v1 does NOT do)

- **AG-1 — the parser / anything past tokens.** This stage is the lexer only.
- **AG-2 — replacing the Rust lexer in the pipeline.** The SIGIL lexer is a tested artifact
  run alongside the Rust one; wiring it in is a later bootstrap stage.
- **AG-3 — the streaming iterator form.** `next(self @Mut) -> Option<Token>` is a post-v1
  wrapper over the batch scan.
- **AG-4 — block comments / lexer features the Rust lexer lacks.** Identical means identical:
  no `/* */`, no extras — only what `lex_with_id` does.
- **AG-5 — full `FloatLit` value fidelity (v1).** Pending `parse_f64` (R2); KIND + span match
  in v1.
- ~~**AG-6 — fixing `str ==` to byte-compare.** Tracked as the AG-S1-M follow-on; v1 uses the
  `bytes_eq` helper rather than the compiler change.~~ **✅ SHIPPED (PR #699)** — `str ==` now
  byte-compares; the lexer keeps `bytes_eq` (behaviorally identical).

**Adversarial-pass additions** (the academic edge-cases the ETs deliberately do NOT engineer
fallbacks for):

- **AG-L1 — Non-ASCII identifiers.** The Rust lexer's idents are ASCII
  (`[A-Za-z_][A-Za-z0-9_]*`); the SIGIL lexer matches that exactly. A non-ASCII byte appears
  only inside string literals / comments (passed through) or terminates an identifier / is an
  unexpected char — whatever the Rust lexer does. v1 does NOT design or guarantee a non-ASCII
  identifier extension.
- **AG-L2 — "O(1)" keyword dispatch.** The first-byte+length bucketing is O(bucket-size), not
  literally O(1); a (first-byte, length) cell may hold several keywords. v1 does NOT engineer a
  perfect hash or minimal-collision scheme; bucketing the common case to a handful of
  `bytes_eq` calls is sufficient.
- **AG-L4 — Diagnostic message-text fidelity.** v1 matches lexer-error PRESENCE + POSITION +
  coarse kind (L001–L004), NOT the exact diagnostic message strings (human prose). (Supersedes
  the looser R8 note.)
- **AG-L5 — Sources beyond the encoding ceiling.** A source whose encoded token buffer would
  exceed the packable size bound (ET-6, `COUNT_MAX = 2^24`) is UNSUPPORTED; the encoder
  fail-fasts rather than chunking or streaming. Real compiler sources are far under the bound.
- **AG-L6 — value-overflow lexer errors (PR-3b).** The SIGIL lexer matches the structural,
  deterministic-span lexer errors (L001 hex-without-digits, L003 unterminated string, L004
  unexpected char). It does NOT match the value-overflow sub-cases — an int/hex literal
  exceeding i64 (Rust's `parse`/`from_str_radix` `Err`) or the essentially-unreachable invalid
  `FloatLit` (L002) — which would require reproducing Rust's exact overflow boundary; the SIGIL
  accumulators wrap instead, and such literals do not occur in real source.

*(AG-L3 — `FloatLit` value fidelity — is already AG-5 above.)*

---

## 10. The Arc Beyond

1. **`str.parse_f64`** — closes R2/AG-5 for full float-value fidelity.
2. ~~**Fix `str ==` to byte-compare (AG-S1-M)** — retires the `bytes_eq` workaround and unblocks
   `Map<str, V>` with view/constructed keys (a `match`/`Map`-based keyword table).~~
   **✅ SHIPPED (PR #699)** — `==`/`!=`/`match` byte-compare, fuel-metered; `@SecretCT`
   operands rejected (T033).
3. **Streaming `Lexer { src, pos }` with `next(self @Mut) -> Option<Token>`** — wraps the batch
   scan; `for tok in lexer` over the new iteration protocol.
4. ~~**The parser** (Tier 3 arena/`NodeId` AST) — the next self-hosting stage, consuming this
   `Vec<Token>`.~~ **✅ SHIPPED (#242–#254)** — `selfhost/parser.sigil` parses the whole stdlib
   node-for-node against the `parse_with_id` oracle; see `docs/specs/parser-in-sigil.md`.
5. **Wire the SIGIL lexer into the pipeline** — the Stage-0 → Stage-1 bootstrap.

---

## Cross-references

- `crates/sigil-compiler/src/lexer.rs` — the differential ORACLE (the exact token model).
- `crates/sigil-runtime/tests/lexer_spike.rs` (on main) — the L0 gates (`Vec<Token>`
  round-trip; keyword-on-a-view → the `bytes_eq` rationale + the `bytes_eq` gates).
- `docs/specs/strings.md` — `byte_at`/`len`/`substr`/`starts_with` (the scan primitives) + the
  AG-S1-M `str ==` history (closed by PR #699).
- `docs/specs/tuples.md` — `(value, pos)` multi-return helpers; the shared `.0` lexing hazard.
- `docs/specs/iteration.md` — the streaming `next()` form (the Arc-Beyond shape).
- `docs/specs/self-hosting-completion-ladder.md` — the current bootstrap authority.
