# Attack Test Suite — Known Gaps

## Attack 06: Escalation via Restriction Aliasing

**Status:** Phase 2A.6 M1 shipped (authority parsing + restriction masks). M2 (Z3 bitvector constraints) pending Z3 availability.

**Vector:** Pass a `.restrict()`-attenuated capability to a function expecting the unrestricted base type.

**Phase 2A.6 fix (in progress):** Z3 bitvector authority tracking. Each cap VarId gets a BV<32> representing its authority mask. `.restrict(query)` narrows the mask via AND. At every sink (Call, Spawn, SerializeMessage, Return), Z3 asserts `(auth AND full) == full`. UNSAT → C003 error with counterexample.

**M1 shipped:** Cap types declare authorities (`cap type Fuel { consume, split, query }`). Restriction parsed as compile-time identifier, resolved to bitmask. AIR carries `restriction_mask: u32`.

**M2 remaining:** Z3 constraints in `z3_capability.rs` (feature-gated behind `solver`). Requires Z3 headers on disk.

---

## Attack 06b: Escalation via Aggregate Smuggling — CLOSED in step 25

**Status:** Closed at the type-check pass via T183 (step 25 of the
supremum loop, axis 2). The Z3 Phase 2B SMT memory model is no longer
needed to defend against the source-level smuggling vector — caps are
forbidden from appearing in record fields, full stop.

**Original vector:**
```sigil
let restricted = fuel.restrict(query);
let wrapper = MyRecord { cap: restricted };
let extracted = wrapper.cap;
needs_full_fuel(extracted);  // Z3 sees LoadField → defaults to full_mask
```

**Why it escaped (pre-step-25):** The Z3 blanket source rule assigns
`full_mask` to any cap variable that isn't the destination of
CapRestrict, CapSplit, or Assign(Var). `LoadField` falls into the
"all other" bucket, so capabilities loaded from records got full
authority regardless of what was stored. This earlier doc claimed the
parser rejected cap-typed record fields, but that defense was an
illusion — the parser only rejected the literal field name `cap` (a
reserved keyword); a field named `f: Fuel` (or any other non-keyword
name) compiled cleanly. The smuggling vector was live for any user
who didn't happen to name their field `cap`.

**Step 25 fix:** `validate_records_no_cap_fields` in `type_check.rs`
walks every record definition and emits T183 if any field's type
contains a cap (directly, or via a generic instantiation / array
element). Fixture: `crates/sigil-compiler/tests/fixtures/T183.sigil`.
Message-content test: `diagnostic_messages.rs::t183_message_names_record_and_field_and_type`.

**Step 27 companion fix (T184):** the enum-variant payload channel
is the parallel smuggling vector. An enum like
`enum CapBox { Wrapped(Fuel), Empty }` allows wrapping a restricted
cap, then pattern-matching it out — the destructure binding is a
fresh source that Z3's authority tracker treats as full_mask,
losing the restriction provenance. `validate_enums_no_cap_payloads`
in `type_check.rs` walks every enum and emits T184 if any variant
payload contains a cap. Fixture:
`crates/sigil-compiler/tests/fixtures/T184.sigil`. Message-content
test: `diagnostic_messages.rs::t184_message_names_enum_variant_and_payload_type`.
The T184 message cross-references T183 so a user who hits one rule
can see the related one.

**Future work — Phase 2B SMT memory model:** still useful if Sigil
ever wants to allow caps in records or enum payloads (e.g., for
actor-internal record-of-caps state). The model would let LoadField
and EnumExtract track per-field/per-variant authority precisely
instead of defaulting to full_mask, unblocking the expressiveness
gain without re-opening the smuggling gap. Not required for today's
safety story.

---

## Attack 06c: Escalation via Slot Aliasing — CLOSED (C013)

**Status:** Closed by the structural, solver-independent slot escape gate
(`crates/sigil-compiler/src/slot_escape.rs`, C013). Residual risk row
SR-020 in `docs/RESIDUAL_RISKS.md`; claim 51 in `docs/CLAIMS.md`.

**Vector:** `Slot<Cap>` is non-linear and aliasable. Put a `.restrict()`ed
cap into a slot through an ALIAS — a callee's `Slot<Fuel>` parameter, the
same actor-state slot in another handler, or `let s2 = s` — then take
through the original variable and pass the taken cap to a function that
requires full authority:

```sigil
fn fill(s: Slot<Fuel>, c: Fuel) -> i64 {
    let n = c.restrict(burn);
    slot_put(s, n);            // invisible to the caller's take
    return 0;
}
// caller: fill(s, full1); let taken = slot_take(s); use_full(taken);
//         slot_put(s, full2);   // makes the caller's own meet {full}
```

**Why it escaped:** both authority checkers key a slot's contents on the
TAKING function's own AIR variable. The Z3 rule meets only the `slot_put`s
made through the take's own variable inside the same function (`BV 0` when
there are none), and the linked Lean verifier binds a slot parameter or
state slot to an occupied cell at the type's full ceiling. A put through
an alias is outside both, so when the taker also puts a full cap through
its own name, the meet is {full} and the sink accepts the restricted cap.
The runtime has no facet semantics (restrict is an identity alias), so
nothing backstopped it. Without the taker's own full put the Z3 meet is
empty and fails closed (C003) — that sibling was over-rejected, not
laundered.

**Fix:** reject the PUT. A possibly-restricted cap (a `.restrict`ed value,
a `slot_take` result, or anything without a full-authority origin) may
only be put into a slot created by `slot_new` in the same function and
used nowhere else but `slot_put`/`slot_take` there. Every aliasable slot
therefore holds only full puts, which is exactly what makes "checked at
the ceiling" and "meet of my own puts, else 0" sound — the Z3 constraint
shape and the Lean cell binding stay as they are. The documented
cross-handler pattern (a handler putting its own full payload parameter
into a state slot, `z3_corpus/18_inter_actor_3_of_3.sigil`) is unaffected.
Sound alternative for authors: put the full cap, restrict after the take.

Tests: `crates/sigil-compiler/tests/slot_alias_escape.rs` (default lane,
exact code sets, SC-P4 anti-stub) and `slot_alias_meet.rs` (solver lane:
the prover alone is pinned as still accepting the aliased put; the
pipeline rejects it). Fixture: `crates/sigil-compiler/tests/fixtures/C013.sigil`.

## Attack 06d: Escalation via an Init-Narrowed State Capability — CLOSED (C014)

**Status:** Closed by the state-cap origin gate in the same module
(`crates/sigil-compiler/src/slot_escape.rs`, C014). Residual risk row
SR-021 in `docs/RESIDUAL_RISKS.md`; claim 52 in `docs/CLAIMS.md`.

**Vector:** every authority checker classifies a capability read from a
cap-typed actor-state field as FULL — the slot escape gate's state-read
origin (06c), the Z3 prover's full mask for a state-read cap variable, and
the Lean verifier's cell binding — but nothing checked what `init` stored
there. Narrow the capability in `init`, then sink a `draw` off the field:

```sigil
actor Vault {
    state { hold: Slot<Fuel>, fuel: Fuel }
    init(h: Slot<Fuel>, f: Fuel) { fuel = f.restrict(burn); }   // stored narrow
    on Use() -> i64 { return use_full(fuel.draw(10)); }        // read as full
    on Fill() -> i64 { slot_put(hold, fuel.draw(10)); return 1; } // 06c silent
    on Drain() -> i64 { let t: Fuel = slot_take(hold); return use_full(t); }
}
```

Both the direct form and the state-slot relay compiled on `main` (pinned
ae026aec) and on the C013 branch before this gate.

**Why it escaped:** the type checker makes a non-`mut` state field writable
only in `init` (T123) and forbids a `mut` cap field (C011), so "state caps
are frozen after `init`" was true — but frozen at whatever authority `init`
chose. `init`'s PARAMETERS are spawn sinks and therefore full; the VALUE
stored may be a `.restrict` result, a `slot_take` result, a closure or FFI
result. C013 then trusted the state read as full and waved the narrow
`draw` through into the state slot.

**Fix:** reject the STORE. Every `AirStmt::StateWrite` whose value is a
capability must have an origin the C013 classifier accepts — a bare `init`
parameter, `mint`, a state read or a direct call result, through
`let`/`draw`/`split` — in `init` and in every handler alike (the gate does
not rely on T123/C011 running first). Storing the bare parameter or a `draw`
off it compiles; the empty-`init` positional population
(`init(f: Fuel) {}`, runtime-written from the spawn arguments) carries no
store and is unaffected. Sound alternative for authors: store the
parameter, restrict the value read from the field at the point of use.

Tests: `crates/sigil-compiler/tests/state_cap_origin.rs` (exact code sets,
SC-P4 planted-restrict anti-stub, no lane `cfg`: its solver-lane run is
CI's) and `slot_escape::tests` (AIR-level, including the handler store).
Fixture: `crates/sigil-compiler/tests/fixtures/C014.sigil`.

---

## CT008: Variable shift by a `@SecretCT` amount — CLOSED by T034 (2026-09-30)

**Status:** Closed at the taint pass via `T034` (branch `p2/ct008`,
2026-09-30; author decision 2026-09-30 to fix before the paper
submission rather than narrow the paper's claim). The gap was measured
2026-09-20 against main `ae026aec` with `sigil check --json` and
recorded here open. The rule lives beside CT007's `T026` arm in
`taint_check.rs` (`compute_expr_taint`, `Binary`): a `<<` / `>>` whose
AMOUNT (right operand) carries `@SecretCT` is rejected; the shifted
VALUE is exempt because a shift by a `@Public` count has a count-only
latency and is how constant-time code masks and rotates a secret. The
check is on the label, so `let`-copied and arithmetic-derived amounts
and the compound `<<=` / `>>=` forms (same `Binary` node) are covered.
The value-side exemption is a machine-width (`i32`/`u32`/`i64`/`u64`)
statement. The taint pass runs before the formal gate, so a `u256`
`@SecretCT` AMOUNT is `{T034}` like any other width; a `u256`
`@SecretCT` VALUE shifted by a `@Public` amount passes this rule and is
then refused by the formal gate as `I013` on the `u256_shl`/`u256_shr`
lowering. Measured 2026-09-30 with `sigil check --json`: secret value +
public amount `{I013}` on `ae026aec` and on this branch; public value +
secret amount `{I013}` on `ae026aec`, `{T034}` on this branch. No
`u256` shift touching `@SecretCT` compiles.
Owner: the constant-time spec (`docs/specs/secret-ct.md` §3, row
CT008). Review point: any change to that `Binary` arm, to the parser's
`compound_assign_op`, or a new shift-shaped operator (a rotate
intrinsic would need the same amount rule).

**Pinned by** (all exact code sets, `crates/sigil-compiler/tests/taint_constant_time.rs`):
`ct008_shl_by_secret_ct_amount_rejected`,
`ct008_shr_by_secret_ct_amount_rejected`,
`ct008_shift_by_secret_ct_amount_rejected_for_i32_and_u64`,
`ct008_shift_with_both_operands_secret_ct_rejected`,
`ct008_let_copied_secret_ct_amount_rejected`,
`ct008_arithmetic_derived_secret_ct_amount_rejected`,
`ct008_compound_shift_assign_by_secret_ct_amount_rejected` (all `{T034}`;
the compound test shifts a `@Public` value so it pins the AMOUNT operand
specifically — the write-back of the `@SecretCT` result is a flow-sensitive
rebind of the local, not a `T001` sink);
`ct008_secret_ct_value_shifted_by_public_amount_accepted`,
`ct008_public_shift_accepted`,
`ct008_secret_non_ct_amount_is_not_a_ct_violation` (accepted controls);
`ct008_anti_stub_planted_secret_ct_amount_in_the_accepted_shape_is_detected`
(SC-P4); `t034_message_and_hint_name_the_amount_and_the_sound_alternative`;
plus the dedicated fixture `fixtures/T034.sigil` (parity manifest row,
`registry_wired`). Measured on this branch's CLI vs `ae026aec`: the
shift-by-secret probes move `ok → {T034}`; the `/` control stays
`{T026}`; the value-side and public controls stay accepted.

**Original vector:** `docs/specs/secret-ct.md` reserved CT008 as "no current
source operator". That reason is false: `<<` and `>>` parse
(`parser.rs`, `Shl`/`Shr`) and type-check on `i32`/`u32`/`i64`/`u64`.
Neither the taint pass (which checks only `/`, `T026`) nor the formal
gate (whose policy classes have no shift class) rejects a `@SecretCT`
shift AMOUNT, so this compiles clean with an empty diagnostic set:

```sigil
#[ring(outer)] module ext;
fn f(a: i64, n: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return a << n;
}
```

The same holds for `>>`, for `u64` and `i32`, and for both operands
`@SecretCT`. Controls: the same shape with `/` in place of `<<` is
rejected with exactly `{T026}`, and a `@SecretCT` VALUE shifted by a
`@Public` amount compiles (that one is fine: the amount, not the
value, is what a barrel-shifter-less core leaks).

**Why it matters:** a data-dependent shift count is variable-time on
cores without a barrel shifter (and on some microcoded paths), which
is exactly the class the `@SecretCT` sublattice claims to reject
("variable-time operations on secret-tainted operands"). Wasm engines
compile `i64.shl` to a native shift, so on mainstream x86-64/AArch64
hosts the leak is theoretical; the claim, not the deployment, is what
is wrong.

**While open, deliberately not pinned as an acceptance test:** a
passing test that compiled this program would have read as an
endorsement. The shift rule landed as `T034` with the exact-set
rejection tests listed under "Pinned by" above, and this entry closed.
The selfhost shadow (`selfhost/taint_check.sigil`) has no shift rule:
`T034` is oracle-only, like `T033`, and the SH-TAINT differential
filters both sides to its 13-code core set, so the shadow lags the
oracle on this rule rather than disagreeing with it.

---

## Effect-check ring routing — a generic was checked under the FIRST module's ring — CLOSED by the governing meet (2026-09-30)

**Status:** Closed. Monomorphized instances (and closures lifted while one is
re-checked) are effect- and ring-checked under the MEET of the defining module
and every module whose scope resolved names in the re-checked body
(`TypedProgram::governing_context`, BUG-5b; claim 50 in `docs/CLAIMS.md`,
SR-019 in `docs/RESIDUAL_RISKS.md`, pinned by `effect_ring_routing.rs`). The
fix landed in the same integration as this entry's measurements, so the
behavior below was never on `main` without its fix. CHECKING follows the
governing meet; EMISSION still follows the filing module (`modules[0]`), and
the two-ring placement gate refuses every lowered call between an instance and
a caller in different rings with exactly R007 (SR-018). So a layout the meet
accepts but whose instance is filed in the other ring than its caller is
refused, fail-closed, until instances are emitted into their governing ring
(issue #768; the author chose on
2026-10-01 to land the meet with these refusals). `effect_ring_routing.rs` pins
each such layout at two layers: the checker layer accepts it, the pipeline is
exactly {R007}. **Owner:** effect/ring gate
owners. **Review point:** any change to monomorph module filing in
`crates/sigil-compiler/src/type_check/mod.rs` (the `else { 0 }` owner arm) or to
the instance homes recorded at instantiation. Everything below is the
measurement against `main` at `ae026aec`, kept as history; the
`effect_ring_scope.rs` pins it cites were flipped when the fix landed: each
escape to its twin's code, each mirror to exactly {R007}.

**Vector:** monomorphized generic instances are filed under `modules[0]`
regardless of their defining module, and both `effect_check` and `ring_check`
key on the filing module's ring. Measured against the compiler built from
`main` at `ae026aec`, with the program's first module carrying the ring
opposite to the generic's own:

- An inner-ring generic function whose body calls an `extern` COMPILES CLEAN
  when the first module is outer-ring. The measured diagnostic set for that
  program is exactly EMPTY — not "R003 is replaced by something else", not
  "another gate catches it later": nothing rejects it. Its byte-identical
  non-generic twin is exactly {R003}. R004 does not apply (there is no
  cross-ring call — the `extern` is declared in the inner module itself), E003
  does not apply (the generic names no privilege effect in its row), and the
  taint gates are silent once the result is bound `@Internal`. This escape
  matters most for the effect story: R003 is one of the two host-boundary fences
  the inner-ring effect-check exemption rests on. It is not the only ring-code
  escape — R001 and R002 escape in the opposite module order (see "Ring codes"
  below) — and `docs/SOUNDNESS_MATRIX.md` SND-RING-001 recorded the R001,
  R002 and R003 clauses as proven for non-generic code only until the meet landed.
- An inner-ring generic function with an undeclared effect DOES produce E001,
  and one containing `handle Unsafe` DOES produce E002, where the non-generic
  twins compile clean. Fail-closed, but the scope sentences in the diagnostic
  docs would otherwise read as promising the opposite. Do not read every
  inner-ring E001 as this gap: a second, ring-blind emitter in the type checker
  (`bind_and_check_effect_rows`) raises E001 for row contravariance on a generic
  callee's `Fn`-typed formal regardless of ring or module order, pinned in
  `crates/sigil-compiler/tests/effect_ring_scope.rs`. E002 has no such twin.
- With an inner-ring first module the mirror holds: an outer-ring generic
  function or generic impl method escapes the effect check entirely.

**Ring codes — every code `ring_check.rs` emits escapes.** The same filing
reaches R001, R002 and R003, because `ring_check` keys all three on the filing
module's ring. Each measured against its byte-identical non-generic twin, in both
first-module orders, against `main` at `ae026aec`, and pinned as exact code
sets in
`crates/sigil-compiler/tests/effect_ring_scope.rs` (section "Ring codes under monomorph routing": written as
EXPECTED TO FLIP against `ae026aec` and flipped in the landing that merged
`p2b/routing`, so each ESCAPES bullet below now pins the twin's code, and each
mirror — accepted by the meet, as its twin — pins exactly {R007}, because its
instance is still filed in the other ring than its caller (#768)):

- R001 ESCAPES — inner-ring first module, outer-ring generic owning a cap as a
  parameter, as its return type, or `let`-bound (free fn or generic impl method):
  exactly EMPTY; twin exactly {R001}.
- R002 ESCAPES — inner-ring first module, outer-ring generic returning a
  cap-reference-bearing closure type (`-> Fn(i64) -> &Tool`): exactly EMPTY;
  twin exactly {R002}. (A bare `-> &Tool` does not reach R002: T253 pre-empts it
  in both twins.)
- R003 ESCAPES — outer-ring first module, inner-ring generic calling an `extern`
  (free fn or generic impl method): exactly EMPTY; twin exactly {R003}. This is
  the direction described in the first bullet above.
- Each mirror is fail-CLOSED: after an inner-ring first module an outer-ring
  `#[trusted]` generic calling an `extern` is exactly {R003}; after an outer-ring
  first module an inner-ring generic owning a cap is exactly {R001} and one
  returning a cap-reference closure type is exactly {R002}. Every twin is clean.
- NOT affected: R004 (raised by the type checker against the DEFINING module's
  ring, both call directions) and R006 (a module attribute) are identical for a
  generic and its twin in both orders. R005 is never emitted; R010–R013 are
  AIR-level invariants with no ring key. An uninstantiated generic has no typed
  instance, so it has nothing to check or emit.

So `docs/SOUNDNESS_MATRIX.md` SND-RING-001 recorded the R001, R002 and R003
clauses as proven for non-generic code only; with the meet it records them for
generic code too (its "GENERIC CODE, HISTORY AND PINS" paragraph).

**Why it was filed here and not in `docs/RESIDUAL_RISKS.md`:** that register's
completion gate admits only `Closed` and `Accepted` rows, and an `Accepted` row
must carry a real tracking-issue reference. When measured, this gap had neither a
fix in this tree nor an issue number, and inventing one would have been worse than
filing it here with an owner and a review point. The fix now carries SR-019.

---

## E003 covers free functions only, and only a DECLARED row

**Status:** Open, two limits, both confirmed by repro against `main` at
`ae026aec`. **Owner:** effect/ring gate owners (`type_check/validators.rs`,
`validate_inner_ring_no_effects`). **Review point:** before E003 is cited as a
host-boundary fence anywhere, or on any change to the inner-ring privilege-row
validator. Not fixed here.

**Vector 1 — impl methods are outside the walk.** `validate_inner_ring_no_effects`
iterates `module.items` and matches `Item::FnDef` only
(`crates/sigil-compiler/src/type_check/validators.rs`, the walker around line
395). An inner-ring impl method may therefore declare `! { Unsafe }` and even
contain a `handle Unsafe` block: the program compiles clean, exit 0, empty
diagnostic set, while the free-function twin is exactly {E003}. Reaching the
host from there is still fenced by R003 (an extern call from such a method is
rejected), so this is a hole in the row-hygiene rule, not a demonstrated host
escape.

**Vector 2 — a row-less function needs no row.** E003 rejects the privilege
effect NAMED in a declared row. An inner-ring function that declares no row at
all may still write `handle Unsafe { ... }`, which the effect checker skips in
the inner ring, so E002 does not fire either. Pinned as a clean compile by
`inner_ring_handle_unsafe_is_exempt_outer_fires_e002` in
`crates/sigil-compiler/tests/effect_ring_scope.rs`.

Consequence for the docs: E003 must not be listed as one of the fences that
make the inner-ring effect-check exemption safe. R003 and R004 are the fences
that carry that weight.

---

## Generic functions resolve by bare name across modules — OPEN

**Status:** Open (attack surface). Found 2026-09-28 while fixing the two-ring
call-index defect (P2B-TWORING round 2, diagnostic R007); pre-existing, not
introduced by that fix, and not closed by the BUG-5b routing work (the governing
meet bounds what the instance may do, not whether the call is visible). Pinned as
it stands by `known_gap_generic_free_fn_call_bypasses_use_and_r004` in
`crates/sigil-compiler/tests/effect_ring_routing.rs`, which is written to FAIL
when the gap is closed. Owner: `sigil-compiler` type checker (call resolution).
Review point: before any claim about module privacy or ring isolation in a
multi-module compilation unit, and with the SR-019 follow-up (re-checking free-fn
instances in the definer's scope), which touches the same resolution path.

**Vector (measured on single-file multi-module sources with the round-2
CLI):** a generic function is callable by its BARE name from any module of
the compilation unit, even when it is private and even across the ring
boundary. The same call to a non-generic function is rejected (`undefined
function`), and the qualified spelling of the generic (`first::ident`) is
rejected too, so only the bare-name generic path leaks:

```sigil
#[ring(outer)]
module a;
fn dummy() -> i64 { return 0; }
module b;                                  // inner ring
fn ident<T>(x: T) -> T { return x; }       // PRIVATE to b
#[ring(outer)]
module c;
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return 0 - ident(42); }
```

compiles clean (`sigil check --json` reports `"status": "ok"` and a module is
emitted): outer `c` directly calls private inner `b::ident` with no
privacy diagnostic and no cross-ring (R004) diagnostic. The single-ring
variant (private generic in one module, bare call from another) compiles
too, bypassing module privacy.

**What R007 covers:** when the monomorphized instance lands in a ring other
than its caller's (it is filed under the FIRST module), the lowered call
crosses the ring boundary and R007 rejects it at emission. Above, the first
module `a` is outer like the caller, so the instance and the call are both
outer and nothing fires. With the governing meet in place this is unchanged:
no CHECKER rejects a bare-name generic call, so a source-level cross-ring call
is refused (R007) exactly when its instance is filed in the other ring than its
caller, and compiles otherwise. Pinned both ways in
`known_gap_generic_free_fn_call_bypasses_use_and_r004`: an inner module calling
an outer generic, outer definer first, passes the checker layer and is exactly
{R007} end to end (with or without `use`); the same call with the inner caller
first compiles. R007 is a by-product of filing there, not a fence for this gap,
and it would stop firing for the first layout once #768 emits instances into
their governing ring. The module-privacy and `use` bypass is open in every
layout.

**Fix direction:** resolve generic callees through the same module-scoped
path as non-generic ones, so privacy and R004 apply at the source call
site. It needs its own change and fixture corpus.

**Vector, restated with the governing meet in place:** a generic free fn is resolved by BARE NAME from a program-wide table
(`universe.generic_fns`, `type_check/expressions/calls.rs`), independently of the calling
module's `use` scope and of the R004 cross-ring rule. An inner-ring module can therefore call an
outer-ring module's generic directly, with no `use` and no `grant`, where the byte-identical
non-generic twin is exactly T062 (no `use`) or exactly R004 (with `use`). Pinned as it stands by
`known_gap_generic_free_fn_call_bypasses_use_and_r004` in
`crates/sigil-compiler/tests/effect_ring_routing.rs`, which is written to FAIL when the gap is
closed.

**What bounds it today:** the instance such a call creates is governed by the MEET of its
definer and the caller's scope (`TypedProgram::governing_context`, SR-019): it is effect-walked
unless every governing module is inner-ring, holds `handle Unsafe` authority only if every one is
trusted, and gets BOTH rings' rules when it straddles them — so an inner caller routing an
`extern` through an outer generic is exactly R003
(`outer_generic_resolving_an_inner_callers_extern_is_r003`). What is NOT bounded is visibility:
the call itself passes every checker (R007 refuses it at emission only when the instance is
filed in the other ring than the caller, see above), and a private-by-convention generic is
callable program-wide.

**Fix direction (a language decision, deliberately not taken in BUG-5b):** resolve generic free
fns through the same `use`-scope and ring filter as non-generic ones (`call_resolve.rs`). It
rejects programs that compile today — any cross-module generic call without `use`, and every
cross-ring one — so it needs a corpus measurement first. Owner: `sigil-compiler/type_check`.
Review point: with the SR-019 follow-up (re-checking free-fn instances in the definer's scope),
which touches the same resolution path.
