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
- NOT affected: R004 (raised by the type checker, both call directions) and R006
  (a module attribute) are identical for a generic and its twin in both orders,
  where each generic is defined and called in one module. R004 is judged against
  the ring of the module being checked, and a generic free fn's body is
  re-checked while the module being checked builds its instance: the module
  whose own code reaches the instantiation, directly or through other generic
  bodies. So with the definer and that module in different rings, R004 follows
  the instantiating module, and an outer-ring generic's call into the inner ring
  escapes R004 when an inner-ring module instantiates it (its twin is exactly
  {R004}; the instance is emitted, if at all, in the inner ring). That split is
  reachable only through the bare-name gap below ("Generic functions resolve by
  bare name across modules"); a generic method is never split, since a method
  call resolves only within the caller's ring. Pinned by
  `r004_in_a_generic_body_is_judged_against_the_instantiating_module` in
  `crates/sigil-compiler/tests/effect_ring_routing.rs`. R005 is never emitted;
  R010–R013 are AIR-level invariants with no ring key. An uninstantiated generic
  has no typed instance, so it has nothing to check or emit.

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
when the gap is closed. The cross-ring layouts of
`r004_in_a_generic_body_is_judged_against_the_instantiating_module` (same file)
reach their generics through this gap too, so that test fails then as well.
Owner: `sigil-compiler` type checker (call resolution).
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
outer-ring module's generic directly, with no `use`, where the byte-identical
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

**Second vector, the other direction (found 2026-10-05 by the independent review of #797;
measured on main `e0f991c2`): a generic body reaches its INSTANTIATOR's private functions.** A
generic free fn's body is re-checked in the context of the module whose call creates the
instance, that module's function sigs, `use` scope and ring (SR-019), and its function sigs
include its PRIVATE functions. So a generic defined in `lib` can call a private function of any
module that instantiates it, by bare name:

```sigil
#[ring(outer)] #[trusted]
module host;
extern "C" fn fs_read(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };
fn raw(p: i32, n: i32) -> i64 ! { FFI, Unsafe } { let r: i64 @Internal = fs_read(p, n); return 0; }
fn secret_helper(y: i64) -> i64 { return y * 2; }
pub fn boot(p: i32, n: i32) -> i64 ! { FFI, Unsafe } { return g(1, p, n); }
pub fn boot2(y: i64) -> i64 { return h(1, y); }
#[ring(outer)]
module lib;
pub fn g<T>(x: T, p: i32, n: i32) -> i64 ! { FFI, Unsafe } { return raw(p, n); }
pub fn h<T>(x: T, y: i64) -> i64 { return secret_helper(y); }
```

compiles clean in both module orders (`sigil check --json` reports `"status": "ok"`): untrusted
`lib`'s generics call `host`'s private FFI wrapper and its private pure function. The
non-generic twins (`lib` with `use sigil::host`, and `host` without its calls, since a `use` in
both directions is a cyclic module dependency) are exactly T062 for the bare calls and exactly
T155 for `host::raw` and `host::secret_helper`. Trust does not matter (an untrusted `host` leaks the
same), and the leak crosses rings: an inner-ring generic reaches an outer-ring module's private
pure function when the outer module sorts first (the instance is filed in its ring); with the
inner definer first the instance is filed in the inner ring and the outer caller's call is R007,
the filing by-product described above. A generic IMPL METHOD does not leak: CF-D9 gives it its
definer's function sigs, and the `use`-scope fallback admits only `pub` names (exactly T062).
Pinned as it stands by `known_gap_generic_body_reaches_the_instantiating_modules_private_fns` in
`crates/sigil-compiler/tests/effect_ring_routing.rs`, written to FAIL when the gap is closed.

**What bounds the second vector today:** everything but visibility. The instance's effect row
(a private FFI wrapper's `{ FFI, Unsafe }` must be declared on the generic, or E001; a private
pure function needs no row, so nothing bounds that form), the governing meet (R003 for an
`extern`, E002 for `handle Unsafe`), E003 for a privilege row on an inner-ring definer, and
capability values, which must be passed. The fix is SR-019's follow-up: re-check a free-fn
instance body in its DEFINER's scope, so a generic body resolves exactly as its non-generic twin.

---

## A negative `i32` index read and wrote past its buffer — CLOSED

**Status:** Closed in `sigil-compiler/air` by `index_for_bounds_check`, which hands every bounds
check its index as a `u32`.

**Vector:** the emitter picks a compare's signedness from its left operand. An 8-byte index was
wrapped to `u32` before its bounds check, but a 4-byte signed one reached the check as an `i32`,
and the signed `i32.ge_s` / `i32.gt_s` let a negative index through. Found on `byte_at`, and
present at every bounds check that took the index as it came:

- `s.byte_at(i)` read the byte `-i` positions before the string. With `"XYZ"` laid out before
  `"hello"`, `byte_at(-1)` on `"hello"` read the `Z`:

  ```sigil
  let x: str = "XYZ";
  let s: str = "hello";
  let i: i32 = 0 - 1;
  return s.byte_at(i) + x.len();
  ```

  This returned 93 (90 plus 3) instead of trapping.
- `a[i]` read, and `a[i] = v` WROTE, before the array.
- `s[i]` read before a slice.
- `&a[lo..hi]` built a slice that began before its array. Both of its checks, `lo > hi` and
  `hi > len`, were signed.

Each ran to completion without a trap. The same programs with an 8-byte index trapped.

**Fix:** `index_for_bounds_check` reinterprets a 4-byte signed index as `u32` (a typed copy, bits
unchanged: the `.as_u32()` lowering) wherever an 8-byte one is wrapped. A negative index is then
at least 2^31 and fails the unsigned check. A `u32` or 8-byte index lowers to the same bytes as
before. The self-hosted compiler makes the same copy in `byte_at` and at an array element
(`selfhost/air.sigil`), and it refuses slice construction and slice indexing.

**Pinned by:**
- `byte_at_traps_out_of_bounds_at_every_index_width` in `crates/sigil-runtime/tests/str_api.rs`;
- `crates/sigil-runtime/tests/signed_index_bounds.rs`: array reads and writes, slice reads and
  slice ranges.

Both run every index width the type checker admits, each with an in-bounds control. An
out-of-bounds program returns 0 unless it traps, so a missed trap reads as `Ok`. Run against the
compiler before the fix, every one of them fails on its negative `i32` index.
`tests/compile/signed_index_bounds.sigil` pins the new lowering's bytes in the parity manifest.

---

## Construct parts typed at their default width — CLOSED, except unannotated mixed-width arrays

**Status:** Closed in `sigil-compiler/type_check` (SR-032) for enum payloads and record fields (of
a generic enum or record too, with or without an annotation that names the instance), tuple
elements, array elements under an array slot, assigned values, returns, the arguments of a
resolved, generic or closure call (a closure inside one included), and a value typed by an
integer literal it is not, at every site that narrows one. One shape stays open, pinned by
`known_gap_mixed_width_array_elements` in `crates/sigil-runtime/tests/construct_slot_width.rs`,
which is written to fail when it closes. It predates SR-032. Owner: `sigil-compiler` type
checker. Review point: any change to integer-literal narrowing (`resolve_int_literals_in_expr`,
`first_unnarrowable_value`, `fit_to_instance_slot`), to array element inference, or to generic
call or construction inference.

**Vector:** a construct lays each part out at the width of the part's own type, while every reader
uses the slot's declared type. An unannotated array literal takes its first element's type, and a
later element built at other widths passes the homogeneity check (`[(1, 10), (x, 20)]` with
`x: i32`). The array is read as `(i64, i64)` elements, so `a[1]` reads wrong bytes.

**Closed with it**, each pinned by a test in the same file:

- a value typed by an integer literal it is not (a local bound by `let n = 5;` or `let p = (5, 6);`,
  a call such as `id(5)`, an enum construct built before its slot was known), narrowed to a 4-byte
  or `u256` slot, is rejected with the site's own code (T071, T041, T045, T049, T054, T055). The
  scalar form compiled to a module the engine refused (the `i32` half of the literal-binding entry
  below), except in a tuple element or a record field, where it ran with a wrong value. The compound
  form ran with its parts at other offsets: `let p = (5, 6);` passed to a `(i32, i32)` parameter
  read `(5, 0)`. The rule is per value, so it also rejects a value that happened to read back right
  because its only narrow part is its last (`let o = Some(5);` passed to an `Option<i32>` parameter,
  `let p = (1, 2);` into a `(i64, i32)`), failing closed. A function value whose parameter or return
  a literal typed is such a value too: its instance computes at the `i64` default. Passed to a
  resolved call's `Fn() -> i32` parameter, bound by `let k: Fn() -> i32 = g;` or returned as an
  `Fn() -> i32` (`g` from `constf(7, c)`), it was read as an `i32` and trapped at the indirect call,
  on main too. It is T071, T041 or T049 now, and it passes at `i64` and `u64`. The rule is per
  value, so a binding that is never called is rejected too, where main ran it, failing closed. A
  `Result` is left as it was: the `Ok`/`Err` shortcut below owns its typing;
- a generic function's argument is pinned once a turbofish or the arguments before it bind its
  type parameters, and fitted to its parameter type once the instance is known otherwise
  (`fit_to_instance_slot`): its literal parts are narrowed (a literal that does not fit its part
  is T071), and it is checked against the type at every depth. No generic call checked its
  arguments before, so a `(i64, i64)` argument for a `(i32, i64)` parameter compiled. Two
  differences are stored alike and pass, as they did before: a `u64` where a literal bound the
  parameter, which the literal's `i64` instance reads (and computes on signed, the OPEN entry
  below), and a bare `None` typed without arguments, which main passed too. A unit variant is a
  tag-only cell, but a method can give a value with a payload such a type (the OPEN entry on
  method arguments below). Any other difference in signedness is T071: `max(a, b)` with
  `a: u32` and `b: i32` compiled. A slot a literal bound is compared at the `i64` default
  through every type, so a `[i32; 3]` for `xs: &[T]` is T071 (the instance read its first
  element as the slice's length), and so is a function value whose return a literal typed,
  for an `i32` return (it trapped at the indirect call). Such a part of a function type is the
  `i64` its instance computes, so it reads alike at `u64` too: the same value passes for a `u64`
  return, and so does a `u64` closure beside a literal that bound a record's `T`. An earlier
  step of this change rejected both (T071), where main ran them. An out-of-range literal is
  reported once, at its span (`report_once`): the pin and the fit each reported it, and so did a
  tuple's element narrowed again at its argument or its `let`. A literal in a generic body that
  two instances narrow is reported once too, where main reported it once per instance. Two
  double reports from other
  checks remain: `let h: Hold<i32> = Hold { v: 5000000000 };` (the field check and the
  pinned-annotation check, on main too), and the record order below;
- an argument whose parameter type mentions a function type is inferred with no slot, since a
  closure in it binds a row variable, so the literals beside a closure kept the `i64` default:
  `g((c, (1, 40)), 0)` for `p: (Fn(i64) -> i64, (i32, i64))` read 171798691940. They are narrowed
  once the instance is known. An enum construct there is built before that, and is T071 where
  the instance reads it otherwise: `g(5, (Some(5), f))` for `t: (Option<i32>, Fn(i64) -> i64)`
  (main read it back right only because the narrow part is the cell's last). A generic enum
  binds no row variable (E011), so its function-typed payload is pinned like any other. An
  earlier step of this change left such a payload unpinned and unfitted with no instance in
  view, and `W::F((1, 40, f), 7)` for `F((i32, i64, Fn(i64) -> i64), T)` read 171798691940, as
  on main;
- a generic record's field or a generic enum's payload whose declared type mentions a type
  parameter, built with no annotation that names the instance, kept the widths it was typed
  with: `P { t: (1, 40) }` for `record P<T> { t: (i32, T) }`, and `let b = B::V((1, 40));` for
  `V((i32, T))`, read 171798691940. Each is now pinned once the parts written before it bind its
  type parameters, as a generic call's argument is (so `R { a: x, o: Some(5) }` and
  `E::V(x, Some(5))` build the `Some` at `Option<i32>`), and fitted to the instance otherwise; a
  part the instance does not read alike is T071 (a `bool` in the `i32` part compiled without a
  diagnostic). A part written before the part that binds its type parameter is built first, so
  an enum construct there is T071 (`R { o: Some(5), a: x }`), as the same order is for a generic
  call; main read it back right only because the narrow part was the cell's last. A record's
  pin takes the bindings of the fields written before it, as a generic call's does, where a
  concrete type nested in a later field replaces a literal's binding. Its instance is built from
  the fields in declared order instead, where the first binding wins and nothing replaces it. So
  a literal in the first declared field that binds `T` builds the `i64` instance: a `u32` beside
  it (`Pair { a: 5, b: u }`) is T071, since the 4-byte value sat in an 8-byte field and `p.b`
  read 4 bytes past it, the next allocation's, and so is `R { a: 5, o: s }` with
  `s: Option<i32>` (main read `r.o` as 21474836485), where `f(5, s)` builds `f<i32>`. Written
  the other way round, `R { o: s, a: 5 }` pins the literal to `s`'s `i32` and reads back 5: the
  verdict follows the written order, and both verdicts are sound. Where the two rules disagree,
  the instance is the declared order's, and a field the pin typed otherwise is T071 too:
  `R { a: 5, o: s, c: 7 }` is T071 for `o` and again for `c`. A nested construct the pin typed
  reports a conflict with an earlier field's binding as an annotation's (T071, for
  `R { a: x, inner: Hold { v: y } }` with `x: i32` and `y: i64`), where main reported the two
  bindings' conflict (T234). Both fail closed. A generic enum's
  payload is the same: `PE::P(5, x)` with `x: i32` is T071 (main read it back as 57 only because
  the cell is allocated at the instance's size and the slot's high bytes were zero);
- a closure passed to a generic function was checked for its effect row only, and only at a
  top-level function-typed parameter, so one taking a `(i64, i64)` for `Fn((i32, i64)) -> T` read
  its argument at other offsets, at the top level or inside a tuple, an `Option`, a generic
  record's field or a generic enum's payload (171798691841 once the argument was laid out at its
  slot's widths; main returned 1, by accident). Its parameter and return types are now checked
  wherever it sits, a parameter against the value the instance passes in, so a bare `None`
  passed in for an `Option<i64>` parameter fits. Its effect row is not: the OPEN entry below;
- a closure's parameter and return annotations were resolved without the arity check that a
  non-generic signature's, a `let`'s, a field's and a payload's types have, so
  `fn(o: Option) -> i64` typed a value that may carry a payload as an enum without type
  arguments, which a generic call accepts in any instance's place: `or_default(o, 7)` inside
  such a closure read a 4-byte payload as 8 bytes (4294967301). They are now T231. A generic
  signature still skips the check (the OPEN entry on method arguments below);
- a closure-typed local's arguments are pinned to its parameter types;
- a generic call whose type parameter a literal binds first keeps that literal's `i64` instance
  (the first top-level binding wins, X-M7), so a later argument or a result stored otherwise
  (`id2(5, n)` with `n: u32`, `let x: u32 = id(5);`) is rejected (T071, T041). Each compiled to a
  module the engine refused. Taking the instance from the slot instead would accept them; that
  is an inference change of its own, and until it lands they fail closed.

---

## A `u64` read by the `i64` instance a literal chose computes signed — OPEN

**Status:** Open. Found 2026-10-04 in SR-032's fifth review; pre-existing, measured the same on
`main` (`77b85c2`). Pinned by `known_gap_u64_where_a_literal_bound_the_instance_computes_signed`
in `crates/sigil-runtime/tests/construct_slot_width.rs`, which is written to fail when the gap is
closed. Owner: `sigil-compiler` type checker (generic call inference, `unify_inner`). Review
point: with the inference change that takes a generic instance from its strongest binding, and
before any claim that a generic call computes at its arguments' signedness.

**Vector:** in a generic call a literal binds a type parameter first and weakly, and a later
top-level argument does not replace it (X-M7, kept for parity with the self-hosted checker), so
`max(0, n)` with `n: u64` builds `max<i64>`. A `u64` is stored as an `i64` is, so the call passes
it as main did, but the instance compares and divides it signed: with `n` at `u64::MAX`,
`max(0, n)` returns 0. The mirror case passes too: a function whose return a literal typed
computes an `i64`, and a `u64` slot reads those bits unsigned. `big(d, g)` with `d: u64` and `g`
from `constf(7, c)`, where `c` returns -1, compares -1 as `u64::MAX` and returns 1, as on main,
and as `let u: u64 = n;` does for `let n = 0 - 1;`.

---

## A closure's effect row is lost through a generic parameter that is not a top-level `Fn` — OPEN

**Status:** Open (attack surface). Found 2026-10-04 in SR-032's fifth review, and widened in its
sixth; pre-existing, measured the same on `main` (`77b85c2`). Pinned in the outer ring, which
checks effects, by `known_gap_closure_effect_row_through_a_generic_parameter` in
`crates/sigil-runtime/tests/construct_slot_width.rs`, which is written to fail when the gap is
closed, beside its top-level twin and a direct call (both E001). Owner: effect checker (`bind_and_check_effect_rows` in
`type_check/expressions/calls.rs`). Review point: before any claim that a pure function performs
no effect, and with any change to row binding for generic calls.

**Vector:** `bind_and_check_effect_rows` binds and checks a closure's effect row only against a
formal written `Fn(..)` at the top level of a generic function's signature, and the instance's
indirect call discharges the formal's row, not the closure's. A closure that reaches the
instance any other way keeps no row: passed as `b: T` beside a pure closure (`pick(p, q)` returns
a value of the pure closure's type), inside a tuple (`p: (Fn(i64) -> T, i64)`), or stored in a
generic record's `Fn(i64) -> T` field. A pure `tool_main` in the outer ring then calls a closure
that performs `Log`, and returns 9. SR-032's argument check compares a closure's parameter and
return types at every depth, but not its effect row or its linearity. Linearity is lost through
the same slots and more: the next entry.

---

## A linear closure passed through a generic slot is called more than once — OPEN

**Status:** Open (attack surface). Found 2026-10-05 in SR-032's eighth review; pre-existing,
measured the same on `main` (`7693116`). Pinned by
`known_gap_linear_closure_through_a_generic_slot_is_called_twice` in
`crates/sigil-runtime/tests/construct_slot_width.rs`, which is written to fail when the gap is
closed. Owner: `sigil-compiler` type checker (`type_compatible`'s `Fn` linearity rule, which
rejects the two twins below, and SR-032's argument check, `stored_alike`). Review point: before
any claim that a typestate value is consumed at most once through a function value.

**Vector:** a closure that captures a typestate value is linear: `q` below moves `a: File<Open>`
into `shut`, so it may run once. A resolved call's non-linear `Fn() -> i64` parameter rejects it
(T071), and so does a generic enum's concrete `Fn() -> i64` payload. But a generic function's
`Fn() -> i64` parameter (`twice(1, q)` for `twice<T>(d: T, f: Fn() -> i64)`), a generic enum's
`Fn() -> T` payload and a generic record's `Fn() -> T` field each take it. The program then calls
it twice, so `shut` consumes the same `File<Open>` twice, and each program returns 6 (3 + 3).
Fallback 1 checks no argument's linearity, and SR-032's fit to an instance compares a closure's
parameter and return types, not its linearity or its effect row.

---

## A method's argument is not checked, and a generic signature skips the arity check — OPEN

**Status:** Open (attack surface). Found 2026-10-04 in SR-032's sixth review; pre-existing,
measured the same on `main` (`77b85c2`). Pinned by `known_gap_method_argument_is_not_checked` in
`crates/sigil-runtime/tests/construct_slot_width.rs`, which is written to fail when the gap is
closed. Owner: `sigil-compiler` type checker (method calls in `type_check/expressions/methods.rs`,
signature validation in `type_check/mod.rs`). Review point: before any claim that a method call
checks its arguments, or that an enum type written without type arguments is a tag-only cell.

**Vector:** a method call checks an argument only for an integer literal's fit, a machine-integer
parameter and a top-level function-typed parameter; any other argument is passed as it is. A
`(i64, i64)` passed for a method's `(i32, i64)` parameter is read at the parameter's offsets
(171798691940), where the free-function twin is T071. A generic function's or generic impl's
signature is not held to the arity rule (T231), so `fn keep<T>(o: Option, d: T)` compiles where
its non-generic twin is T231. Together they give a value that carries a payload an enum type
written without type arguments, which SR-032's argument check accepts in any instance's place,
as main did: an `Option<i32>` passed to a generic impl method's `o: Option`, or to `x: T` of a
`Holder<Option>` built from `Holder { v: None }`, reaches `or_default(o, 7)`, which reads its
4-byte payload as 8 bytes (4294967301).

---

## An unborrowed array passes for a slice parameter — OPEN

**Status:** Open. Found 2026-10-04 in SR-032's sixth review; pre-existing, measured the same on
`main` (`77b85c2`). Pinned by `known_gap_unborrowed_array_passes_for_a_slice_parameter` in
`crates/sigil-runtime/tests/construct_slot_width.rs`, which is written to fail when the gap is
closed. Owner: `sigil-compiler` type checker (`type_compatible`). Review point: any change to
slice coercion or to `type_compatible`'s slice arm.

**Vector:** `type_compatible`'s slice arm is commented as the coercion of a borrowed array
(`&[T; N]` for `&[T]`), but a borrow is already typed as a slice (`infer_borrow_expr`), so the arm
matches only an unborrowed `[T; N]`, and no coercion builds a slice at the call. So `count(arr)`
for `xs: &[i32]` with `arr: [i32; 3]` reads the array's first element as the slice's length (7);
`count(&arr)` reads 3.

---

## A type argument left `Type::Error` with no diagnostic — OPEN

**Status:** Open. Found 2026-10-04 in SR-032's sixth and seventh reviews; pre-existing, measured
the same on `main` (`77b85c2`). Pinned by `known_gap_unreported_error_type_argument_carries_a_payload`
in `crates/sigil-runtime/tests/construct_slot_width.rs`, which is written to fail when the gap is
closed. Owner: `sigil-compiler` type checker (`infer_path_expr`'s qualified unit variant, and the
unbound type parameters of Fallback 2's enum construct). Review point: before any claim that a
`Type::Error` was reported where it arose.

**Vector:** two sources type a value with `Type::Error` and no diagnostic.

- `let mut o = Option::None;` is typed `Option<Error>`, and `o = Some(x)` with `x: i32` is then
  accepted. `Type::Error` is compatible with every type, so SR-032's fit of `pick(d, o)` for
  `pick<T>(d: T, o: Option<T>)` with `d: i64` passes `Option<Error>` for the `Option<i64>` slot,
  and the instance reads the 4-byte payload as 8 bytes (4294967301).
- A type parameter that no payload binds and no expected type names: in the `Either::R(r)` arm
  of `let e = Either::L(7);`, `r` has that type. `let y: i32 = r + 1;` passes the type checker,
  and the backend then panics on the operand it cannot lower ("unsupported binary op Add for type
  Unit"), measured by probe on `main` (`7693116`) and on SR-032's seventh-review head. No test
  program pins the crash: the SHP gate compiles every program in the test files with production,
  and holds production's crashes to a shrink-only set (`SHP_ORACLE_PANICS`), so the crash is to
  be fixed rather than added. An out-of-range literal beside it (`r + 5000000000`) is reported
  (T041), as on main, pinned by `out_of_range_literal_beside_an_unreported_error_is_reported`.

---

## A `match` on an `Ok`/`Err` shortcut runs the other arm — OPEN

**Status:** Open. Found 2026-10-04 while testing SR-032; pre-existing, measured on the compiler
before that change. Pinned by `known_gap_result_shortcut_match_runs_the_other_arm` in
`crates/sigil-runtime/tests/construct_slot_width.rs`, which is written to fail when the gap is
closed. Owner: `sigil-compiler` (Result lowering in `air.rs` and match dispatch). Review point:
before any claim about `Result` values, and with any change to `lower_result_ctor`, `ResultTry`
or enum match dispatch.

**Vector:** `Ok(..)` and `Err(..)` parse to a shortcut that lowers to a record `{ is_ok, value }`
with `is_ok = 1` for `Ok`, which `?` (`ResultTry`) reads that way. A `match` reads offset 0 as the
stdlib enum's variant index, where `Ok` is 0, so it runs the other arm:

```sigil
let r: Result<i32, i64> = Ok(3);
match r { Ok(v) => { return 100 + v.as_i64(); }, Err(e) => { return 200 + e; } }
```

returns 203, and `Err(4)` returns 104. The shortcut also infers its value with no expected type
(`check_result_ctor_expr`), the SR-032 class: the `3` is stored at the `i64` default, which `?`
reads at the slot's width from the same offset (the low bytes, on this little-endian target). The
SR-032 slot rule leaves a `Result` as it was until this entry is fixed.

---

## A bare unit variant several enums declare resolved to a random enum — CLOSED

**Status:** Closed. Found 2026-10-04 in SR-032's second review. Pinned by
`ambiguous_bare_unit_variant_takes_the_slot_enum` in
`crates/sigil-runtime/tests/construct_slot_width.rs`. Owner: `sigil-compiler` type checker
(`infer_path_expr`).

**Vector:** a bare unit variant (`Q`, with no parentheses) took the first declaring enum in
`universe.enums` order, which is a `HashMap`'s. With `enum E1 { P, Q }` and `enum E2 { Q, R }`,
`let e: E2 = Q;` compiled or failed (T046) from run to run. It now takes the enum its slot names,
as a payload variant does (`classify_variant_callee`), and is T236 when no slot chooses. The
self-hosted checker still rejects such a variant (T060) where production now accepts it: the SHP
gate counts that a refusal, not a divergence, and no corpus program holds the shape.

---

## `ct_lt` misordered an 8-byte pair whose difference did not fit in an i64 — CLOSED

**Status:** Closed 2026-10-04 in `sigil-compiler` (`wasm.rs`, the `IntrinsicCtLt` sequences, with
the order carried in AIR) and in the self-hosted emitter that mirrors it. Found the same day while
fixing the narrow `ct_*` operand miscompile (T075).

**Vector (measured with `sigil forge` on main at `77b85c2`):** `ct_lt(a, b)` lowered to
`((a - b) >> 63) & 1` over i64 locals, the sign bit of the WRAPPING difference. That is the signed
order of the pair only while the true difference fits in an i64, and a `u64` operand was read as a
signed value:

- `ct_lt(i64::MIN, 1)` was false, and `ct_lt(i64::MAX, -1)` was true;
- on `u64` operands, `ct_lt(2^63, 0)` was true.

So a constant-time bound written as `ct_lt(index, limit)` on a `u64` the caller controls could pass
a value of 2^63 or more. The sequence was constant-time; only its answer was wrong.

**Fix:** `ct_lt` takes the sign bit (`>> 63`, a constant shift) of an overflow-safe word (Hacker's
Delight §2-12): `(a - b) ^ ((a ^ b) & ((a - b) ^ a))` for two `i64`, the signed order, and
`(!a & b) | ((!a | b) & (a - b))` for two `u64`, the unsigned order. The type checker gives both
operands one signedness (`unify_ct_lt_operands` in `type_check/expressions/intrinsics.rs`): an
integer literal beside a `u64` is checked as a `u64`, as the type checker checks it beside `<` (so
a negative literal there is `T075`), and one `i64` beside one `u64` is rejected with `T075`, since
that pair has no single order. The order travels in AIR
(`AirStmt::IntrinsicCtLt`'s `unsigned`), never from the operand locals' types: an un-annotated
literal binding keeps an `i64` local where its use checks as a `u64`. Each sequence is still ALU
ops on locals with a constant shift amount, and `taint_ct_audit.rs` scans both. The self-hosted
emitter emits the same two sequences, with one seed succession. It refuses a mixed pair, an integer
literal beside a `u64` included, rather than pick an order.

**Pinned by:**
- `ct_lt_orders_every_i64_pair_at_the_extremes` and `ct_lt_orders_every_u64_pair_at_the_extremes`
  in `crates/sigil-runtime/tests/int_convert.rs`: every ordered pair of a set that holds both ends
  of the type and the values on each side of its sign boundary, against Rust's `<`;
- `ct_lt_orders_a_literal_beside_a_u64_by_unsigned_value` (same file): a literal and an
  un-annotated literal binding beside a `u64`;
- `ct_lt_orders_an_i32_widened_to_u64_by_its_unsigned_bits` (same file): an `i32` widened with
  `.as_u64()` is a `u64` and orders by its unsigned bits, which the `T075` hint for a 4-byte
  operand warns of;
- `ct_lt_refuses_a_mixed_signedness_pair_and_a_conversion_admits_it` and
  `ct_lt_refuses_a_negative_literal_beside_a_u64` in
  `crates/sigil-compiler/tests/taint_constant_time_phase_b.rs`;
- `shp1_fences_hold_on_the_committed_seed` and
  `shp1_mixed_signedness_ct_lt_is_rejected_by_production_and_refused_by_the_seed` in
  `crates/sigil-runtime/tests/selfhost_backend_parity.rs`.

Run against the compiler before the fix, the four `int_convert.rs` tests fail: the `i64` matrix on
`(i64::MIN, 1)`, the `u64` matrix on `(0, 2^63 + 1)`, the literal test, and the widened `i32` on
`(-1, 1)`. The first three replace
`known_gap_ct_lt_misorders_a_pair_whose_difference_overflows`, which pinned the gap as it stood.

---

## An un-annotated literal binding keeps an `i64` local where its use checks as another type — OPEN

**Status:** Open (attack surface), pre-existing, beside a `u64`; closed where a use checks it as an
`i32` (the second bullet below). Found 2026-10-04 while fixing `ct_lt` (the entry above), whose fix
carries the order in AIR for this reason; measured with `sigil forge` on that branch. Pinned as it
stands by `known_gap_literal_binding_beside_a_u64_takes_signed_arithmetic` in
`crates/sigil-runtime/tests/int_convert.rs`, written to FAIL when the gap is closed for any of its
shapes. Owner: `sigil-compiler` (PIL literal resolution, AIR lowering). Review point: before any
claim that `u64` arithmetic is exact, and with any change to literal defaulting or to how the
emitter picks an operator's signedness or width.

**Vector:** a binding of an un-annotated literal, by `let n = 5;` or by a tuple pattern
(`let (a, b) = (5, 6);`), checks as the type each use gives it: beside a `u64` it is a `u64`
(`infer_binary_expr` gives an integer-literal operand the other operand's type). But the binding's
local keeps the default `i64`, and the emitter takes a binary operator's signedness and width from
its left operand's local (`function.var_type(*lhs)` in `wasm.rs`). So:

- beside a `u64`, `<`, `<=`, `>`, `>=`, `/`, `%` and `>>` each give the signed answer. With
  `let five = 5;`, `let ten = 10;`, `let all_ones = 0 - 1;`, `one: u64` and `max` the `u64`
  2^64 - 1: `five < max` is false, `five > max` is true, `ten / max` is not 0, `ten % max` is 0,
  and `let s: u64 = all_ones >> one;` keeps the sign bit. A tuple-pattern binding gives the same
  `<`. The literal itself (`5 < max`), an annotated binding (`let five: u64 = 5;`) and
  `ct_lt(five, max)` give the unsigned answers.
- where a use checks it as an `i32` (assigned to one, beside an `i32` operand on either side as in
  `x + n` or `x == n`, or passed to an `i32` parameter), the binding's `i64` local met an `i32`
  one, and the module did not validate: wasmtime refused it before it ran, but the checker had
  accepted the program. **Closed** by SR-032 (the construct-slot entry above): a value typed by an
  integer literal before its slot was known is rejected wherever a 4-byte slot would narrow it,
  with the site's own code (T041 for a `let`, T054 or T055 beside an `i32` operand, T071 for an
  argument). `literal_binding_used_as_an_i32_is_rejected_at_the_use` in `int_convert.rs` pins
  each of these five uses, for a `let` binding and a tuple-pattern one, beside an annotated twin
  whose module validates. It replaces
  `known_gap_literal_binding_used_as_an_i32_builds_an_invalid_module`, which pinned the gap as it
  stood.

**What bounds it:** only a binding of an un-annotated literal, beside a `u64`, and only on the
left of a binary operator: on the right its bits are the same in either local, and the left
operand picks the order. A use that would narrow it to a 4-byte slot is rejected (above). Every
annotated binding, every literal operand and every `ct_lt` call gets the checked type.

**Fix direction:** give each use whose checked type differs from the local's that type: copy the
binding into a fresh local of its checked type at such a use (as `index_for_bounds_check` does for
a bounds-check index), or give the binding its use type when all its uses agree. It changes bytes
wherever such a binding is used, so it needs its own parity-manifest measurement and a self-hosted
mirror under the keep-up policy.

---

## A narrowing's refinement reaches a binding that shadows its name — CLOSED by DBC-0a (2026-10-14)

**Status:** Closed. Found 2026-10-06 while fixing SR-035; pre-existing, measured the same on `main`
(`d7ac39a`). Every binding site now writes an entry for its name into the innermost
`pattern_refinement_stack` frame — the bound value's facts, or an empty one — and `check_block`
keeps a frame per block, so `lookup_pattern_refinement` stops at the innermost binding and an outer
name's facts never reach a binding that shadows it (the design-by-contract spec's DBC0-1). Pinned
as exact refusals (T211) by `narrowing_stops_at_a_binding_that_shadows_its_name` in
`crates/sigil-runtime/tests/instance_body_context.rs` (a `let`, a `match` binding, a closure
parameter), `narrowing_fact_stops_at_a_binding_that_shadows_its_name` and
`refined_parameter_fact_stops_at_a_binding_that_shadows_it` in
`crates/sigil-compiler/tests/refinement_fact_lifetime.rs`, and `z3_corpus` fixtures 104 and 105.
The second DBC-0a review found two binding sites the rule had missed, closed the same day: a
tuple `let`, whose desugar wrote its entries into a frame the nested block had already popped
(the tuple forms of the two `refinement_fact_lifetime` tests above), and a binding that reuses
the name of an outer `let mut` (a `let`, a tuple binding, a `match` binding, an iterator loop
variable), which T042's by-name mutable set still lets the scope assign while its entry said
immutable, so a narrowing on it or the refined value it was bound to survived the assignment
(`a_binding_that_reuses_an_assignable_name_carries_no_fact`). An entry is now mutable wherever
the name is assignable. Soundness row: SR-037 in `docs/RESIDUAL_RISKS.md`, Closed once the entry
below closed the field store. The vector, as found:

**Vector:** `if x > 0 { .. }` pushes a frame that refines the NAME `x`, and every lookup of a
local named `x` inside the arm finds it, whatever binding the name denotes there. A `let x` in the
arm, a `match` arm's binding `Some(x)`, a closure's parameter `x` and a loop variable `x` (`for x
in arr`, or a range loop that pushes no frame of its own: one whose start is not the literal `0`,
or whose end is not a constant) each shadow the narrowed `x` with a value that has no such fact,
and the frame still discharges a refined call: with `fn validate(x: i64) where x > 0`,
`if x > 0 { let x: i64 = 0 - 7; validate(x) }` compiles and runs `validate` with -7 (each of the
first three forms returns -7 through `validate`; `for x in arr` over `[-7, -7]` runs it with -7,
`for x in 0-9..0-7` with -9 and -8, and `for x in 0..n` with 0). SR-035 stopped the same frame
from reaching a different function's body (an instance first created inside the arm), and made a
range loop's own fact and frame refuse every rebinding in the loop body, expressions included;
within one function body, a binding that shadows an `if` or `match` narrowing is the open part. A
fix shadows the name in the current frame wherever a binding enters scope (`let`, a pattern, a
closure parameter, a loop variable), so that its lookup finds no fact.


**The same frame carries a refined parameter.** `check_function_block` pushes each refined
parameter's clauses as a frame keyed by the parameter's name, so a `let` that shadows a refined
parameter inherits its predicate: inside `fn relay(x: i64) where x > 0`, `let x: i64 = 0;
need_positive(x)` compiles (the design-by-contract spec's probe P13). Pinned by
`known_gap_refined_parameter_reaches_a_binding_that_shadows_it` in
`crates/sigil-compiler/tests/refinement_fact_lifetime.rs`, beside a twin that binds a new name and is
refused with T211 — now `refined_parameter_fact_stops_at_a_binding_that_shadows_it`, refusing both. The
fix above closed it too.

---

## A refinement fact outlives a field store — CLOSED by DBC-0b (2026-10-14; the assignment forms by DBC-0a the same day)

**Status:** Closed (soundness row SR-037 in `docs/RESIDUAL_RISKS.md`, Closed; tracked in #832).
Measured 2026-09-22 by the design-by-contract spec (draft PR #761, section 3.1,
probes P4, P8, P10 and P11) and re-measured 2026-10-08 on `main` (`e3a33349`): each form below
compiled with no diagnostic, and with the solver was certified `solver_verified: true` (Z3 4.16.0);
its twin, the same call with no stale fact, is refused with T211 in both builds. The assignment
forms are closed: a `mut` binding carries no fact — a narrowing on it records nothing, and a
`let mut` of a refined value keeps nothing (DBC0-2) — so each is refused with T211 in both builds,
pinned by `refinement_fact_dies_with_its_mutable_binding` (beside
`an_immutable_binding_keeps_its_fact`, which shows the immutable forms still discharge) in
`crates/sigil-compiler/tests/refinement_fact_lifetime.rs` and by `z3_corpus` fixtures 101–103. The
same holds for a binding whose name the scope may still assign (an immutable binding that reuses
an outer `let mut`'s name: `a_binding_that_reuses_an_assignable_name_carries_no_fact`) and for an
actor state field the body may write (a `mut` field in a handler, any field in `init`:
`an_assignable_state_field_carries_no_fact`), both found by the second DBC-0a review. The
field store is closed by DBC-0b: every store into a refined record's field carries the
construction site's obligation, keyed on the place's record type, pinned in the same file by
`a_field_store_is_a_refinement_sink` (a local's field, a nested field, an array element's field,
a place reached through a `&mut` borrow, a store through an `@Mut` parameter) and
`a_store_into_a_state_fields_record_is_a_refinement_sink` (T210 with the solver; without it the
obligation is collected and not decided, SR-038), `a_field_store_without_a_fact_for_the_clause_is_refused`
(T211 for a value with no fact, a value computed from the field and a compound store; T215 for a
narrowed value with a weaker bound) and `a_store_into_a_cross_field_clauses_field_is_refused`
(T216, either side), each beside the store that keeps the invariant, and by `z3_corpus` fixtures
106–110. Owner: `sigil-compiler` type checker (`type_check`, which records the facts, and
`type_check_v2`, which collects the obligations). Review point: closed; a store site added to the
typed AST without its obligation reopens it.

**Vector:** with `fn need_positive(x: i64) where x > 0`:

- **An assignment does not end a fact — CLOSED.** A fact was recorded for a NAME: a narrowing's
  frame (`if y > 0`), or the refinement a `let` carries from a refined return (`let mut p = pos()`
  with `fn pos() -> i64 where @ > 0`). An assignment to the name gave it a new value and left the
  fact in place: `let mut y = input; if y > 0 { y = 0; need_positive(y) }`; the same narrowing across a
  loop back-edge, `if y > 0 { while y > -5 { need_positive(y); y = y - 1; } }`, which calls
  `need_positive` with 0 to -4 on the later iterations; and `let mut p = pos(); p = 0 - 3;
  need_positive(p)`. The in-code note `V4-W4S10` (`type_check/statements.rs`) described only the
  first form; it now records the rule that closed all three.
- **A field store is not a refinement sink — CLOSED.** A read of a refined record's field takes its
  fact from the record TYPE (`compute_field_access_refinement` reads `record_refinements`), and the
  obligation collector never looked at an assignment's target, so `let mut i = Index { value: 200 };
  i.value = 5; need_big(i.value)` compiled with `record Index { value: i64 } where value > 100` and
  `fn need_big(x: i64) where x > 100`. The broken invariant then held for every later read of the
  field, in any function, while whole-record construction and reassignment were sinks (z3-corpus
  #27). The collector now walks every statement of every typed function body (nested and
  expression-borne blocks included) and gives a store into a refined record's field the
  construction site's dispatch: a literal is a `LiteralFits` obligation, a value with a fact a
  subsumption obligation, a value with no fact or a compound store a T211 refusal; a store into a
  field a cross-field or `length()` clause joins to a sibling is refused with T216, because the
  sibling's current value is not tracked.

A binding that shadows a narrowing or a refined parameter was the entry above, closed by the same
change. Keying facts by binding (the spec's DBC-0a) ended a fact at an assignment; the field store
got its own sink (the spec's DBC0-3, DBC-0b): the store is checked against the record's `where`
clause as construction is.
