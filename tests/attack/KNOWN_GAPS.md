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
