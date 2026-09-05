# CSIR v9 occurrence declaration envelope

Status: **production unary occurrence enforcement, dual-gate phase**. Every
successful compiler result is now authorized through the linked v9 verifier over
this exact envelope. That verifier first re-runs the complete retained-v8 decision,
then derives v9 semantic dataflow, structured occurrence frontiers and invocation
influence before enforcing destination, FFI, actor, state-write and root-return
occurrence ceilings. A successful declaration decode alone remains neither a
security verdict nor approval of the declared host implementation.

## Canonical framing

The header is `CSIR`, little-endian version `9`, and a little-endian record count.
Every record is 32 bytes. The count includes all chunks and declarations; the
64 MiB byte ceiling and one-million-record ceiling apply to the entire envelope.
Encoding expansion means a profile that fits its standalone limit need not fit
inside CSIR. Oversized envelopes fail closed.

The exact v8 record prefix comes first. Tags 0–43 retain their meanings and bytes,
including their canonical node IDs. The v8 decoder is unchanged and still rejects
version 9. The new decoder reconstructs only that prefix's v8 header for decoding;
it does not reinterpret the whole v9 packet as v8 or treat v8 acceptance as a v9
policy verdict. The new decoded type explicitly retains model version 9.

Offsets within each appended record are: tag at 0, labels at 1–2, flags at 3,
five little-endian words at 4–23, global node ID at 24–27, and zero at 28–31.
Node IDs are one-based positions across the entire envelope. No source spans or
computed security verdicts occur in these records.

| Tag | Record | Five words / content |
| --- | --- | --- |
| 44 | Manifest | Prefix record count, profile byte length, FFI binding count, actor binding count, function-root count |
| 45 | Byte chunk | Twenty verbatim bytes; unused trailing bytes must be zero |
| 46 | FFI binding | Semantic owner node, profile operation index, first argument operand position, parameter count, result count |
| 47 | Actor identity | Semantic owner node, subtype, zero, zero, zero |
| 48 | Function/root contract | Function ID, actor type ID, handler ID, export-name byte length, entry-actor bit |

The order is manifest, profile chunks, FFI bindings, actor identities, then one
function/root contract followed immediately by its export-name chunks for every
function. Bindings follow their owners' instruction order; functions follow their
canonical IDs. Duplicate, missing, reordered, unknown, nonzero-reserved and trailing
records refuse. Manifest/chunk/FFI/actor label and flag bytes must be zero.

## Host and actor binding

A zero profile length means **unknown legacy host semantics**, not a private
profile. An explicitly empty profile still has its complete nonempty canonical
encoding. Profile chunks retain every provider identity, revision, operation,
domain, scope, label and footprint checked by the independent host-profile codec.

Every FFI instruction has exactly one binding. With a profile, its operation
index is one-based and must resolve to the exact module `ffi`, exact name and
ordered Wasm signature. Without a profile it must be zero, explicitly unknown.
Names come from the instruction's existing exact string-immediate operands;
argument/result types come from its actual referenced value declarations. Missing
owners, ambiguous declarations, malformed slices, nonzero name padding, reordered
arguments and mismatching identities or ABI refuse. The pointer-domain contract
is retained, not inferred from scalar type equality.

Actor subtypes are send=1, ask=2, spawn=3, serialize=4 and deserialize=5. Every
actor instruction has exactly one identity record. The codec preserves the
supplied subtype rather than guessing it from arity. Source projection checks it
against the actual AIR constructor and metadata. The current raw machine emits a
boundary event for all five subtypes, so production v9 conservatively requires a
Public occurrence for each. A future operational distinction would require a new
proved policy; the codec alone cannot authorize an otherwise malformed operation.

## Function/root declarations

Every function has a contract, including internal functions. Role flags are:
internal=0, module initializer=1, module function=2, actor initializer=3 and actor
handler=4. Exposed roles must match the existing function kind. Closure functions
and `$`-prefixed synthetic exports are internal; their identity fields and
occurrence labels use canonical zero placeholders. Exposed export names are
nonempty, exact valid UTF-8 and unique, with no normalization. They are bounded
by the whole envelope, not by the host-name grammar. Hash-derived actor/handler
IDs may legitimately be zero.

The two labels declare entry and root-return **occurrence**, independently of
return-payload confidentiality. The codec can represent Public, Internal and
Secret declarations; SecretCT is not a variable-time boundary declaration.
Current source projection supplies Public defaults for exposed roots. It does
not infer private roots or private actor endpoints from payload annotations.
The record ID supplies a stable function-boundary identity for future raw v9
semantics; this does not change historical v8 output events.

## Production evidence and remaining boundary

`formal::project_v9_declarations` projects real TypedProgram/AIR input without
constructing a `FormalSecurityReport`. Production `formal::verify_with_context`
uses the same projector, calls only the linked `sigil_csir_v9_verify` decision,
and constructs a model-9 report only after its zero verdict. The report hashes the
exact complete v9 bytes; schema-v9 certificates compare every report field against
fresh re-derivation and reject model/checker/CSIR drift as R819. The declaration
decoder remains a separate non-authorizing API.

An explicit host context is encoded into the checked envelope and the exact profile
fingerprint is emitted once into every generated Wasm ring. Contract-bound runtime
instantiation compares that section with the immutable profile whose callbacks and
ABIs were installed. Legacy actor and ephemeral entry points reject profile-bearing
artifacts they cannot honor; profile-free WAT remains supported by normalizing,
checking and compiling the same binary bytes.

The Rust codec and independent Lean codec consume the same source-built fixtures.
Their tests distinguish successful declaration decoding from both historical-v8
acceptance and the production v9 security verdict.
Regenerate fixture bytes only through the explicitly armed ignored test in
`formal_v9_declarations.rs`; ordinary tests compare the complete file inventory
and exact generated bytes.

Activation-aware raw call/return correspondence and the independent-length Public
theorem have since landed in `PublicBisimulationSecurity.lean`; they are downstream
of, and distinct from, the executable verifier's unary soundness/completeness result
described here. Complete accepted-corpus compatibility, cross-platform/performance
evidence, and the tagged dual-gate release are still required. No retained gate is
retired, and no private host behavior is proved merely by a profile declaration.
