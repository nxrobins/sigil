# Self-hosted Wasm emission contract

**Status:** Implemented and current. This document replaces the historical SH-WASM W0-W5
rollout journal.

## Purpose

`selfhost/air.sigil` emits complete Wasm modules for the exact self-hosted AIR surface. The
authority is differential: supported modules must be byte-identical to
`wasm::emit(&fuel::insert(memory::lower(lower_oracle(src))).0)`, its inner module and, for a
program with an outer-ring module, its outer one; unsupported modules must return the explicit
`!!` poison sentinel. A single-ring answer is `OK:{hex}`; a two-ring answer is
`OK:{inner}|{outer}` (SHP-2b), and either module's refusal refuses both.

The Rust authorities are:

- `crates/sigil-compiler/src/air.rs`
- `crates/sigil-compiler/src/memory.rs`
- `crates/sigil-compiler/src/fuel.rs`
- `crates/sigil-compiler/src/wasm.rs`

The surrounding self-hosted AIR contract is documented in [sh-air.md](sh-air.md).

## Module contract

The covered surface preserves these module-level invariants:

- Each ring is its own module. The inner ring imports the eight fixed SIGIL runtime functions;
  the outer ring (every function of a `#[ring(outer)]` module) imports `fuel_decrement` and
  `alloc`, then one `ffi.{name}` per extern its functions call. Imports precede local functions,
  so `alloc` is `call 4` in the inner module and `call 1` in the outer one.
- A function's `FuncId` is its position in the complete function vector: every module in source
  order, both rings. Actor initializers and handlers occupy positions in that vector, and so does
  the synthesized initializer of a module that has no function of its own: production's
  `{module}__init`, type `() -> ()`, a body of `return` with no fuel prologue, exported always. A
  generic function is not a function of its own module. Production synthesizes the initializers
  first and then appends every monomorph instance to the first module, so a first module whose
  only function is generic holds its initializer, then the instances.
- A local function's Wasm index is its ring's import count plus its position among its ring's
  functions. A call to a function of the other ring has no index and is refused (production's
  ring checks reject it first, R004 and R007).
- Free functions export as `{module}__{function}`; actor functions export as
  `{actor}__{function}`. Export hygiene (oracle `wasm::emit`, 2026-09-01): only an externally
  callable function has an export entry. A free function is externally callable iff it is `pub`;
  impl methods (Public by default on both sides), actor initializers and handlers, and the
  synthesized module initializer always are; a monomorph instance inherits its generic's
  visibility. A withheld export never moves an index: the function keeps its type, code, and
  table entries, and the export section count drops by exactly the withheld entries.
- The type section contains the ring's import signatures followed by one entry per local function
  of the ring in vector order. It does not deduplicate equal local signatures. Production then appends, once
  each, every `call_indirect` signature that no local function carries; this emitter emits no
  `call_indirect`, so a module on the covered surface never carries one.
- A ring with functions has a table sized by the whole program's function count, and one element
  segment per run of consecutive `FuncId`s in the ring that places each function at its `FuncId`,
  so a slot of the other ring stays empty. A ring with no function has neither (an outer-only
  program's inner module is production's fixed empty module). Memory starts at one page, and
  `BUMP_PTR` starts at the aligned end of the ring's static string data.
- String segments are discovered in emission order per ring, deduplicated by contents, and packed
  from offset 1024 before the final eight-byte alignment, each ring from its own 1024.
- Unsupported expressions, statements, opcodes, actor-state operations, or module shapes taint
  the module. A tainted module cannot produce plausible Wasm bytes.

## Refusals and exact rules from SHP-0b

The never-diverge gate (`selfhost_backend_parity.rs`, [self-host-backend-parity.md](self-host-backend-parity.md))
found programs on which this emitter produced a module production does not, and its review found
more outside the gated corpora. Every class found is now exact or refused, and `SHP0B_FENCES` in
the same file pins programs of each class by name. These rules close the classes found. They are
not a proof that no other shape diverges: the gate bounds its corpora and the named fences.

Refused before any function is walked (`ai_program_refusal`; the census names the reason):

- an actor in an outer-ring module (SHP-2b; SHP-0b refused every outer-ring module): production's
  outer module imports neither `send`, `ask` nor `spawn`, and production now rejects the
  declaration itself (R014);
- a type alias, whose uses would be lowered at a guessed width;
- a `u256` or `i256` type, or an integer literal above `i64::MAX` (production types it `u256`):
  the emitter never builds the 32-byte cell such a value points to. The emitter reads a literal
  from its span, so a long literal that fits (19 decimal digits) is refused too;
- a call to a generic function with a higher-kinded type parameter, whose instance the walk
  cannot lower;
- a parse-error node reachable from the root: a construct the parser skipped cannot be shown to
  be codegen-free.

Typed by the slot (`cv_slot_var`). Production types an integer literal by the slot it is written
to, so every value written to a slot is typed by it here too: a call or method argument, a return
value, a record field, an array element, a tuple element, an enum payload, a field write or an
element write. A bare integer literal takes the slot's integer type. Any other value must already
carry the slot's type, or the program is refused. The typing reaches into compound values: an
array literal, a record construct or a tuple literal written to a slot whose declared type the
emitter can see is typed by that type, so an inner array's elements take its element type, a
nested construct's fields take its record's types and a tuple's elements take its element types
(the construct-slot rule, below). Where the slot's type is not visible to the emitter, a value
production types from context alone (a literal, or arithmetic over literals) is refused. These
cases fall here:
- an array literal under an assignment, or in a tuple whose own slot is not visible;
- a literal element of a tuple literal under an assignment, in an enum payload, or anywhere
  else the emitter lowers the tuple without its slot's type;
- a type-parameter field of a generic record with no instance in view;
- a literal in a type-parameter payload of a generic enum with no instance in view (an
  assignment, a record field, an array element, a nested payload);
- a parameter whose type the emitter cannot read;
- an enum payload whose declared type the emitter does not track (a record, `str`, an array or a
  tuple). Any other argument there takes its own type, except a tuple literal, which is refused:
  production would type its elements by the payload's.

A generic record construct whose slot names a monomorphized instance takes the instance's field
types, including a nested construct whose field type names an instance by its type arguments
(`Box<i64>` inside `Wrap<i64>`). A binary operand made of literal arithmetic takes the other
operand's type.

Refused where the shape appears:
- a constant of any declared type but `i64`;
- a pattern that binds one name twice;
- a call whose return type the emitter cannot resolve;
- a void method call (a statement `b.poke();` lowers through the value path, which would store a
  result that does not exist);
- `substr` bounds of any type but `i64`;
- a range-for index access (`a[i]`, read or written) inside an `if`, `while` or `match` that lies
  within the loop and names the loop variable in its condition or scrutinee (SHP-5a). Production
  tightens the index's interval with such guards (RF-M3, its refinement channel) and then elides
  the bounds check, keeps it, or rejects the access; this emitter carries no refinement channel,
  so it poisons rather than guess. An access no such guard encloses elides exactly as production
  does when the loop's bound fits the array (RF-M2) and keeps the check otherwise.

SHP-0b also refused a `byte_at` index of type `i32`, whose production bounds check was signed;
that index is now exact (the signed-index rule, below). It refused an enum payload argument made
of literals too, unless the payload was `i64` (or `u64` for a bare literal), because production
stored such an argument at the `i64` default even in a narrower payload; a payload is now a slot
like any other (the construct-slot rule, below).

Exact, matching the Rust authority:
- `i32` arithmetic and comparisons use the signed opcodes;
- a 4-byte constant is production's `value as i32`, so a `u32` literal of 2^31 or more encodes
  as a negative `i32.const`;
- a `Region` value is `i64`;
- a byte store always uses `i64.store8`, widening a 4-byte value with `i64.extend_i32_u` first;
- a `byte_at` index wraps to `u32` only when it is 8 bytes wide (a 4-byte signed one is copied,
  below);
- a qualified unit-variant last arm keeps its tag test, and the fall-through after the last
  tested arm jumps to the match's exit.

## Rules from SHP-1

Exact, matching the Rust authority (`SHP1_FENCES` in `selfhost_backend_parity.rs` pins one
program per rule):

- `load8(ptr)` is `IntrinsicLoad8`: its i64 destination is allocated before the pointer is
  lowered; the pointer is wrapped by `i32.wrap_i64` when it is 8 bytes wide; then `i32.load8_u`
  (align 0, offset 0), `i64.extend_i32_u` and `local.set`.
- `ct_eq` is `i64.xor` then `i64.eqz`. `ct_lt` is an overflow-safe word, then `i64.const 63`,
  `i64.shr_u` and `i32.wrap_i64`. For two `I64` operands (signed) the word is
  `(l - r) ^ ((l ^ r) & ((l - r) ^ l))`, for two `U64` operands (unsigned) it is
  `(!l & r) | ((!l | r) & (l - r))`, with `!l` as `l ^ -1` and each operand read again by
  `local.get` rather than held in a scratch local. (Changed 2026-10-04, with production's fix for
  the `ct_lt` overflow: it was `i64.sub`, `i64.const 63`, `i64.shr_s`, `i32.wrap_i64`,
  `i32.const 1` and `i32.and`.) `ct_select` is the branchless mask the `substr` lowering already
  emitted.

Refused: a `load8` pointer that is not an integer; a `ct_*` operand that is not 8 bytes wide, a
`ct_select` condition that is not `bool`, or a destination of any other type (production applies
i64 opcodes to the operands as given; a 4-byte operand, which gave a module that does not
validate, is now rejected by production's typecheck with `T075`, so for it this refusal is a
fail-closed backstop, pinned by
`shp1_narrow_ct_operands_are_rejected_by_production_and_refused_by_the_seed`); a `ct_lt` pair
whose operands differ in signedness (production rejects one `i64` beside one `u64` with `T075`,
pinned by `shp1_mixed_signedness_ct_lt_is_rejected_by_production_and_refused_by_the_seed`, but
checks an integer literal beside a `u64` as a `u64`, while the seed lowers the literal to an `I64`
local; `SHP1_FENCES` pins a literal and a literal binding beside a `u64` as refused); and a call to any
intrinsic the emitter lowers with the wrong argument count, refused where it stands rather than
resolved to a same-named function, since production resolves the intrinsic first. The `byte_at`
index rules are SHP-0b's, above, and the signed-index rule's, below.

## The signed-index rule (SR-030)

Production compared a 4-byte signed index with the signed `i32.ge_s` at its bounds checks, so a
negative index passed; it now copies that index into a `u32` local first
(`index_for_bounds_check` in `air.rs`). The emitter mirrors the copy wherever it lowers a bounds
check:

- a `byte_at` index, and an array element index on a read or a write, of type `i32` reaches the
  check through a fresh `u32` local: a typed copy (`local.get`, `local.set`, bits unchanged)
  allocated where an 8-byte index is wrapped, so the compare is `i32.ge_u`. A `u32` index is used
  as it is.

`SHP0B_FENCES` pins `byte_at_i32_index`, `array_read_i32_index` and `array_write_i32_index`. The
slice checks the fix also reached need no rule: the emitter refuses slice construction and
slice indexing.

## Rules from SHP-2b

Exact, matching the Rust authority (`SHP2_FENCES` in `selfhost_backend_parity.rs` pins one
program per rule):

- the two modules, each by the module contract above, answered as `OK:{inner}|{outer}`;
- a call to an `extern "ABI" fn` is production's `ExternCall`: its destination is allocated before
  the arguments are lowered, each argument is a `local.get`, then `call` the ring's FFI import, then
  `local.set` unless the extern returns `()`. No fuel is charged before it;
- the FFI imports are production's `collect_ffi_imports`: one per distinct key, the extern's name
  and the wasm types of the call's arguments and destination (not the declaration's), in the
  order the keys first occur over the ring's functions, each function's blocks in vector order
  and each block's statements in order. Each import has its own type entry, after the base
  imports' and before the functions'. Only an extern a call reaches is imported. The import
  count fixes every function index, so it is counted before any body is encoded, from the
  distinct externs the ring's functions call (the type check pins each extern's types to its
  declaration), and a ring whose encoded calls register another count is refused.

Refused: a call to an extern that returns `()` (production's type check rejects any call to a
`()` function as a value, `T073`, and the self-hosted one does not, so the emitter refuses it, as
it refuses such a direct call); an FFI call in the inner ring, which production's ring check
rejects first (R003); and an outer-ring actor, above.

Also refused before any function is walked (`ai_extern_refusal`): a program whose extern names the
emitter cannot resolve as production does. Production resolves an extern call in the caller's
module, where an extern is private to its module, makes it an FFI call only when it resolved to
an extern, and resolves an intrinsic's name before either. The self-hosted type check holds one
signature per name for the whole program. So the emitter refuses:
- a call to an extern another module declares (production rejects it, `T062`);
- an extern named like a function anywhere in the program (production resolves each call to
  whichever of the two the caller's module holds, which one signature per name cannot);
- one extern name declared in two modules;
- an extern named like one of production's intrinsics (`resolve_intrinsic_call`), called or not:
  production resolves the intrinsic first and never calls such an extern.

## Rules from SHP-5b

Exact, matching the Rust authority (`SHP5B_FENCES` in `selfhost_backend_parity.rs` pins one
program per rule):

- a capability type annotation, plain (`Fuel`) or a parametric usage (`Approval(2030)`), is a
  pointer-width local, production's `lower_type(Type::Cap)`; before this it was the `<skip>`
  sentinel, which poisoned every function binding one;
- `declassify(v, c)` and `declassify_ct(v, c)` are production's `SecurityRelease`: a fresh local
  of the value's type is allocated first and the value lowered into it, the cap operand becomes a
  local (a bare name is its own), a fresh pointer local is allocated as the dead ownership sink,
  and the statement copies the value to the destination and the cap to the sink (`local.get`,
  `local.set`, twice);
- `&x` on a local that is not an array is production's `Borrow`, a `local.get`/`local.set` copy;
- `c.restrict(auth)` is production's `CapRestrict`: `local.get c`, `i32.const` of the authority's
  bit (its index in the cap type's declaration, `AuthorityRegistry`), `call` the `cap_restrict`
  import (index 5 of the inner ring's full set), `local.set`; the mask is a 4-byte constant,
  production's `restriction_mask as i32`, so with bit 31 set (a 32-authority type's last
  authority, or its full mask) it is a negative `i32.const`. `c.restrict_deadline(n)` is the
  same statement with the full mask (every declared authority; 0 for a cap type declaring none),
  production's no-op authority restrict. The receiver is a name, resolved in the environment,
  and its cap type is read from the function's own bindings: a parameter's or an annotated
  let's annotation, or, for an unannotated let bound to a capability operation, its receiver's
  (MI-3);
- `c.split(n)` and `c.draw(n)` are production's `CapSplit` and `CapDraw`, one byte sequence:
  `local.get n`, `i64.const 0`, `i64.lt_s`, `if`, `unreachable`, `end` (the unconditional signed
  guard), `local.get c`, `local.get n`, `call` the `cap_split` import (index 6), `local.set`. The
  receiver is resolved before the amount is lowered, so a literal amount takes the local after
  the destination's, as in production.

Refused: a borrow of an array (production allocates a slice header, which this emitter does not
mirror) or of anything but a bare local (a slice range, a field, a call); a capability operation
whose receiver is not a pointer-typed local, whose cap type two bindings of the name give
differently (the resolver cannot order a shadowing against the use), or whose authority the cap
type does not declare (production's `T101`, before emission); a split or draw amount of any type
but `i64`; and, in the outer ring, every capability operation (the reduced import set has no cap
imports; production refuses with `R009` and the pipeline mirrors it before emission, so the arm's
own refusal is a backstop). Grants, `mint` and the actor statements stay refused at the stages before the emitter (SHP-7,
SHP-9); slots and regions are emitted since SHP-5c-3 (below).

## Rules from SHP-5c-3

Exact, matching the Rust authority (`SHP5C3_FENCES` in `selfhost_backend_parity.rs` pins one
program per rule):

- a `Slot<C>` annotation of a declared cap type is a pointer-width local, production's
  `lower_type(Named("Slot", [Cap]))`; a `Region` annotation an `I64` (the SHP-0b rule);
- `slot_new::<C>()` is production's `SlotNew`: `i32.const 8`, `call` the ring's alloc import
  (index 4 of the inner ring's full set, 1 of the outer ring's reduced set), `local.set dst`,
  then `local.get dst`, `i32.const 0`, `i32.store` at alignment 0 and offset 0 and the same at
  offset 4 — the tag and capability words zeroed. The destination is allocated before the
  operands (X6; there are none);
- `slot_put(s, c)` is `SlotPut`: `local.get s`, `i32.load` (alignment 0, offset 0),
  `i32.const 0`, `i32.ne`, `if`, `unreachable`, `end` (a full cell traps), `local.get s`,
  `i32.const 1`, `i32.store` (offset 0), `local.get s`, `local.get c`, `i32.store` (offset 4);
  the statement's `Unit` destination then takes production's placeholder `Assign dst 0`;
- `slot_take(s)` is `SlotTake`: `local.get s`, `i32.load` (offset 0), `i32.const 0`, `i32.eq`,
  `if`, `unreachable`, `end` (an empty cell traps), `local.get s`, `i32.load` (offset 4),
  `local.set dst`, then both words zeroed as at `SlotNew`. The destination is allocated before
  the slot operand (X6);
- a `region name(limit) { body }` statement lowers as production's `lower_region_expr`: the
  statement's `Unit` destination is allocated first, the limit lowered to a local, a `U32` save
  local allocated; `RegionBegin` is `global.get 0` (the ring's bump pointer), `local.set save`;
  the body's statements inline into the enclosing block over a scoped environment; `RegionEnd` is
  `global.get 0`, `local.get save`, `i32.sub`, `local.get limit` (after `i32.wrap_i64` when the
  limit is 8 bytes wide), `i32.gt_u`, `if`, `unreachable`, `end`, `local.get save`,
  `global.set 0` — the trap when the net allocation exceeds the limit, then the rewind. The
  reclaim is unconditional: production emits it for module and tool functions, the only kinds
  this emitter lowers;
- a region's name used as a value (handed to a `Region` parameter, bound to a `Region` let) is
  a fresh `I64` local assigned `0` per use, production's inert handle (`materialize_region_handle`
  on the operand path, `Assign dst 0` into a destination).

Refused: a `slot_new` with other than one type argument naming a declared cap type, or with
arguments (the type checker's T191/T192/T074 come first); a `slot_put` or `slot_take` carrying
type arguments (no intrinsic in production: the type checker's T062 comes first); a slot or
capability operand, or a destination, that is not a pointer-typed local; a region body holding
any statement but a let, an expression statement or an assignment (control flow is the type
checker's T068); a body ending in an expression statement (its value is the region's — a
destination routing this slice does not mirror); a limit that is not an integer local; and a
`grant` of a closure (SHP-7).

## The construct-slot rule (SR-032)

Production typed the parts of a construct on their own: an enum constructor's arguments, a tuple
literal's elements and an assigned value took no expected type, so an integer literal there kept
its `i64` default and a generic construct built the `i64` instance. The construct lays each part
out at its own width while every reader uses the slot's declared type, so the parts after a
narrow one were read at the wrong offsets. Production now types each part by its slot, and the
emitter mirrors it wherever it can see the slot:

- an enum payload is a slot. A bare integer literal takes the payload's integer type (`E::V(3,
  40)` with `V(i32, i64)` stores the `3` in 4 bytes); literal arithmetic is accepted only in an
  `i64` payload, as at every slot.
- a payload typed by a type parameter of a generic enum takes the instance's type argument when
  the instance's type node is in view: an annotated `let`, a return, a method argument, an
  argument of a non-generic function, or a tuple element under a visible tuple type
  (`let e: E<i32> = E::V(3, 8);` stores an `i32`).
  With no instance in view a literal there is refused; where production gives the construct no
  slot at all (an unannotated `let`, an expression statement), a literal keeps its `i64` default
  in both compilers.
- a tuple literal is typed by its slot's tuple type when the emitter can see it: an annotated
  `let`, a return, a method argument, an argument of a non-generic function, a record field, an
  array element, or an enclosing tuple's element. Each element is then written to its element
  type as above, so an array literal element takes its element type
  (`let t: ([i32; 2], i64) = ([1, 2], 3);`). Where
  production gives the tuple no slot (an unannotated `let`, an expression statement, an
  unannotated array's element), its elements type themselves in both compilers, except an
  enum construct with a literal in a type-parameter payload: the emitter lowers that element
  without a slot, which it treats as hidden, so it refuses it.
- a call to a monomorphized generic function (`TcSig.inst`) lowers a tuple, array, record or
  enum argument against a hidden slot (`cv_call_arg_tid`), so a literal part of it is refused.
  Production types such an argument by the instance's parameter as well, but by two paths: it
  is pinned while inferred when a turbofish or the arguments before it bind the type
  parameters its declared type mentions, and narrowed after inference otherwise, where a part
  that retyping cannot narrow (an enum construct already built at another instance) is
  rejected. Which path an argument takes depends on argument order, which this lowering does
  not model. A scalar or `str` argument keeps its slot: production narrows a literal there
  once the instance is known.
- a bare variant that several enums declare (`B(x)` with `B` in `E1` and `E2`) takes, in
  production, the enum of the slot it is written to. Where the emitter has that slot in view
  it does the same; where it does not (an argument of a generic instance, a record field), its
  ST-1 fallback took the first declaring enum, and now refuses. A bare match pattern
  (`B(v) =>`) is refused the same way: production names the scrutinee's variant, and the
  emitter's pattern lookup took the first declaring enum's tag.

`SHP0B_FENCES` pins the rule by name (see its SR-032 rows), and `ag6_6_narrow_variant_size_corpus`
and `ag6_7_unresolved_generic_enum_contexts_fail_closed` pin the generic-enum contexts: byte-equal
where the instance is in view, refused where it is not.

## Encoding contract

The emitter uses the same position-sensitive integer encodings as the Rust authority:

| Position | Encoding |
| --- | --- |
| section sizes, counts, indices, vector lengths, and name lengths | ULEB128 |
| `local.*`, `call`, `br`, and `br_if` operands | ULEB128 |
| memory alignment and offset operands | ULEB128 |
| `i32.const` and `i64.const` operands | SLEB128 |
| value types and opcodes | fixed single bytes |

The signed boundary cases 63, 64, 127, 128, and -1 remain pinned. All opcode mappings are derived
from oracle output and covered by byte comparison; an unrecognized mapping poisons emission.

Control-flow emission mirrors the Rust block walker, including loop back-edge fuel, branch-merge
selection, dispatch exits, unreachable tails, and typed return defaults. Memory lowering preserves
typed loads and stores, bounds checks, bump allocation, narrow-index wrapping, arrays, records,
and string data. Calls materialize arguments in order and use the callee's index in the caller's
ring.

## Evidence map

The W0-W5 names remain stable test identifiers, not implementation phases:

| Identifier | Permanent evidence |
| --- | --- |
| W0 | pinned oracle modules, strict comparison diagnostics, and totality over the corpus |
| W1 | scalar bodies, constants, arithmetic, mangling, and signed-LEB boundaries |
| W2 | branches, loops, matches, traps, and control-flow joins |
| W3 | loads, stores, allocation, arrays, records, and static data |
| W4 | calls, recursion, multiple functions, actors, and a stdlib ABI module |
| W5 | execution through the production runtime plus determinism and fuel census |

The accompanying `X-W*` labels identify permanent fences:

- `X-W2`: position-specific ULEB/SLEB and oracle-derived opcode mappings;
- `X-W3`: section contents are assembled before their encoded headers;
- `X-W4`: strict hexadecimal decoding and `!!` poison propagation;
- `X-W5`: self-hosted emission stays below half of the configured fuel budget;
- `X-W6`: byte mismatches report the first offset, local hex windows, and best-effort WAT;
- `X-W7`: this harness's final Wasm evidence is restricted to a single inner-ring module; two-ring
  modules are compared by `pipeline_differential.rs` and the never-diverge gate (SHP-2b);
- `X-W8`: independent runs produce identical bytes.

`crates/sigil-runtime/tests/air_differential.rs` owns these cases. The preservation manifest in
`tests/support/air_case_manifest.rs` pins the required checks so test repacking cannot silently
remove evidence.

## Execution boundary

The W5 corpus compiles tool-shaped programs through both emitters, requires byte equality, and
executes each module with `execute_ephemeral`. It covers arithmetic, loops, branches, calls,
matches, arrays, records, recursion, mutation, and nested loops.

Byte equality is the primary correctness criterion. Runtime execution is an additional end-to-end
check that the identical artifact is accepted and behaves as expected. Two-ring programs are
compared byte for byte, both modules, and stateful actor forms remain explicit poison as specified
by [sh-air.md](sh-air.md).

## Required verification

Changes to self-hosted Wasm emission must keep these suites green:

```text
cargo test -p sigil-runtime --test air_differential
cargo test -p sigil-runtime --test pipeline_differential
cargo test -p sigil-runtime --test selfhost_backend_parity
cargo test -p sigil-runtime --test preserve_pins
cargo test -p sigil-runtime --test claims_ledger
cargo test -p sigil-runtime --test selfhost_self_census
```

Pinned module bytes, certified source digests, and corpus floors may move only with a deliberate
compiler change and the corresponding evidence update.
