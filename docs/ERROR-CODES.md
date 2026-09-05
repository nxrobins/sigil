# Sigil Diagnostic Codes

This is the canonical reference for every diagnostic code emitted by the Sigil
compiler. Each code is a stable identifier — once published, codes are never
renamed or repurposed (only deprecated). Agent-driven tooling can act on these
codes mechanically; the human-readable `title` and `hint` come from the central
registry at [`crates/sigil-compiler/src/diagnostics/registry.rs`](../crates/sigil-compiler/src/diagnostics/registry.rs).

## Code namespace

| Prefix | Category | Range |
|--------|----------|-------|
| `L` | Lexer | L001–L099 |
| `P` | Parser | P001–P099 |
| `N` | Name resolution | N001–N099 |
| `T` | Type checking (incl. monomorphization) | T001–T299 |
| `O` | Ownership / borrow | O001–O099 |
| `E` | Effect / taint | E001–E099 |
| `R` | Ring / structural capability / runtime | R001–R899 |
| `C` | Z3 capability proofs | C001–C099 |
| `F` | FFI / foreign types | F001–F099 |
| `S` | Source-limit / forge gates | S001–S099 |
| `Y` | Codegen (Wasm emit) — reserved | Y001–Y099 |
| `I` | Internal compiler error | I001–I099 |

**Range policy**: 001–799 are compiler-emitted; 800–899 are reserved for
runtime feedback re-emitted as compile-style diagnostics; 900–999 are unstable
codes (tagged `(unstable)` in JSON and may be renamed before 1.0).

**JSON wire format**: see [`crates/sigil-compiler/src/diagnostics/json.rs`](../crates/sigil-compiler/src/diagnostics/json.rs)
for the schema. Every diagnostic carries `severity`, `code`, `title`,
`message`, `hint`, `doc_url`, and an optional `location { file, span, line, column }`.
`doc_url` uses the scheme `sigil://errors/<code>` so tooling can substitute a
real base URL later without a schema bump.

---

## Lexer (L)

### L001 — Invalid integer literal

Integer literals must fit in `i64`. Check for typos, oversized values, or accidental non-digit characters.

### L002 — Invalid float literal

Float literals must parse as `f64`. Use the form `1.5` or `1.5e3`; check for stray characters.

### L003 — Unterminated string literal

String literal opened with `"` but never closed. Add the closing `"` (escape inner quotes as `\"`).

### L004 — Unexpected character

This character has no meaning at this position. Remove it, or if it was meant to be part of a string, wrap the surrounding text in quotes.

---

## Parser (P)

### P001 — Expected token

The parser expected a specific token at this position. The message indicates what was expected; insert or correct the token. (This code covers all generic `expect_<token>()` helper failures.)

### P002 — Expected `module` declaration

Sigil source files start with `module <name>;`. Add the module declaration at the top of the file.

### P003 — Unknown ring annotation

`#[ring(...)]` accepts only `inner` or `outer`. Choose one of the two values.

### P004 — Expected `}` to close module body

The module body opened with `{` must be closed with `}`. Add the missing brace, or check for an unbalanced item declaration above.

### P005 — Expected `;` or `{` after module name

Use `module name;` for a top-level module, or `module name { ... }` for a scoped module.

### P006 — Expected item declaration

Inside a module body, declare items with `fn`, `actor`, `record`, `enum`, `cap type`, `effect`, `const`, `use`, `impl`, or `extern`.

### P007 — Expected ABI string after `extern`

Write `extern "C" fn ...;` — the ABI string identifies the calling convention.

### P008 — Expected `fn` after extern ABI

After the ABI string, the next token must be `fn` to declare an extern function.

### P009 — Duplicate `state` block in actor

An actor may have at most one `state { ... }` block. Merge the fields into a single block.

### P010 — Duplicate `init` block in actor

An actor may have at most one `init(...) { ... }` block. Merge the bodies, or move logic to a helper handler.

### P011 — Expected `state`, `init`, or `on` inside actor body

Actor bodies contain only `state { ... }`, `init(...) { ... }`, and `on Message(...) { ... }` items.

### P012 — Expected `fn` inside `impl` block

`impl <Type> { ... }` blocks contain only function definitions.

### P013 — Expected `,`, `;`, or `}` after field declaration

Field declarations are separated by `,` and the block is closed with `}`. Check for a missing comma.

### P014 — Expected literal value

This position expects a literal: integer, float, boolean (`true`/`false`), or string.

### P015 — Expected statement

Block bodies contain `let`, assignment, expression, `if`, `match`, `while`, `for`, or `return` statements.

### P017 — Expected `in` after `for` loop variable

`for` syntax is `for x in <iterable> { ... }` — add the missing `in`.

### P018 — Expected `,`, `;`, or `}` after match arm

`match` arms are separated by `,` and the block is closed with `}`. Check for a missing comma.

### P019 — Expected pattern

`match` patterns are: a literal (`1`, `"x"`, `true`), a binding (`x`), `_`, or an enum variant (`Some(x)`).

### P020 — Expected expression

This position expects an expression. Check for a missing operand or a stray operator.

### P021 — Unknown taint label

Taint labels are `@Public`, `@Internal`, or `@Secret`. Check the spelling and capitalization.

### P022 — Expected `Stop` or `Restart(n)` after `supervision:`

`supervision:` accepts `Stop` (terminate on failure) or `Restart(<n>)` (restart up to n times).

### P023 — Expected `actor` keyword

An `entry` modifier must precede an `actor` declaration: `entry actor Main { ... }`.

---

## Name resolution (N)

### N001 — Duplicate module

Two `module` declarations share a name. Rename one or merge their contents.

### N002 — Duplicate item definition

Two top-level items in the module share a name. Rename one or remove the duplicate.

### N003 — Duplicate actor handler

Two `on Message(...)` handlers within the same actor share a message name. Rename one or merge their bodies.

### N004 — Duplicate actor state field

Two fields within the actor's `state { ... }` block share a name. Rename one or remove the duplicate.

### N005 — Duplicate parameter name

Two parameters within the same function, init, or handler share a name. Rename one.

### N006 — Parameter shadows actor state field

An init or handler parameter has the same name as an actor state field. Rename the parameter to keep state references unambiguous.

---

## Type checking (T)

### T001 — Taint downgrade without declassification

Use `declassify(value, cap)` with a consumed Declassify capability, or accept a higher-or-equal taint level on the binding/return.

### T040 — Constant value type mismatch

The constant's value type does not match its declared annotation. Either change the annotation or cast the value to the expected type.

### T041 — Let binding type mismatch

The let binding's value does not match its declared type annotation. Drop the annotation to let the type be inferred, or fix one side to match.

### T042 — Cannot assign to immutable variable

Declare the binding with `let mut name = ...` to allow reassignment.

### T043 — Reassignment forbidden — value owns a linear or scope-tied resource

Reassignment via `let mut x: T = ...; x = ...;` is permitted for primitives, `ActorRef`, arrays, and any user-defined record / enum whose fields are themselves reassignable. It is rejected when the value transitively owns a capability (which would break linear-move discipline) or a borrow (which would leave the borrow tracker holding a dangling source). For cap-bearing values, consume the cap rather than store it. For borrow-bearing values, drop the borrow before reassigning. The message names which category fired so the fix is unambiguous.

### T044 — Missing return value

The function declares a non-unit return type but no `return <value>` statement reaches the end. Add a return value on every control-flow path.

### T045 — Assignment value type mismatch

The assigned value's type does not match the variable's declared type. Convert the value or change the variable type.

### T046 — Unsupported let binding annotation

Let bindings only accept built-in primitive type annotations today. Drop the annotation to let inference run, or use a built-in type.

### T047 — `return` requires a value

The function returns a non-unit type but this `return` has no value. Add the value: `return <expr>;`.

### T048 — Unit-returning function cannot return a value

This function returns `()` (no return type or `-> ()`). Change to `return;` or remove the return.

### T049 — Return value type mismatch

The returned value's type does not match the function's declared return type.

### T050 — `if` condition must be `bool`

`if` requires a boolean condition. Compare your value (e.g., `x == 0`) instead of using it directly.

### T051 — `while` condition must be `bool`

`while` requires a boolean condition. Compare your value (e.g., `i < n`) instead of using it directly.

### T052 — `for-in` requires an array

`for x in ...` only iterates arrays today. Materialize a `[...]` literal or pass an array variable.

### T053 — `match` arm guard must be `bool`

Guards (`if <expr>`) must evaluate to `bool`. Compare your value rather than using it directly.

### T054 — Numeric operator requires matching operands

Arithmetic operators (`+`, `-`, `*`, `/`) require both operands to be the same numeric type (`i32`, `u32`, `i64`, `u64`, or `f64`). Bit operators (`<<`, `>>`, `&`, `|`) additionally require integer operands — floats and bools are rejected. Cast one side or change the literal type to match.

### T055 — Comparison operator requires comparable operands

Comparison operators (`<`, `<=`, etc.) require operands of compatible types. Cast or normalize the types before comparing.

### T060 — Undefined local

This name is not in scope. Declare it with `let`, add it as a parameter, or check the spelling.

### T062 — Undefined function

No function with this name is in scope. Declare it, import it via `use`, or check the spelling.

### T064 — Unknown actor

No actor with this name has been declared. Add an `actor X { ... }` definition or check the spelling.

### T065 — Actor has no such handler

The actor does not declare a handler for this message. Add `on Message(...) { ... }` to the actor body, or check the message name.

### T066 — Unknown type

No type with this name is in scope. Declare a `record`, `enum`, or `cap type`, import via `use`, or check the spelling.

### T067 — Unknown actor in `ActorRef<T>`

The named actor does not exist. Declare `actor X { ... }` with that name, or correct the spelling.

### T069 — Unknown effect in `handle` block

Declare the effect with `effect X;` somewhere in scope, or check the spelling. `Unsafe`, `FFI`, `NetIO`, `FsIO`, `Alloc` are well-known names.

### T070 — Function call arity mismatch

Pass the exact number of arguments the function declares.

### T071 — Function argument type mismatch

Each call argument must match the declared parameter type. Convert or cast the offending argument.

### T072 — Enum variant constructed with wrong arity

Provide exactly the number of fields declared by the enum variant.

### T073 — Function returning `()` used as a value

This function does not return a value. Call it as a statement, or change the function to return a value.

### T074 — Intrinsic call arity mismatch

`alloc` takes 1 argument; `load8` takes 1; `store8` takes 2. Check your call site.

### T075 — Intrinsic argument type mismatch

Intrinsic arguments must be integer types: `alloc(size: i64)`, `load8(ptr: i64)`, `store8(ptr: i64, val: i64)`.

### T080 — Match arm after catch-all is unreachable

The `_` arm matches everything; arms after it are dead. Move them above the `_` arm or remove them.

### T081 — Match pattern type does not match scrutinee

Each pattern must match the type of the matched expression. Use a literal of the same type or restructure the match.

### T082 — Duplicate match pattern

The same literal appears as the head of two arms — only the first can match. Remove the duplicate.

### T083 — Duplicate `_` match arm

A `match` may have at most one catch-all `_` arm. Remove the duplicate.

### T084 — Variant pattern against non-enum scrutinee

Enum variant patterns (`Some(x)`, `Err(e)`) only match enum-typed scrutinees. Match a different shape, or change the scrutinee.

### T085 — Enum variant pattern arity mismatch

The pattern must bind exactly as many fields as the enum variant declares.

### T086 — Enum has no such variant

The named variant is not declared on this enum. Add it to the enum definition, or use an existing variant name.

### T087 — Non-exhaustive match (missing variants)

Add an arm for every missing enum variant, or add a `_` catch-all.

### T088 — Non-exhaustive match (add `_` arm)

Add `_ => { ... }` as the final arm to cover remaining cases.

### T089 — Cannot infer type of empty array literal

Annotate the binding (e.g., `let xs: [i64] = [];`) so the element type is known.

### T090 — Entry actor must be named `Main`

An `entry actor` must be declared as `entry actor Main { ... }` — rename the actor or move `entry` to a different one.

### T091 — Multiple entry actors

Only one actor across the program may carry the `entry` keyword. Drop `entry` from all but one.

### T092 — Actor capability state must be in `init`

Capability state fields cannot be implicitly created — they must be passed via an `init(<name>: <CapType>)` parameter.

### T093 — `ask` timeout must be `i64`

`ask(msg, timeout: <i64>)` — the timeout is a number of milliseconds (i64).

### T094 — Spawn init argument arity mismatch

Pass exactly the init arguments declared by the spawned actor's `init` block.

### T095 — Spawn init argument type mismatch

Each spawn argument must match the declared `init` parameter type.

### T096 — Spawn supports cap-typed init args only

Today `spawn::<Actor>(...)` accepts only capability-typed init arguments. Restructure the actor to receive non-cap state via messages.

### T097 — Message target must be `ActorRef<T>`

`x.send(...)` and `x.ask(...)` require `x: ActorRef<T>`. Pass an actor reference, not a primitive.

### T098 — `ask` requires handler to return a value

`ask` is request/response — the handler must declare `-> <T>`. Use `send` for fire-and-forget, or add a return type.

### T099 — `ask` return type must be `Send`

Return types crossing the actor boundary must implement `Send`. Use bool, i64, ActorRef<T>, or a cap type.

### T100 — `.restrict()` requires a capability

`x.restrict(<authority>)` requires `x` to be a capability. Pass an owned cap type rather than a primitive.

### T101 — Unknown authority on `.restrict()`

The authority name does not match any declared by `cap type X { authority1, authority2, ... }`. Add the authority or fix the spelling.

### T102 — `.split()` requires a capability

`x.split(<amount>)` requires `x` to be a capability. Pass a cap-typed value (typically `Fuel`).

### T103 — `.split()` amount must be `i64`

The split amount is `i64`. Use a literal or cast.

### T104 — `grant` requires `&cap T`, not a slice

`grant(&cap_value, ...)` — pass a single borrowed capability, not a slice or array.

### T105 — `grant` requires `&cap T`

Borrow a capability with `&cap_value` (or `&self.cap`) for the first argument of `grant`.

### T106 — `grant` closure parameter type mismatch

The closure's parameter type must equal `&CapType` of the borrowed capability.

### T107 — `grant` closure parameter arity

The `grant` closure takes exactly one parameter — the cap reference.

### T108 — `grant` body must be a closure

Pass a closure as the second argument: `grant(&cap, fn(c: &CapType) -> T { ... })`.

### T109 — Cross-ring return error must be `ErrorCode`

Functions returning `Result` across ring boundaries must use `ErrorCode` (a `u32`). Use rich error types only within a single ring.

### T110 — `declassify` requires `Cap<Declassify>`

Pass an owned `Declassify` capability as the second argument: `declassify(value, declass_cap)`.

### T111 — `region` size limit must be numeric

Pass an integer literal or expression as the size argument: `region buf(1024) { ... }`.

### T112 — `ask` return type currently restricted

`ask` return values are limited to bool, i64, ActorRef<T>, and cap types in the current runtime ABI.

### T113 — Message constructor required

`send` and `ask` expect a constructor call like `MessageName(arg1, arg2)`, not a free expression.

### T114 — Message constructor must be a simple call

Use `Name(...)` — no chained calls, methods, or paths in the message constructor position.

### T115 — Send/ask handler arity mismatch

Pass exactly the number of arguments the handler's `on Message(...)` signature declares.

### T116 — Send/ask handler argument type mismatch

Each message argument must match the handler's declared parameter type.

### T117 — Send/ask argument is not `Send`

Message arguments crossing the actor boundary must implement `Send`. Use bool, i64, ActorRef<T>, or a cap type.

### T118 — Send/ask argument type currently restricted

Today the runtime ABI accepts bool, i64, ActorRef<T>, and cap-typed message arguments only.

### T120 — Type has no such field

The named field is not declared on the record. Check the spelling or add the field to the `record` definition.

### T121 — Type is not a record

Field access is only valid on `record` types. Use a different operation appropriate for this type.

### T122 — Cannot access field on non-record value

Field access (`.x`) is only valid on values of `record` types. Restructure to project from a record.

### T130 — Cannot call method on this type

The receiver type does not support method calls in this position. Use a free function or restructure the expression.

### T131 — Method call arity mismatch

Pass exactly the number of arguments the method declares.

### T132 — No such method on type

The receiver type has no method with this name. Check the spelling, or use a free function.

### T133 — Cannot borrow primitive type

Only heap-allocated types (records, arrays, capabilities) can be borrowed. Pass primitives by value.

### T140 — Array element type mismatch

All elements of an array literal must share the same type. Cast or normalize the offending element.

### T141 — Cannot index non-array value

Indexing (`arr[i]`) requires an array type. Use a different operation appropriate for this type.

### T142 — Array index must be integer

Array indices must be integer types (`i32`/`u32`/`i64`/`u64`). Cast or change the index expression.

### T150 — Could not infer type parameter

Use turbofish syntax to specify the type parameter explicitly: `f::<i64>(x)`.

### T151 — Monomorphization depth exceeded

A generic function instantiates itself (or its callees) too deeply. Restructure to break the recursion or simplify the generic chain.

### T160 — Extern function must declare `FFI` effect

Add `! { FFI, Unsafe }` to the extern signature: `extern "C" fn x() -> i32 ! { FFI, Unsafe };`.

### T161 — Extern function must declare `Unsafe` effect

Add `Unsafe` to the extern's effect row: `extern "C" fn x() -> i32 ! { FFI, Unsafe };`.

### T170 — Supervision `max_restarts` out of range

`supervision: Restart(n)` accepts n in 1..=255. Choose a value within range.

### T171 — Supervision `max_restarts` must be integer literal

Pass a literal: `supervision: Restart(3)`. Variables and expressions are not supported here yet.

### T172 — Supervision `max_restarts` must be compile-time literal

The `max_restarts` argument must be a compile-time integer literal so the supervision strategy is known statically.

### T180 — `?` error type mismatch

The `?` operator's error type must match the enclosing function's `Result` error type. Convert via `.map_err(...)` or change one side.

### T181 — `?` requires `Result` return type

`?` only works inside functions returning `Result<_, E>`. Change the function's return type or restructure to handle the error inline.

### T182 — `?` requires a `Result` value

`?` can only be applied to `Result<T, E>` values. Wrap the value or restructure the call.

### T190 — Range pattern: lower bound greater than upper bound

Inclusive range patterns (`lo..=hi`) require `lo <= hi`. A range like `57..=48` is unsatisfiable — the arm can never fire — so the type-checker rejects it rather than leaving a dead arm at runtime. Swap the bounds to `48..=57`.

### T191 — `Slot<T>` requires T to be a capability type

`Slot<T>` is the built-in linear container designed for capability accumulation. Instantiate with a `cap type` (e.g., `Slot<Fuel>`), not a primitive or record. Using non-cap T would bypass the Z3 authority propagation that makes Slot safe.

### T192 — `slot_new` requires a type argument

Slot's element type can't be inferred from the empty argument list. Specify it explicitly at the call site: `slot_new::<Fuel>()`.

### T193 — Type name `Slot` is reserved

`Slot` names the built-in linear container; user records, enums, and cap types cannot reuse the name. Rename your type (e.g., `SlotState`, `MySlot`) — a user `enum Slot<T>` would otherwise shadow the built-in and re-introduce the aggregate-smuggling vector T184 closes for user enums.

<!-- T194 (multi-put-to-same-slot rejection) was retired in Wall 1 Step 4.
     The Z3 source rule now folds every SlotPut's authority into a
     conservative meet at each SlotTake, so multi-branch puts are sound
     without a structural rejection. -->

### T195 — Deadline-typed capability subtype mismatch

The source capability's declared deadline is earlier than the target site requires. Wall 2 Stage 1 added covariant subtyping for parametric (deadline-typed) caps: `Approval(D_a) <: Approval(D_b)` iff `D_a >= D_b`. A longer-lived cap is acceptable wherever a shorter-lived one is required, but the reverse fails. T195 also fires when a parametric form meets a non-parametric form at the same name — those are distinct types. Widen the target's expected deadline to be ≤ the source's, or narrow the source via `restrict_deadline(...)` once that primitive ships in Stage 2/3 of the deadline-typed cap rollout.

### T196 — Parametric capability requires a deadline literal at this position

The capability type was declared as parametric (`cap type <Name>(<param>: i64) {}`); every reference must supply a bound `i64` deadline literal — e.g., `Approval(2030_06_01)`. Add the literal at this site, or, if the cap should be non-parametric, change the declaration to `cap type <Name> {}`.

### T197 — Non-parametric capability cannot accept a deadline literal

The capability type was declared as non-parametric (`cap type <Name> {}`); references must not supply a `(...)` argument. Remove the literal at this site, or, if the cap should be parametric, change the declaration to `cap type <Name>(<param>: i64) {}` (Stage 1 supports a single `i64` parameter).

### T198 — Invalid parametric capability declaration

Parametric capability types are declared as `cap type <Name>(<param>: i64) {}`. Empty parentheses, missing parameter type, and non-`i64` parameter types are not supported in Stage 1. Use the canonical form, or omit the parentheses entirely for a non-parametric cap.

### T199 — Parametric capability literal is past the build-time deadline

The cap-type literal declares a deadline earlier than the value supplied via `--build-deadline`, OR a `restrict_deadline(D')` argument narrows past the build deadline. The compiler refuses to build a program whose caps would be stale at compile time. Either widen the literal to a value `>=` the build deadline, raise the build deadline (or drop the flag), or remove the narrowing if it's intentional staleness for testing. Wall 2 Stages 2-3.

### T200 — `restrict_deadline` cannot extend, run on non-parametric, or narrow a multi-parameter cap

`cap.restrict_deadline(D')` produces a cap with `min(D_orig, D')` — it can only narrow a SINGLE-parameter cap. Three variants fire T200: (a) extension (`D' > D_orig`), (b) call on a non-parametric cap (no deadline to narrow), (c) call on a multi-parameter cap (Wall 3 Stage 1 doesn't support multi-parameter narrowing — split into separate single-parameter cap types). Wall 2 Stage 2 + Wall 3 Stage 1.

### T201 — Parametric capability used with wrong number of values

`cap type Limited(deadline_ms: i64, max_uses: i64) {}` declares arity 2; usages must supply exactly 2 `i64` literals (e.g., `Limited(2030, 5)`). Arity mismatch (M != N, both > 0) fires T201. The arity-0 cases are still T196 (parametric used without values) and T197 (non-parametric used with values). Supply exactly the declared number of values at the usage site, matching the declared parameter order. Wall 3 Stage 1.

---

## Ownership / borrow (O)

### O001 — Use after move (or duplicate linear use)

A linear value (capability, message payload) cannot be used after it has been moved. Restructure to avoid the second use, or split the capability via `cap_split` first.

### O006 — Compatibility alias for T254 region escape

Retained for diagnostic-code compatibility; not emitted. Region escape is enforced as T254.

### O007 — Move while borrowed

Cannot move a value while a borrow (or active grant) is outstanding. Drop the borrow first, or restructure to avoid the move.

---

## Effect / taint (E)

### E001 — Undeclared effect required by callee

Add the missing effect to this function's `! { ... }` row, or wrap the call site in a `handle <Effect> { ... }` block if you have authority for it.

### E002 — `handle Unsafe` requires a `#[trusted]` module

Move this code into a `#[ring(outer)] #[trusted]` module, or remove the `handle Unsafe { ... }` block if it isn't actually needed.

### E003 — Inner-ring function must not declare an effect row

Remove the `! { ... }` clause from this inner-ring function — effect rows are only meaningful in outer-ring code.

---

## Ring / structural capability / runtime (R)

### R001 — Outer-ring code cannot own capabilities

Capabilities live in the inner ring. Pass a borrowed capability via `grant(&cap, fn(ref) -> ...)` instead of taking ownership in outer-ring code.

### R002 — Capability reference escapes its grant scope

A `&cap T` reference is only valid inside the `grant(...)` closure body. Return owned data, not the capability reference.

### R003 — Inner-ring code cannot call `extern` functions

Move the FFI call into a `#[ring(outer)] #[trusted]` module and expose it through a safe wrapper that the inner ring calls via grants.

### R004 — Direct cross-ring call requires a grant

Inner and outer rings can only interact via `grant(&cap, fn(ref) -> ...)`. Direct calls across the boundary are forbidden.

### R005 — Compatibility alias for T109 ring-error sanitization

Retained for diagnostic-code compatibility; not emitted. Cross-ring rich errors are rejected as
T109; use `ErrorCode` (`u32`).

### R010 — Non-capability spawn argument

`spawn::<Actor>(...)` requires capability-typed arguments. Pass a value declared with `cap type T` rather than a primitive or record.

### R011 — Non-capability fuel argument

The fuel argument to `spawn` must be a `Fuel`-typed capability. Pass an owned `Fuel` cap (often a state field) rather than a primitive.

### R012 — Non-cap source or destination at restrict/split

`cap_restrict` and `cap_split` must consume and produce capability-typed values. Check the AIR pipeline if you see this — it usually indicates an upstream type-check bug.

### R800–R807 — Runtime feedback (re-emitted as compile diagnostics)

These codes are emitted by the CLI when a runtime error is translated into the
diagnostic envelope (so the agent loop sees a uniform shape).

| Code | Title |
|------|-------|
| R800 | Runtime error (catch-all / CLI invocation error) |
| R801 | Fuel exhausted |
| R802 | Missing Wasm export |
| R803 | Tool trapped during execution |
| R804 | Tool module missing `tool_main` entry point |
| R806 | Capability table error |
| R807 | Wasm validation or instantiation error |
| R810 | Certificate file unreadable, not a regular file, or over 1 MB |
| R811 | Certificate JSON parse failure |
| R812 | Certificate schema version unsupported by gate (v3 only) |
| R813 | Source fingerprint mismatch |
| R814 | WASM inner-module fingerprint mismatch |
| R815 | WASM outer-module fingerprint mismatch or missing |
| R816 | Effect set mismatch between certificate and runtime |

---

## Z3 capability proofs (C)

### C001 — Capability forgery

Capabilities cannot be constructed from record literals. They must come from `init` parameters, `spawn` results, `cap_split`, or `cap_restrict`.

### C002 — Capability provenance violation

Z3 detected a capability variable that may have originated from an illegitimate source (forged record, unverified value). Trace the cap's source back to an init parameter, spawn result, or attenuation site.

### C003 — Capability authority escalation

A restricted capability (via `cap_restrict`) was passed where full authority is required. Pass the unrestricted capability, or restructure the callee to accept the restricted authority set.

### C004 — Capability verifier solver timeout

Z3 returned UNKNOWN — could neither prove nor refute the property within configured limits. Simplify the cap flow, or increase solver limits if you control the build.

### C005 — SMT query outside the decidable fragment (internal)

The runtime fragment guard rejected a solver query before it reached Z3 (quantifier, disallowed op/sort, uninterpreted function, off-width bitvector, mixed theories, or oversized formula). Every query is compiler-constructed, so this is a compiler bug — please report it. The program is conservatively rejected, never accepted unverified.

---

## FFI / foreign types (F)

_No F-codes are currently emitted. F001 (`Ptr<T>` outside extern context) is reserved but not wired — see the reservation in `crates/sigil-compiler/src/diagnostics/codes.rs`._

---

## Source-limit / forge gates (S)

### S001 — Source exceeds maximum byte size

Reduce the source size, split it into smaller modules, or invoke compilation through `compile_named_module` (no built-in size limit) instead of `compile_tool_with_limits`.

### S002 — Tool module missing `tool_main`

Add `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64` to the module. See `lang-ref.md` for the entry-point ABI.

### S003 — Source must not be empty

Provide source text — at minimum a `module <name>;` declaration.

---

## Internal compiler errors (I)

### I001 — Internal compiler invariant violation

This is a compiler bug: an internal representation violated a required invariant, such as AST/resolved-module correspondence or AIR control-flow integrity. Please file an issue with a minimal reproducer.

---

## Generating this file

This document is hand-maintained today. The registry test
[`registry_is_well_formed`](../crates/sigil-compiler/src/diagnostics/registry.rs)
guarantees every entry in the in-memory table has a non-empty title and hint
and a well-formed code. A future task will add a `cargo xtask docs:errors` job
that regenerates this file from the registry directly.
