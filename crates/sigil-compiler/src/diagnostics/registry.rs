//! Central registry of diagnostic codes, titles, and default fix recipes.
//!
//! Every entry in `CODES` ties a `DiagnosticCode` to a human-readable title
//! and a default `hint` that an LLM driver can act on. Per-call-site `hint`
//! overrides (via `Diagnostic::error_with_hint`) fall back to the registry
//! default when set to `None`.
//!
//! When a new diagnostic is added to the compiler, an entry MUST be added
//! here. The `registry_is_well_formed` test enforces basic invariants
//! (non-empty fields, no duplicates, code format `^[A-Z][0-9]{3}$`).

use super::codes::DiagnosticCode;

/// Coarse grouping for a code, used for ERROR-CODES.md generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Category {
    Lexer,
    Parser,
    NameResolution,
    TypeCheck,
    Ownership,
    Effect,
    Ring,
    Capability,
    Ffi,
    SourceLimit,
    /// Multi-file project / module-set diagnostics (M-prefix family).
    /// Wall 5 Step 1 onwards.
    ModuleSet,
    Codegen,
    Internal,
}

/// One row of the diagnostic catalog.
pub struct CodeEntry {
    pub code: DiagnosticCode,
    pub title: &'static str,
    pub default_hint: &'static str,
    pub category: Category,
}

macro_rules! define_catalog {
    (
        $(
            CodeEntry {
                code: $code:ident,
                title: $title:literal,
                default_hint: $default_hint:literal,
                category: $category:path,
            }
        ),* $(,)?
    ) => {
        pub mod generated_codes {
            use super::DiagnosticCode;

            $(
                #[doc = concat!("Diagnostic code `", stringify!($code), "`.")]
                pub const $code: DiagnosticCode = DiagnosticCode::new(stringify!($code));
            )*

            /// Every declared code in registry order.
            pub static ALL_CODES: &[DiagnosticCode] = &[$($code),*];
        }

        /// The full diagnostic catalog. Constants and entries are generated
        /// together so a code cannot exist on only one side of the API.
        pub static CODES: &[CodeEntry] = &[
            $(
                CodeEntry {
                    code: generated_codes::$code,
                    title: $title,
                    default_hint: $default_hint,
                    category: $category,
                }
            ),*
        ];
    };
}

define_catalog! {
    // ── Source-limit / forge gates ──
    CodeEntry {
        code: S001,
        title: "Source exceeds maximum byte size",
        default_hint: "Reduce the source size, split it into smaller modules, or invoke compilation through `compile_named_module` (no built-in size limit) instead of `compile_tool_with_limits`.",
        category: Category::SourceLimit,
    },
    CodeEntry {
        code: S002,
        title: "Tool module missing `tool_main`",
        default_hint: "Add `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64` to the module. See `lang-ref.md` for the entry-point ABI.",
        category: Category::SourceLimit,
    },
    CodeEntry {
        code: S003,
        title: "Source must not be empty",
        default_hint: "Provide source text — at minimum a `module <name>;` declaration.",
        category: Category::SourceLimit,
    },
    CodeEntry {
        code: S004,
        title: "Too many modules in compilation unit",
        default_hint: "A single compilation accepts at most 256 modules. Split the workload across multiple compiles, or consolidate small modules.",
        category: Category::SourceLimit,
    },
    CodeEntry {
        code: S005,
        title: "Source byte cap exceeded",
        default_hint: "Total source bytes across all modules must be at most 5 MB. Trim unused code, split into separate compilations, or factor large constants into out-of-band data.",
        category: Category::SourceLimit,
    },
    CodeEntry {
        code: S006,
        title: "Function count cap exceeded",
        default_hint: "A single compilation accepts at most 10,000 functions across all modules. Split modules or factor common logic.",
        category: Category::SourceLimit,
    },
    CodeEntry {
        code: S007,
        title: "Nesting depth cap exceeded (expression, block, or type)",
        default_hint: "An expression, statement block, or type expression nests deeper than the parser's recursion limit (128). This usually means machine-generated or adversarial input; refactor deeply nested constructs into intermediate `let` bindings. The cap bounds recursive descent so pathological input raises this diagnostic instead of overflowing the stack and aborting.",
        category: Category::SourceLimit,
    },
    // ── Parser ──
    CodeEntry {
        code: P001,
        title: "Expected token",
        default_hint: "The parser expected a specific token at this position. The message indicates what was expected; insert or correct the token.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P002,
        title: "Expected `module` declaration",
        default_hint: "Sigil source files start with `module <name>;`. Add the module declaration at the top of the file.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P003,
        title: "Unknown ring annotation",
        default_hint: "`#[ring(...)]` accepts only `inner` or `outer`. Choose one of the two values.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P004,
        title: "Expected `}` to close module body",
        default_hint: "The module body opened with `{` must be closed with `}`. Add the missing brace, or check for an unbalanced item declaration above.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P005,
        title: "Expected `;` or `{` after module name",
        default_hint: "Use `module name;` for a top-level module, or `module name { ... }` for a scoped module.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P006,
        title: "Expected item declaration",
        default_hint: "Inside a module body, declare items with `fn`, `actor`, `record`, `enum`, `cap type`, `effect`, `const`, `use`, `impl`, or `extern`.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P007,
        title: "Expected ABI string after `extern`",
        default_hint: "Write `extern \"C\" fn ...;` — the ABI string identifies the calling convention.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P008,
        title: "Expected `fn` after extern ABI",
        default_hint: "After the ABI string, the next token must be `fn` to declare an extern function.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P009,
        title: "Duplicate `state` block in actor",
        default_hint: "An actor may have at most one `state { ... }` block. Merge the fields into a single block.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P010,
        title: "Duplicate `init` block in actor",
        default_hint: "An actor may have at most one `init(...) { ... }` block. Merge the bodies, or move logic to a helper handler.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P011,
        title: "Expected `state`, `init`, or `on` inside actor body",
        default_hint: "Actor bodies contain only `state { ... }`, `init(...) { ... }`, and `on Message(...) { ... }` items.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P012,
        title: "Expected `fn` inside `impl` block",
        default_hint: "`impl <Type> { ... }` blocks contain only function definitions.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P013,
        title: "Expected `,`, `;`, or `}` after field declaration",
        default_hint: "Field declarations are separated by `,` and the block is closed with `}`. Check for a missing comma.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P014,
        title: "Expected literal value",
        default_hint: "This position expects a literal: integer, float, boolean (`true`/`false`), or string.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P015,
        title: "Expected statement",
        default_hint: "Block bodies contain `let`, assignment, expression, `if`, `match`, `while`, `for`, or `return` statements.",
        category: Category::Parser,
    },
    // P016 reserved — removed pending a firing path; see codes.rs (PR-E1 made
    // `else` optional, so "expected else" no longer fires).
    CodeEntry {
        code: P017,
        title: "Expected `in` after `for` loop variable",
        default_hint: "`for` syntax is `for x in <iterable> { ... }` — add the missing `in`.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P018,
        title: "Expected `,`, `;`, or `}` after match arm",
        default_hint: "`match` arms are separated by `,` and the block is closed with `}`. Check for a missing comma.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P019,
        title: "Expected pattern",
        default_hint: "`match` patterns are: a literal (`1`, `\"x\"`, `true`), a binding (`x`), `_`, or an enum variant (`Some(x)`).",
        category: Category::Parser,
    },
    CodeEntry {
        code: P020,
        title: "Expected expression",
        default_hint: "This position expects an expression. Check for a missing operand or a stray operator.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P021,
        title: "Unknown taint label",
        default_hint: "Taint labels are `@Public`, `@Internal`, or `@Secret`. Check the spelling and capitalization.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P022,
        title: "Expected `Stop` or `Restart(n)` after `supervision:`",
        default_hint: "`supervision:` accepts `Stop` (terminate on failure) or `Restart(<n>)` (restart up to n times).",
        category: Category::Parser,
    },
    CodeEntry {
        code: P023,
        title: "Expected `actor` keyword",
        default_hint: "An `entry` modifier must precede an `actor` declaration: `entry actor Main { ... }`.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P024,
        title: "`@in` must name a `Region` parameter",
        default_hint: "`@in r` declares the region a value lives in; `r` must be a `Region` parameter of the same function, e.g. `fn f(r: Region, v: Vec<T> @in r)`.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P025,
        title: "`where region(...)` must name `Region` parameters",
        default_hint: "`where region(a): region(b)` declares that region `a` outlives region `b`; both must be `Region` parameters of the same function, e.g. `fn f(a: Region, b: Region, ...) where region(a): region(b)`.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P026,
        title: "Reserved keyword used as a name",
        default_hint: "This word is a reserved keyword and cannot be used as an identifier (a function, parameter, type, or variable name). Rename it — e.g. `handle` → `handler`, `spawn` → `spawn_task`.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P027,
        title: "Malformed higher-kinded type-parameter kind",
        default_hint: "A higher-kinded type parameter is written `<F: * -> *>` (one argument) or `<F: * -> * -> *>` (two). The kind must be `*` separated by `->`, must have at least one `->` (a bare `*` is not higher-kinded), and may have at most two `->`. Bounds come after, e.g. `<F: * -> * + Functor>`.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P028,
        title: "Malformed state-kinded type-parameter binder",
        default_hint: "Typestate: a state-kinded type parameter is written `<@S>` — a bare `@`-prefixed name with NO `:` bound or kind annotation. Remove the `: …` after `@S` (state markers are declared in a `state Name { … }` item, not as bounds), or drop the `@` if you meant an ordinary type parameter.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P029,
        title: "Inclusive range `..=` in a `for` header",
        default_hint: "Range-for: `for v in a..=b` is not supported — use an exclusive end (`for v in a..b`). One canonical loop form keeps the compile-time bounds fact (`v < end`) exactly the loop condition, with no off-by-one variant to mis-derive.",
        category: Category::Parser,
    },
    CodeEntry {
        code: P030,
        title: "`mut` on a non-state field",
        default_hint: "The `mut` marker is only valid on an actor `state {}` field. Record fields are immutable-by-shape: remove the `mut`. (Actor state mutability is opt-in via `mut` inside a `state {}` block.)",
        category: Category::Parser,
    },
    CodeEntry {
        code: P031,
        title: "Effect row after a `Fn`-typed return binds to the declaration",
        default_hint: "In `fn f() -> Fn(T) -> U ! { E } { … }` the trailing `! { E }` is the DECLARATION's effect row (the pre-existing meaning), not the returned Fn type's latent row. To attach the row to the type, parenthesize it: `-> (Fn(T) -> U ! { E })`. This is a warning, not an error — the parse proceeds with the declaration binding.",
        category: Category::Parser,
    },
    // ── Lexer ──
    CodeEntry {
        code: L001,
        title: "Invalid integer literal",
        default_hint: "Integer literals must fit in `i64`. Check for typos, oversized values, or accidental non-digit characters.",
        category: Category::Lexer,
    },
    CodeEntry {
        code: L002,
        title: "Invalid float literal",
        default_hint: "Float literals must parse as `f64`. Use the form `1.5` or `1.5e3`; check for stray characters.",
        category: Category::Lexer,
    },
    CodeEntry {
        code: L003,
        title: "Unterminated string literal",
        default_hint: "String literal opened with `\"` but never closed. Add the closing `\"` (escape inner quotes as `\\\"`).",
        category: Category::Lexer,
    },
    CodeEntry {
        code: L004,
        title: "Unexpected character",
        default_hint: "This character has no meaning at this position. Remove it, or if it was meant to be part of a string, wrap the surrounding text in quotes.",
        category: Category::Lexer,
    },
    CodeEntry {
        code: L010,
        title: "Source file is not valid UTF-8",
        default_hint: "SIGIL source files must be valid UTF-8. The compiler validates each input file at ingest before parsing begins. Common causes: a file saved in a legacy encoding (Latin-1, Windows-1252), a binary file mistakenly passed as source, or a truncated multi-byte sequence. Save the file as UTF-8 and retry.",
        category: Category::Lexer,
    },
    // ── Name resolution ──
    CodeEntry {
        code: N001,
        title: "Duplicate module",
        default_hint: "Two `module` declarations share a name. Rename one or merge their contents.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N002,
        title: "Duplicate item definition",
        default_hint: "Two top-level items in the module share a name. Rename one or remove the duplicate.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N003,
        title: "Duplicate actor handler",
        default_hint: "Two `on Message(...)` handlers within the same actor share a message name. Rename one or merge their bodies.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N004,
        title: "Duplicate actor state field",
        default_hint: "Two fields within the actor's `state { ... }` block share a name. Rename one or remove the duplicate.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N005,
        title: "Duplicate parameter name",
        default_hint: "Two parameters within the same function, init, or handler share a name. Rename one.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N006,
        title: "Binding shadows actor state field",
        default_hint: "A parameter or `let` binding has the same name as an actor state field. Rename it to keep state references unambiguous (a bare name always denotes the state field).",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N007,
        title: "Unresolved `use` path",
        default_hint: "The module referenced by `use sigil::<m>;` is not present in this compilation. Either include the missing module's source in the same compilation, or check the spelling of the module name.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N008,
        title: "Ambiguous symbol from multiple `use` aliases",
        default_hint: "The same function name is reachable via two different `use` aliases. Disambiguate by qualifying the call site (`module::fn`) or by removing one of the conflicting `use` declarations.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N009,
        title: "Cyclic module dependency",
        default_hint: "Module A's `use` chain reaches back to itself. Break the cycle by extracting shared declarations into a third module, or by inlining one side.",
        category: Category::NameResolution,
    },
    // N010 reserved for partial-success multi-module compilation
    // (see codes.rs). Today's pipeline is fail-fast at every pass
    // boundary, so the cascade scenario doesn't exist; entry omitted
    // until it does.
    CodeEntry {
        code: N011,
        title: "Invalid module name",
        default_hint: "Module names must match `^[a-z_][a-z0-9_]*$` (lowercase alphanumeric + underscores, starting with letter or underscore). Rename the module to fit the pattern.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N012,
        title: "Module-name case collision",
        default_hint: "Two modules differ only in case (e.g. `fs` and `Fs`). This is rejected because some platforms treat them as the same name. Rename one to be unambiguously distinct.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N013,
        title: "Duplicate record field",
        default_hint: "Two fields within the same `record` declaration share a name. Rename one or remove the duplicate.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N014,
        title: "Duplicate enum variant",
        default_hint: "Two variants within the same `enum` declaration share a name. Variant tags are assigned by source order, so a duplicate name silently collides on construction and pattern-matching (the second is unreachable). Rename one or remove the duplicate.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N015,
        title: "Duplicate capability authority",
        default_hint: "Two authorities within the same `cap type` declaration share a name. Authorities map to distinct bit positions in the authority mask, so a duplicate inflates the authority count (consuming the 32-authority budget) and corrupts `restrict`/mask accounting — the second occurrence is unreachable. Rename one or remove the duplicate.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N016,
        title: "Duplicate protocol state",
        default_hint: "Two states within the same `state` declaration share a name. Protocol states are a closed ordered set of markers, so a duplicate is dead. Rename one or remove the duplicate.",
        category: Category::NameResolution,
    },
    CodeEntry {
        code: N017,
        title: "Duplicate type parameter",
        default_hint: "A `fn`, `record`, or `enum` declares two type parameters with the same name (`<T, T>`). Positional substitution would silently collapse to one binding (the same reason `impl Foo<T, T>` is rejected with T229). Rename one — `<T, U>` if they are independent — or drop one if a single parameter suffices.",
        category: Category::NameResolution,
    },
    // ── Taint ──
    CodeEntry {
        code: T001,
        title: "Taint downgrade without declassification",
        default_hint: "Use `declassify(value, cap)` with a consumed Declassify capability, or accept a higher-or-equal taint level on the binding/return.",
        category: Category::Effect,
    },
    // ── Constant-time discipline (`@SecretCT`) — see docs/specs/secret-ct.md ──
    CodeEntry {
        code: T020,
        title: "Secret-dependent branch (CT001)",
        default_hint: "Replace the `if` on `@SecretCT` data with a branch-free `ct_select(cond, then_val, else_val)`. The spec rejects this because the branch's wall-clock timing leaks which arm was taken.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T021,
        title: "Secret-dependent loop (CT002)",
        default_hint: "`while` over a `@SecretCT` condition is rejected — the trip count is observable. Bound the loop by a `@Public` constant instead, and use branch-free body operations.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T022,
        title: "Secret-dependent iteration (CT003)",
        default_hint: "`for x in iter` over a `@SecretCT` iterable is rejected — the trip count leaks via wall-clock. Iterate over a `@Public` collection and lift each element to `@SecretCT` inside the body if needed.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T023,
        title: "Secret-dependent dispatch (CT004)",
        default_hint: "`match` on a `@SecretCT` scrutinee is rejected — the chosen arm is timing-observable. Use a branch-free `ct_select` chain on the scrutinee's bit pattern instead.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T024,
        title: "Secret-dependent array index (CT005)",
        default_hint: "Indexing by a `@SecretCT` value leaks the index through cache state. Iterate the full array under a `@Public` counter and `ct_select` the wanted element by bitwise mask.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T025,
        title: "Secret-dependent memory address (CT006)",
        default_hint: "`load8`/`store8` at a `@SecretCT` pointer is rejected — the access pattern is observable via cache state. Use a `@Public` base address and bitwise-mask the loaded data instead.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T026,
        title: "Variable-time division (CT007)",
        default_hint: "`/` and `%` on `@SecretCT` operands run in data-dependent time on most CPUs. Use a branch-free reduction (Barrett, Montgomery) over public moduli, or declassify the operand first if the result need not be CT.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T027,
        title: "`@SecretCT` value passed to extern function (CT010)",
        default_hint: "Sigil cannot verify the C side's timing properties. Declassify the value with `declassify_ct` (and then `declassify`) before the FFI call, or use a Sigil-side CT intrinsic instead.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T028,
        title: "`@SecretCT` payload across actor boundary (CT014)",
        default_hint: "Inter-actor CT analysis is out of scope (spec §9.3, §9.9). Declassify before `send`/`ask`, or keep `@SecretCT` data within the lexical scope of one actor handler.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T029,
        title: "Secret-dependent allocation size (CT015)",
        default_hint: "`alloc(n)` and `region(n)` with `n: @SecretCT` are rejected — allocator state and heap layout are observable. Size buffers from a `@Public` upper bound instead.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T030,
        title: "`@Internal`/`@Secret` → `@SecretCT` upcast forbidden (CT016)",
        default_hint: "`@SecretCT` values may only be constructed from declared `@SecretCT` parameters, `@SecretCT`-annotated literals, CT intrinsic returns, or `@Public` data (which carries no confidentiality to lose). Untrusted sources (FFI returns, declassified data) cannot be promoted.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T031,
        title: "`declassify` rejects `@SecretCT` input (CT017)",
        default_hint: "`declassify(value, cap)` lowers `@Secret → @Public`. To go from `@SecretCT` to `@Public`, use the two-step ladder: `let mid: T @Secret = declassify_ct(value, ct_cap); return declassify(mid, pub_cap);` — each step consumes its own linear capability.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T032,
        title: "`declassify_ct` input must be `@SecretCT`",
        default_hint: "`declassify_ct` is the CT-specific declassifier; it expects `@SecretCT` input and produces `@Secret`. For non-CT data, use plain `declassify(value, cap)`.",
        category: Category::Effect,
    },
    CodeEntry {
        code: T033,
        title: "Secret-dependent string content comparison",
        default_hint: "CT018: `==` / `!=` on `str` compares CONTENT with an early-exit byte loop, so BOTH its running time and the fuel it consumes reveal the length of the common prefix — two timing oracles over secret data. There is no constant-time `str` comparison to fall back on: `ct_eq` / `ct_select` / `ct_lt` are integer-only, so a CT compare has to be written by hand as a fixed-trip-count fold of `ct_eq` over `byte_at` with no early exit. The alternatives are: fold `ct_eq` yourself over a public trip count; use `bytes_eq` if a length-and-prefix leak is acceptable for this data; or step the value down with `declassify_ct` first if the secrecy is no longer required. Integer `==` on `@SecretCT` stays legal — it is a single instruction with nothing to time.",
        category: Category::Effect,
    },
    // ── Effect ──
    CodeEntry {
        code: E001,
        title: "Undeclared effect required by callee",
        default_hint: "Add the missing effect to this function's `! { ... }` row, or wrap the call site in a `handle <Effect> { ... }` block if you have authority for it.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E002,
        title: "`handle Unsafe` requires a `#[trusted]` module",
        default_hint: "Move this code into a `#[ring(outer)] #[trusted]` module, or remove the `handle Unsafe { ... }` block if it isn't actually needed.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E003,
        title: "Inner-ring function declares a privilege effect",
        default_hint: "Inner-ring functions cannot declare `Unsafe` or `FFI` in their effect row — those are outer-ring privileges. Two concrete fix paths: (1) move the function to a `#[ring(outer)] #[trusted]` module if it genuinely needs the privilege effects, or (2) drop just `Unsafe`/`FFI` from the effect row (other effects like `Alloc` or user-declared domain effects are fine to declare in inner ring).",
        category: Category::Effect,
    },
    CodeEntry {
        code: E004,
        title: "Effect-handler form not yet supported",
        default_hint: "`perform`, clause-form `handle { Op(x) => ... }`, and `resume` are being implemented in stages (EH0-EH5). This rung parses the syntax but does not type-check or lower it yet. Use the bare `handle <Effect> { ... }` form for now, or track the effect-handlers epic for the rung that enables this.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E005,
        title: "Unknown effect operation in `perform`",
        default_hint: "`perform E.op(...)` names an operation `op` that the effect `E` does not declare. Check the operation name against `effect E { fn op(...) -> ...; }`, or add the operation to the effect declaration.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E006,
        title: "Unknown effect in `perform`",
        default_hint: "`perform E.op(...)` names `E`, which is not a declared effect. Declare it with `effect E { fn op(...) -> ...; }`, or check the spelling.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E007,
        title: "Wrong argument count in `perform`",
        default_hint: "`perform E.op(...)` passes the wrong number of arguments for the operation's declared arity. Match the call to the operation signature `fn op(...)` in the effect declaration. (Also fires when a `handle` clause's binder count does not match the operation's arity.)",
        category: Category::Effect,
    },
    CodeEntry {
        code: E008,
        title: "Handle does not cover the effect's operations",
        default_hint: "A clause-form `handle` must provide exactly one clause per operation of each effect it discharges. Add a clause for every missing operation, and remove any duplicate clause for the same operation.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E009,
        title: "Bare `handle` on an effect with operations",
        default_hint: "The bare `handle E { ... }` form only widens the effect row; an effect that declares operations needs the clause form `handle <expr> { E.op(x) => ... }` so each operation has a meaning. Switch to the clause form, or remove the operations from the effect.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E010,
        title: "Orphan `perform` of an undeclared effect",
        default_hint: "`perform E.op(...)` requires the effect `E` to be available. Declare it in this function's effect row (`fn f(...) ! { E } { ... }`), or wrap the computation in a `handle <expr> { E.op(x) => ... }` that discharges it.",
        category: Category::Effect,
    },
    CodeEntry {
        code: E011,
        title: "Invalid effect-row variable",
        default_hint: "An effect-row variable (a type parameter used inside `! { ... }`, e.g. `fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e }`) is restricted in v1: it must be an ordinary binder on a free generic function; it must not shadow a declared effect, be used in type position, or duplicate another binder; and it may appear only in the function's declared row, the top-level row of a `Fn`-typed parameter (at most one variable per such row), or the return type. Calls to a row-polymorphic function cannot use turbofish. Rename the binder or move the row to a supported position.",
        category: Category::Effect,
    },
    // ── Ownership ──
    CodeEntry {
        code: O001,
        title: "Use after move (or duplicate linear use)",
        default_hint: "A linear value (capability, message payload) cannot be used after it has been moved. Restructure to avoid the second use, or split the capability via `cap_split` first.",
        category: Category::Ownership,
    },
    CodeEntry {
        code: O006,
        title: "Compatibility alias for T254 region escape",
        default_hint: "O006 is retained for diagnostic-code compatibility but is not emitted. Region escape is enforced as T254; return owned data or move the allocation to the caller.",
        category: Category::Ownership,
    },
    CodeEntry {
        code: O007,
        title: "Move while borrowed",
        default_hint: "Cannot move a value while a borrow (or active grant) is outstanding. Drop the borrow first, or restructure to avoid the move.",
        category: Category::Ownership,
    },
    // ── Ring ──
    CodeEntry {
        code: R001,
        title: "Outer-ring code cannot own capabilities",
        default_hint: "Capabilities live in the inner ring. Pass a borrowed capability via `grant(&cap, fn(ref) -> ...)` instead of taking ownership in outer-ring code.",
        category: Category::Ring,
    },
    CodeEntry {
        code: R002,
        title: "Capability reference returned from an outer-ring function",
        default_hint: "An outer-ring function may not RETURN a type containing a `&cap T` reference (checked structurally through tuples, arrays, closure params/returns and generic args). Return owned data instead. NOTE: this check is the return-type test only — it does not track a reference's lifetime against its `grant(...)` scope; that confinement is enforced separately by the ownership pass (O007, move-while-borrowed).",
        category: Category::Ring,
    },
    CodeEntry {
        code: R003,
        title: "Inner-ring code cannot call `extern` functions",
        default_hint: "Two ways to fix: (1) move the FFI to a `#[ring(outer)] #[trusted]` module and call the outer module's wrapper from the inner ring via `grant(&cap, fn(ref) -> ...)`, or (2) declare the calling module itself as `#[ring(outer)] #[trusted]` if it's the FFI surface module.",
        category: Category::Ring,
    },
    CodeEntry {
        code: R004,
        title: "Direct cross-ring call requires a grant",
        default_hint: "Inner and outer rings can only interact via `grant(&cap, fn(ref) -> ...)`. Direct calls across the boundary are forbidden.",
        category: Category::Ring,
    },
    CodeEntry {
        code: R005,
        title: "Compatibility alias for T109 ring-error sanitization",
        default_hint: "R005 is retained for diagnostic-code compatibility but is not emitted. Cross-ring rich error types are rejected as T109; use ErrorCode (u32).",
        category: Category::Ring,
    },
    CodeEntry {
        code: R006,
        title: "`#[trusted]` requires `#[ring(outer)]`",
        default_hint: "The `#[trusted]` privilege unlocks `handle Unsafe` and FFI extern declarations — it is only meaningful in the outer ring. Either change the module to `#[ring(outer)] #[trusted]`, or drop `#[trusted]` if the module does not need trust.",
        category: Category::Ring,
    },
    CodeEntry {
        code: R010,
        title: "Non-capability spawn argument",
        default_hint: "`spawn::<Actor>(...)` requires capability-typed arguments. Pass a value declared with `cap type T` rather than a primitive or record.",
        category: Category::Capability,
    },
    CodeEntry {
        code: R011,
        title: "Non-capability fuel argument",
        default_hint: "The fuel argument to `spawn` must be a `Fuel`-typed capability. Pass an owned `Fuel` cap (often a state field) rather than a primitive.",
        category: Category::Capability,
    },
    CodeEntry {
        code: R012,
        title: "Non-cap source or destination at restrict/split",
        default_hint: "`cap_restrict` and `cap_split` must consume and produce capability-typed values. Check the AIR pipeline if you see this — it usually indicates an upstream type-check bug.",
        category: Category::Capability,
    },
    // ── Capability (Z3) ──
    CodeEntry {
        code: C001,
        title: "Capability forgery",
        default_hint: "Capabilities cannot be constructed from record literals. They must come from `init` parameters, `spawn` results, `cap_split`, or `cap_restrict`.",
        category: Category::Capability,
    },
    CodeEntry {
        code: C002,
        title: "Capability provenance violation",
        default_hint: "Z3 detected a capability variable that may have originated from an illegitimate source (forged record, unverified value). Trace the cap's source back to an init parameter, spawn result, or attenuation site.",
        category: Category::Capability,
    },
    CodeEntry {
        code: C003,
        title: "Capability authority escalation",
        default_hint: "A restricted capability (via `cap_restrict`) was passed where full authority is required. Pass the unrestricted capability, or restructure the callee to accept the restricted authority set.",
        category: Category::Capability,
    },
    CodeEntry {
        code: C004,
        title: "Capability verifier returned unknown",
        default_hint: "Z3 returned UNKNOWN — could not prove or refute the property within the configured rlimit. The diagnostic message includes Z3's reason string. `max. resource limit exceeded` means the policy needs simplification or the rlimit needs raising; other reasons indicate a theory-level issue that should be filed as a bug. Verification is a soundness contract — UNKNOWN is treated as a hard error, never an advisory pass.",
        category: Category::Capability,
    },
    CodeEntry {
        code: C005,
        title: "SMT query outside the decidable fragment (internal)",
        default_hint: "The runtime fragment guard rejected a solver query (quantifier, disallowed op/sort, uninterpreted function, off-width bitvector, mixed theories, or oversized formula). Every query is compiler-constructed, so this indicates a compiler bug — please report it. The program is conservatively rejected, never accepted unverified. See docs/specs/z3-fragment-guard.md and docs/z3-theory-inventory.md.",
        category: Category::Capability,
    },
    CodeEntry {
        code: C010,
        title: "Capability from actor state consumed in a handler",
        default_hint: "A capability read from immutable actor state is borrow-only inside a message handler: use it non-consumingly (`grant(&field, …)` or `field.draw(n)`), or delegate it at construction time (`init`, or the entry actor's `Start`). Consuming ops (spawn arg, send/ask payload, `.split`, `.restrict`, moving it by value, returning it) are rejected so the same state cap can never be spent twice across handler invocations.",
        category: Category::Capability,
    },
    CodeEntry {
        code: C011,
        title: "`mut` actor-state field must be plain reassignable data",
        default_hint: "A `mut` state field is overwritten in handlers, so its type must be plain reassignable data — capability-, reference-, borrow-, or function-bearing types are rejected (overwriting a capability held in state would drop it without linear accounting, an unbounded leak / double-spend). Drop the `mut` (a bare state field keeps the immutable-after-init cap/ref discipline), or store an inline scalar (`i64`, `bool`, `f64`) in the `mut` field instead.",
        category: Category::Capability,
    },
    CodeEntry {
        code: C012,
        title: "`mut` actor-state field's element shape is not yet preserved across dispatches",
        default_hint: "A `mut` state field persists when every stored element can be promoted at its storing write: inline scalars, `str`, flat scalar records (a record of scalars), and `Vec`/`Map` collections whose elements (Vec elements, Map keys/values) are any of those. What is not yet preserved is an element the promotion's field copy cannot deep-copy — a record with a pointer-bearing interior (str/Vec/record fields), a nested collection, or a 256-bit value. Flatten the element (inline the nested fields as scalars), store parallel collections of promotable elements, or await the transitive-promotion slice of the persistent-pointer-state epic.",
        category: Category::Capability,
    },
    // ── FFI ── (F001 reserved — removed pending a firing path; see codes.rs)
    // ── Runtime feedback (R800-R899) ──
    CodeEntry {
        code: R800,
        title: "Runtime error",
        default_hint: "A runtime-side error occurred during execution. Inspect the message and audit log for context.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R801,
        title: "Fuel exhausted",
        default_hint: "Increase the fuel budget via `--fuel <n>` or simplify the program to consume fewer fuel units. Fuel is decremented on every call and loop back-edge.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R802,
        title: "Missing Wasm export",
        default_hint: "The compiled module is missing an export the runtime expected. This usually indicates a compiler/runtime ABI mismatch — file an internal compiler error report.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R803,
        title: "Tool trapped during execution",
        default_hint: "The tool hit a Wasm trap (out-of-bounds access, unreachable, host error). Check the tool's host-call usage and ensure inputs are valid.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R804,
        title: "Tool module missing `tool_main` entry point",
        default_hint: "Add `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64` to the tool module. See `lang-ref.md` for the entry-point ABI.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R806,
        title: "Capability table error",
        default_hint: "A capability operation (split / restrict / lookup) failed at runtime. Check the capability flow and ownership in the source.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R807,
        title: "Wasm validation or instantiation error",
        default_hint: "The runtime could not load or validate the compiled Wasm module. This usually indicates a compiler bug — file an internal compiler error report.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R808,
        title: "I/O grant set exceeds per-category cap",
        default_hint: "Each grant category (`fs`, `fs_write`, `net`, `time`, `random`) is capped at 256 entries. Reduce the grant list, or split the workload across multiple tool invocations with narrower grant sets.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R809,
        title: "Verification certificate did not validate",
        default_hint: "The supplied certificate does not match the source. Inspect the structured `differences` list in the envelope data — typical causes are a tampered cert, a mismatched source file, or a cert generated by a different compiler version that produces different proof obligations.",
        category: Category::Internal,
    },
    // ── Certificate gating (R810-R816, iteration 36 of Spec A + E) ──
    CodeEntry {
        code: R810,
        title: "Certificate file unreadable, not a regular file, or over 1 MB",
        default_hint: "The `--cert <path>` argument must point at a regular file no larger than 1 MB. Check the path is correct, the file isn't a fifo / symlink to a special device, and re-emit if the cert was corrupted: `sigil check <source> --cert <path>`.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R811,
        title: "Certificate JSON parse failure",
        default_hint: "The cert file exists and is well-formed at the filesystem level, but its contents are not valid SIGIL cert JSON. Re-emit the cert with `sigil check <source> --cert <path>`. If the cert came from a different SIGIL version, see R812 — the schema may have changed.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R812,
        title: "Certificate schema version unsupported by gate",
        default_hint: "The run/forge gate accepts schema v3 only (SHA-256 fingerprints). Re-emit with the current compiler: `sigil check <source> --cert <path>`. The `sigil verify-cert` reporter still reads older schemas with a deprecation warning, but the gate refuses to bind to a hash algorithm that isn't collision-resistant.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R813,
        title: "Source fingerprint mismatch",
        default_hint: "The cert was emitted from a different source than what's about to run. Either revert the source to the version the cert was emitted from, or re-emit the cert: `sigil check <source> --cert <path>`. The diagnostic message names the cert's hash and the freshly-computed hash; compare to find the divergence.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R814,
        title: "WASM inner-module fingerprint mismatch",
        default_hint: "The freshly-compiled WASM does not match the cert's claimed `wasm_inner_fingerprint`. If the source matches but the WASM differs, the compiler may have introduced non-determinism — file a bug. Otherwise re-emit the cert: `sigil check <source> --cert <path>`.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R815,
        title: "WASM outer-module fingerprint mismatch or missing",
        default_hint: "The cert claims a `wasm_outer_fingerprint` but the current compilation produced no outer module (or vice versa, or the bytes differ). Re-emit the cert from the current source: `sigil check <source> --cert <path>`. Single-module programs never trigger this code.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R816,
        title: "Effect set mismatch between certificate and runtime",
        default_hint: "The cert declares a different set of required effects than the runtime is configured to grant. The message names the offending effects in both directions: `cert requires X but runtime lacks` (under-grant; add `--fs`/`--net`/etc.) or `runtime grants Y but cert doesn't claim` (over-grant; either remove the extra grant or re-emit the cert with the broader effect surface).",
        category: Category::Internal,
    },
    CodeEntry {
        code: R818,
        title: "Persistent heap exhausted",
        default_hint: "A persistent allocation would raise the actor's persistent floor past the host's per-actor byte cap (PPS-4). The message names the actor, the requested bytes, the floor it would reach, and the cap. Under `Restart(n)` supervision this trap IS the collector: the restart discards the persistent heap and replays a replay-safe `init`, so growth starts over from birth. If it fired without supervision, add `supervision: Restart(n)` to the spawn, raise the cap (`RuntimeHost::set_persistent_cap` / `--persistent-cap`), or reduce replace-heavy state churn (every replacement abandons its predecessor's bytes until a restart reclaims them).",
        category: Category::Internal,
    },
    CodeEntry {
        code: R817,
        title: "Certificate not solver-verified (Z3 proofs did not run)",
        default_hint: "The cert records `solver_verified: false`: it was produced by a solver-off toolchain (`--no-default-features`), so the Z3 flow-sensitive proofs — capability flow (C002-C004) and refinement discharge (T210/T215/…) — never ran. Only the structural half was checked. The run/forge gate fails closed rather than vouch for unverified obligations. Rebuild the compiler with the `solver` feature and re-emit the cert, or, for dev/CI only, set `SIGIL_ALLOW_UNVERIFIED_CERT=1` to accept the structural-only artifact deliberately.",
        category: Category::Internal,
    },
    CodeEntry {
        code: R819,
        title: "Formal security report or CSIR fingerprint mismatch",
        default_hint: "Schema-v9 execution requires a formal report freshly re-derived by the current compiler. The supplied report is missing or differs in model version, checker fingerprint, canonical CSIR fingerprint, toolchain, or checked counts. Treat this as certificate tampering or toolchain drift and re-emit the certificate from the exact source and compiler binary.",
        category: Category::Internal,
    },
    // ── Type checking — declarations & assignments ──
    CodeEntry {
        code: T040,
        title: "Constant value type mismatch",
        default_hint: "The constant's value type does not match its declared annotation. Either change the annotation or cast the value to the expected type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T041,
        title: "Let binding type mismatch",
        default_hint: "The let binding's value does not match its declared type annotation. Drop the annotation to let the type be inferred, or fix one side to match.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T042,
        title: "Cannot assign to immutable variable",
        default_hint: "Declare the binding with `let mut name = ...` to allow reassignment.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T043,
        title: "Reassignment forbidden — value owns a linear or scope-tied resource",
        default_hint: "Reassignment is allowed for primitives, ActorRef, arrays, and any record / enum whose fields are themselves reassignable. It is rejected when the value transitively owns a capability (linear) or a borrow (scope-tied). For cap-bearing values, consume the cap rather than store it; for borrow-bearing values, drop the borrow before reassigning.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T044,
        title: "Missing return value",
        default_hint: "The function declares a non-unit return type but no `return <value>` statement reaches the end. Add a return value on every control-flow path.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T045,
        title: "Assignment value type mismatch",
        default_hint: "The assigned value's type does not match the variable's declared type. Convert the value or change the variable type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T046,
        title: "Unsupported let binding annotation",
        default_hint: "Let bindings accept two annotation shapes: (a) primitive types `i32`, `u32`, `i64`, `u64`, `f64`, `bool`; (b) generic record types with concrete type arguments matching the declaration's arity, e.g. `let h: Holder<i64> = Holder { value: 42 };` for `record Holder<T> { value: T }`. For non-generic records, drop the annotation and let inference run (`let x = ...`). Mixed cases — generic record annotated without arity, or unknown type — fall through to T046.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T047,
        title: "`return` requires a value",
        default_hint: "The function returns a non-unit type but this `return` has no value. Add the value: `return <expr>;`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T048,
        title: "Unit-returning function cannot return a value",
        default_hint: "This function returns `()` (no return type or `-> ()`). Change to `return;` or remove the return.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T049,
        title: "Return value type mismatch",
        default_hint: "The returned value's type does not match the function's declared return type.",
        category: Category::TypeCheck,
    },
    // ── Type checking — control-flow conditions & operators ──
    CodeEntry {
        code: T050,
        title: "`if` condition must be `bool`",
        default_hint: "`if` requires a boolean condition. Compare your value (e.g., `x == 0`) instead of using it directly.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T051,
        title: "`while` condition must be `bool`",
        default_hint: "`while` requires a boolean condition. Compare your value (e.g., `i < n`) instead of using it directly.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T052,
        title: "`for-in` requires an array",
        default_hint: "`for x in ...` only iterates arrays today. Materialize a `[...]` literal or pass an array variable.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T053,
        title: "`match` arm guard must be `bool`",
        default_hint: "Guards (`if <expr>`) must evaluate to `bool`. Compare your value rather than using it directly.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T054,
        title: "Numeric operator requires matching operands",
        default_hint: "Arithmetic and shift operators require both operands to be the same numeric type. Cast one side or change the literal type suffix.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T055,
        title: "Comparison operator requires comparable operands",
        default_hint: "Comparison operators (`<`, `<=`, etc.) require operands of compatible types. Cast or normalize the types before comparing.",
        category: Category::TypeCheck,
    },
    // ── Type checking — undefined names ──
    CodeEntry {
        code: T060,
        title: "Undefined local",
        default_hint: "This name is not in scope. Declare it with `let`, add it as a parameter, or check the spelling.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T062,
        title: "Undefined function",
        default_hint: "No function with this name is in scope. Declare it, import it via `use`, or check the spelling.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T064,
        title: "Unknown actor",
        default_hint: "No actor with this name has been declared. Add an `actor X { ... }` definition or check the spelling.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T065,
        title: "Actor has no such handler",
        default_hint: "The actor does not declare a handler for this message. Add `on Message(...) { ... }` to the actor body, or check the message name.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T066,
        title: "Unknown type",
        default_hint: "No type with this name is in scope. Declare a `record`, `enum`, or `cap type`, import via `use`, or check the spelling.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T067,
        title: "Unknown actor in `ActorRef<T>`",
        default_hint: "The named actor does not exist. Declare `actor X { ... }` with that name, or correct the spelling.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T068,
        title: "Control-flow statement in `handle`/`region` body",
        default_hint: "`handle` and `region` bodies are lowered inline within a single AIR basic block, so block-creating statements (`if`, `while`, `match`, `for`, `return`) cannot live there without a separate proof framework for cross-block effect/region scoping. Use straight-line code (`let`, `=`, expression statements). Extract control flow into a helper function called from the body.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T069,
        title: "Unknown effect",
        default_hint: "Declare the effect with `effect X;` somewhere in scope, or check the spelling. `Unsafe`, `FFI`, `NetIO`, `FsIO`, `Alloc` are well-known names.",
        category: Category::TypeCheck,
    },
    // ── Type checking — arity & argument count ──
    CodeEntry {
        code: T070,
        title: "Function call arity mismatch",
        default_hint: "Pass the exact number of arguments the function declares.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T071,
        title: "Function argument type mismatch",
        default_hint: "Each call argument must match the declared parameter type. Convert or cast the offending argument.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T072,
        title: "Enum variant constructed with wrong arity",
        default_hint: "Provide exactly the number of fields declared by the enum variant.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T073,
        title: "Function returning `()` used as a value",
        default_hint: "This function does not return a value. Call it as a statement, or change the function to return a value.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T074,
        title: "Intrinsic call arity mismatch",
        default_hint: "`alloc` takes 1 argument; `load8` takes 1; `store8` takes 2. Check your call site.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T075,
        title: "Intrinsic argument type mismatch",
        default_hint: "Intrinsic arguments must be integer types: `alloc(size: i64)`, `load8(ptr: i64)`, `store8(ptr: i64, val: i64)`.",
        category: Category::TypeCheck,
    },
    // ── Type checking — patterns & exhaustiveness ──
    CodeEntry {
        code: T080,
        title: "Match arm after catch-all is unreachable",
        default_hint: "The `_` arm matches everything; arms after it are dead. Move them above the `_` arm or remove them.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T081,
        title: "Match pattern type does not match scrutinee",
        default_hint: "Each pattern must match the type of the matched expression. Use a literal of the same type or restructure the match.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T082,
        title: "Duplicate match pattern",
        default_hint: "The same literal appears as the head of two arms — only the first can match. Remove the duplicate.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T083,
        title: "Duplicate `_` match arm",
        default_hint: "A `match` may have at most one catch-all `_` arm. Remove the duplicate.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T084,
        title: "Variant pattern against non-enum scrutinee",
        default_hint: "Enum variant patterns (`Some(x)`, `Err(e)`) only match enum-typed scrutinees. Match a different shape, or change the scrutinee.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T085,
        title: "Enum variant pattern arity mismatch",
        default_hint: "The pattern must bind exactly as many fields as the enum variant declares.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T086,
        title: "Enum has no such variant",
        default_hint: "The named variant is not declared on this enum. Add it to the enum definition, or use an existing variant name.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T087,
        title: "Non-exhaustive match (missing variants)",
        default_hint: "Add an arm for every missing enum variant, or add a `_` catch-all.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T088,
        title: "Non-exhaustive match (add `_` arm)",
        default_hint: "Add `_ => { ... }` as the final arm to cover remaining cases.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T089,
        title: "Cannot infer type of empty array literal",
        default_hint: "Annotate the binding (e.g., `let xs: [i64] = [];`) so the element type is known.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T190,
        title: "Range pattern: lower bound greater than upper bound",
        default_hint: "Inclusive range patterns require `lo <= hi`. Swap the bounds (e.g., `0x30..=0x39`, not `0x39..=0x30`).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T191,
        title: "`Slot<T>` requires T to be a capability type",
        default_hint: "Slot is a built-in linear container designed for capability accumulation. Instantiate with a `cap type` declared in scope (e.g., `Slot<Fuel>`), not a primitive or record.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T192,
        title: "`slot_new` requires a type argument",
        default_hint: "Slot's element type can't be inferred from an empty argument list. Specify it explicitly: `slot_new::<Fuel>()`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T193,
        title: "Type name `Slot` is reserved",
        default_hint: "`Slot` names the built-in linear container; user records, enums, and cap types cannot reuse the name. Rename your type (e.g., `SlotState`, `MySlot`).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T195,
        title: "Deadline-typed capability subtype mismatch",
        default_hint: "The source cap's deadline is earlier than the target site requires. Covariant subtyping reads `Approval(D_a) <: Approval(D_b)` iff `D_a >= D_b` — a longer-lived cap is acceptable wherever a shorter-lived one is required, but not the reverse. Widen the target's expected deadline to `<=` the source's, or narrow the source via `restrict_deadline(...)` (Stage 2/3 of the deadline rollout).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T196,
        title: "Parametric capability requires a deadline literal at this position",
        default_hint: "The capability type was declared as parametric (`cap type <Name>(<param>: i64) {}`); every reference must supply a bound `i64` deadline literal — e.g., `Approval(2030_06_01)`. Add the literal at this site, or, if the cap should be non-parametric, change the declaration to `cap type <Name> {}`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T197,
        title: "Non-parametric capability cannot accept a deadline literal",
        default_hint: "The capability type was declared as non-parametric (`cap type <Name> {}`); references must not supply a `(...)` argument. Remove the literal at this site, or, if the cap should be parametric, change the declaration to `cap type <Name>(<param>: i64) {}` (Stage 1 supports a single `i64` parameter).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T198,
        title: "Invalid parametric capability declaration",
        default_hint: "Parametric capability types are declared as `cap type <Name>(<param>: i64) {}`. Empty parentheses, missing parameter type, and non-`i64` parameter types are not supported in Stage 1. Use the canonical form, or omit the parentheses entirely for a non-parametric cap.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T199,
        title: "Parametric capability literal is past the build-time deadline",
        default_hint: "The cap-type literal declares a deadline earlier than the value supplied via `--build-deadline`, OR a `restrict_deadline(D')` argument narrows past the build deadline. The compiler refuses to build a program whose caps would be stale at compile time. Either widen the literal to a value `>=` the build deadline, raise the build deadline (or drop the flag), or remove the narrowing if it's intentional staleness for testing.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T200,
        title: "`restrict_deadline` cannot extend, run on non-parametric, or narrow a multi-parameter cap",
        default_hint: "`cap.restrict_deadline(D')` produces a cap with `min(D_orig, D')` — it can only narrow a SINGLE-parameter cap. Three variants fire T200: (a) extension (`D' > D_orig`), (b) call on a non-parametric cap (no deadline to narrow), (c) call on a multi-parameter cap (Wall 3 Stage 1 doesn't support multi-parameter narrowing — split into separate single-parameter cap types).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T201,
        title: "Parametric capability used with wrong number of values",
        default_hint: "`cap type Limited(deadline: i64, max_uses: i64) {}` declares arity 2; usages must supply exactly 2 `i64` literals. Arity mismatch (M != N, both > 0) fires T201. The arity-0 cases are still T196 (parametric used without values) and T197 (non-parametric used with values). Supply exactly the declared number of values at the usage site, matching the declared parameter order.",
        category: Category::TypeCheck,
    },
    // ── Wall 4 Step 1: refinement predicates on i64 record fields ──
    CodeEntry {
        code: T210,
        title: "Record construction violates a declared refinement predicate",
        default_hint: "The record's `where` clause cannot be discharged against the supplied literal field value. Z3 either returned a counterexample (the predicate is refutable) or exhausted its rlimit budget (Unknown). Either change the literal so the predicate holds, or weaken the refinement at the record declaration. Step 1 supports only integer-literal RHS values; non-literal field arguments emit T211.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T211,
        title: "Refinement check requires a literal field value",
        default_hint: "Wall 4 Step 1 supports refinement satisfiability only when every field value supplied to a refined-record construction is a `TypedExpr::IntLiteral`. Symbolic values (function parameters, function-call results, destructured field reads) are explicitly deferred to a later step that adds fact propagation. Construct with a literal, or lift the computation into a non-refined intermediate record. If the value came from a refined field read, inline it at the construction site (refinement is not preserved through `let` bindings or other intermediate expressions).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T212,
        title: "Refinement predicate references a non-i64 field",
        default_hint: "Refinement predicates may only constrain `i64`-typed fields in Wall 4 Step 1. Cap-typed fields, aggregate-typed fields, and other primitive types are out of scope; Wall 2's deadline-typed caps already cover cap refinement. Move the refinement off the non-i64 field, or expose an `i64` projection that carries the constraint.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T213,
        title: "Refinement RHS literal out of i32 range",
        default_hint: "Refinement RHS integer literals must lie in the closed range [-2_147_483_648, 2_147_483_647]. The QF_LIA Z3 encoding used by Step 1 is sound only within this range; out-of-range literals could diverge from i64 runtime semantics. Choose a smaller literal, or wait for a later step that adopts a QF_BV<64> encoding.",
        category: Category::Parser,
    },
    CodeEntry {
        code: T214,
        title: "Excess refinement clauses in a `where` position",
        default_hint: "Every refinement `where` position — record declaration, enum-variant payload, function parameter, and return value — admits exactly ONE `<lhs> <op> <rhs>` clause. A second clause is rejected whether it arrives via a `&&` / `||` combinator or a second `where` keyword; combinator support is deferred to a future step. Collapse the constraint into the strongest single bound, carry the second clause as the refinement of a wrapping record, or check it with a runtime assert.",
        category: Category::Parser,
    },
    // ── Wall 4 Step 5: array-length refinement RHS ──
    CodeEntry {
        code: T217,
        title: "Refinement RHS `.length()` references a non-array field",
        default_hint: "Wall 4 Step 5 admits `<field>.length()` at refinement RHS position ONLY when `<field>` is directly-owned `Type::Array { elem, size }`. Slices, references to arrays, and any other type are out of scope (anti-goal A11). Use the array's exact size as a literal (`where len == 8`) instead, or convert the slice/reference to an owned array field.",
        category: Category::TypeCheck,
    },
    // ── Wall 4 Step 4: cross-field refinement RHS ──
    CodeEntry {
        code: T216,
        title: "Cross-field refinement references a field missing or unsuppliable at construction",
        default_hint: "Wall 4 Step 4 admits `where <lhs_field> <op> <rhs_field>` cross-field refinement clauses. At each construction site, BOTH the LHS and RHS fields must be supplied with concrete or refinement-attached values (per V72's 9-case dispatcher matrix). When at least one side is symbolic-without-refinement, the cross-field predicate cannot be discharged and T216 fires. Either supply concrete literals for both fields, attach refinements to the source field-reads (Step 2's preservation), or drop the cross-field clause.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T218,
        title: "Cross-field refinement self-references the same field",
        default_hint: "Wall 4 Step 4's `where <lhs> <op> <rhs>` requires LHS and RHS to be DIFFERENT field names. `where a == a` is vacuously true (any value equals itself); `where a < a` is vacuously false. Such a predicate carries no information beyond what the record's other invariants already provide. Pick distinct fields, use a literal RHS (`where a < 100`), or drop the clause.",
        category: Category::Parser,
    },
    CodeEntry {
        code: T219,
        title: "Cross-field refinement RHS field is not `Type::I64`",
        default_hint: "Wall 4 Step 4 admits cross-field refinements only when BOTH the LHS field AND the RHS field are `Type::I64` (per V60 / anti-goal A9). T212 covers non-i64 LHS; T219 covers non-i64 RHS. Cap-typed fields (A10), other integer types (i32, u32, u64), bool, and named-record fields are out of scope. Convert the RHS field to `i64`, or drop the cross-field clause.",
        category: Category::TypeCheck,
    },
    // ── Wall 4 Step 2: refinement preservation through field reads ──
    CodeEntry {
        code: T215,
        title: "Refinement supplied does not match destination's required predicate",
        default_hint: "Wall 4 Step 2 propagates refinements through `TypedExprKind::FieldAccess`. The supplied symbolic value carries a refinement (from the source record's `where` clause), but none of its clauses subsume this destination clause. Refinement match compares operator and literal only; field names are not compared. Wall 4 Step 3 attempts Z3-backed semantic implication when syntactic match fails: if the source's predicate provably implies the destination's over i64, the construction is accepted. If Z3 returns a counterexample (a specific `x` value that satisfies the source's predicate but violates the destination's), the counterexample is embedded in the diagnostic message. To fix, either weaken the destination's predicate, strengthen the source's, or pick a literal that satisfies the destination directly.",
        category: Category::TypeCheck,
    },
    // ── Wall 4 Step 6: refinement on enum variants ──
    CodeEntry {
        code: T220,
        title: "Variant refinement predicate violated at construction",
        default_hint: "Wall 4 Step 6 mirrors record refinement (T210) onto enum variants. The supplied payload value violates the variant's declared `where` clause; Z3 found a counterexample. Either supply a literal value that satisfies the predicate, ensure the symbolic value's preserved refinement subsumes the variant's (per Step 3's Z3-backed implication path), or weaken the variant's `where` clause. The diagnostic message carries the variant-qualified name (`EnumName::VariantName`), the violated predicate, and Z3's counterexample.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T221,
        title: "Pattern-narrowing or variant-refinement field-resolution conflict",
        default_hint: "Wall 4 Step 6 reserves T221 for two cases: (a) a `match` arm's variant-declared refinement contradicts an already-attached refinement on the matched scrutinee — refactor the upstream code so the refinements are compatible; (b) a variant `where` clause references a field name that doesn't appear in this variant's payload (cross-variant references are not in scope per N19-S6) — pick a payload field of THIS variant or move the refinement to the variant that owns the field.",
        category: Category::Parser,
    },
    CodeEntry {
        code: T222,
        title: "Variant refinement references a non-`Type::I64` payload field",
        default_hint: "Wall 4 Step 6 requires variant-refinement-referenced payload fields to be `Type::I64` (per N6-S6, A9-S6, A10-S6). T222 mirrors T212 for variants. Cap-typed payload fields, other integer types (i32, u32, u64), bool, and named-record fields are out of scope. Either convert the payload field to `i64`, or drop the refinement clause referencing it.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T223,
        title: "Variant payload shape error",
        default_hint: "Wall 4 Step 6 admits variant refinements only on fully-named payloads. T223 fires for four parser-level cases: (1) a positional-only variant declared with a `where` clause (`V(i64) where x > 0`) — name the payload fields (`V(x: i64) where x > 0`); (2) mixed named/positional payload (`V(x: i64, i64)` or `V(i64, x: i64)`) — pick all-named or all-positional; (3) duplicate field name in a named variant (`V(x: i64, x: i64)`) — rename one; (4) zero-payload variant with a refinement clause (`Zero where 1 == 1`) — variants with no fields cannot carry refinements.",
        category: Category::Parser,
    },
    // ── Wall 4 Step 7: refinement on function parameters / return types ──
    CodeEntry {
        code: T224,
        title: "Call-site argument violates declared parameter refinement",
        default_hint: "Wall 4 Step 7 admits parameter refinements via `fn name(p: i64) where p > 0`. Callers must supply values that satisfy the predicate: (a) a literal argument is Z3-checked directly (T224 fires on Sat); (b) a symbolic argument with a preserved refinement (from a refined-return call result or a refined record-field read) is checked via Step 3's syntactic-match + Z3 subsumption — T224 fires if no clause subsumes; (c) a symbolic argument with no preserved refinement fires T211 (use a literal or refactor the upstream computation to preserve refinement). Z3 `Timeout` fires T224 with a timeout-flavored detail; counterexamples surface when Z3 returns Sat with a model.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T225,
        title: "Function body `return` expression violates declared return refinement",
        default_hint: "Wall 4 Step 7 admits return refinements via `fn name(...) -> i64 where @ > 0`. The function body's `return <expr>` statements are checked against the declared `@` predicate. The recursive walker descends into `if`/`match`/`while`/`for`/nested blocks; every return path is checked. To fix, either weaken the declared return predicate or ensure every reachable return supplies a value satisfying it.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T226,
        title: "Refinement on generic function / closure / no-return function — rejected",
        default_hint: "Wall 4 Step 7 explicitly defers three contexts for function refinement: (1) generic functions (`fn id<T>(x: T) where x > 0`) — refinement does not propagate through monomorphization; (2) closures — captures lose refinement at lambda-lifting; (3) functions with `where @ ...` but no return type — `@` has no referent. To fix: (1) make the function non-generic (drop the `<T>` params); (2) move the logic into a free function; (3) declare an `i64` return type.",
        category: Category::Parser,
    },
    // ── SIGIL Complete v0 — Phase 1.1 array size + Phase 6 impl generics ──
    CodeEntry {
        code: T227,
        title: "Array size mismatch",
        default_hint: "SIGIL Complete v0 / Phase 1.1: array types `[T; M]` and `[T; N]` are compatible only when `M == N`. Pre-v0 the Array arm of `type_compatible` discarded the size field, making `LengthOf` refinements and every fixed-size-array contract unsound. To fix: either (a) change the producer's literal/expression to match the declared size, (b) change the consumer's declared `[T; N]` to match the producer's size, or (c) widen the consumer's signature to accept `&[T]` (slice) which coerces from any `[T; N]`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T228,
        title: "Method-level type parameter shadows impl-block-level type parameter",
        default_hint: "SIGIL Complete v0 / Phase 6: with first-class generic impl blocks (`impl Result<T, E> { ... }`), the impl's `<T, E>` are in scope for every method body. Redeclaring one of them as a method-level type parameter (`fn map<T>(...)`) would silently shadow the impl's binding at dispatch time and break substitution. To fix: either (a) rename the method-level type parameter to a fresh name (e.g., `<U>` instead of `<T>`), or (b) drop the method-level redeclaration if the intent was to refer to the impl's binding (the impl's `T` is already in scope without redeclaration).",
        category: Category::Parser,
    },
    CodeEntry {
        code: T229,
        title: "Impl block declares duplicate type parameter names",
        default_hint: "SIGIL Complete v0 / Phase 6: an impl block's type parameter list must contain unique names — `impl Foo<T, T> { ... }` is rejected because positional substitution against the receiver's concrete type args would silently collapse to one binding. To fix: rename one of the duplicates (e.g., `impl Foo<T, U>` if the two are truly independent, or drop one if a single parameter suffices).",
        category: Category::Parser,
    },
    CodeEntry {
        code: T230,
        title: "Method `self`-param type-args don't mirror impl block's type parameters",
        default_hint: "SIGIL Complete v0 / Phase 6: per N6-V0, a method declared inside `impl TypeName<T, E> { ... }` must have its `self` parameter typed as exactly `TypeName<T, E>` in the same declaration order. Swapping or substituting (`self: Result<E, T>` when impl is `Result<T, E>`) silently mis-binds substitutions at dispatch time. To fix: align the `self`-param's type-args with the impl block's type parameters in declaration order.",
        category: Category::Parser,
    },
    CodeEntry {
        code: T231,
        title: "Method dispatch arity mismatch with impl block's type parameters",
        default_hint: "SIGIL Complete v0 / Phase 6: at method dispatch, the receiver's concrete type-arg count must equal the impl block's `type_params.len()`. A receiver shaped `Result<i64>` (1 arg) cannot dispatch against `impl Result<T, E> { ... }` (2 params). To fix: supply the missing type argument(s) at the receiver's construction site, or call against a different impl block whose type-param count matches.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T232,
        title: "Method dispatch receiver carries unresolved generic",
        default_hint: "SIGIL Complete v0 / Phase 6: at method dispatch, every entry in the receiver's type-args must be either concrete OR a `Type::Generic` that is bound in the current scope (impl-block / method / outer-fn type_params). An unscoped generic (passed in from a context that never bound it) would identity-substitute and pass the call vacuously. To fix: either (a) ensure the caller's containing function declares the relevant `<T>` in its type parameters, or (b) substitute the generic at the call site with a concrete type via turbofish.",
        category: Category::TypeCheck,
    },
    // ── PR A: Generic record CONSTRUCTION substitution ──
    CodeEntry {
        code: T233,
        title: "Type parameter cannot be inferred at generic record construction",
        default_hint: "PR A / SIGIL Complete: at a generic record construction site (e.g., `Holder { value: 42 }` against `record Holder<T> { value: T }`), SIGIL infers type parameters by unifying each supplied field value's type against the record's declared field types. T233 fires when the type parameter doesn't appear in any field's type — common for phantom-T records where the parameter exists only at the type level. To fix: add an explicit type annotation on the binding (`let x: RecordName<ConcreteType> = RecordName { ... }`); the annotation propagates concrete args into the construction's substitution map BEFORE field inference runs.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T234,
        title: "Conflicting type-parameter inferences across construction fields",
        default_hint: "PR A / SIGIL Complete: a generic record construction binds the same type parameter to incompatible types across multiple fields (e.g., `record Foo<T> { a: T, b: T }` with `Foo { a: 42, b: \"hi\" }` infers T=i64 from `a` AND T=Str from `b`). The diagnostic describes the conflict rather than picking one field as the violator. To fix: either (a) supply consistent types across all fields binding the same parameter, or (b) split the conflicting positions into independent parameters (`record Foo<T, U> { a: T, b: U }`). A single T234 fires per conflicting parameter regardless of how many fields contribute conflicts; downstream type-checks see `Type::Error` for the conflicting parameter to prevent cascade.",
        category: Category::TypeCheck,
    },
    // ── PR B: ambiguous bare enum variant constructor ──
    CodeEntry {
        code: T236,
        title: "Ambiguous bare enum variant constructor",
        default_hint: "PR B / N22-PRB: a bare variant call (e.g., `Some(42)`) matches the variant of more than one enum declared in this compilation unit, and no annotation context is available to disambiguate. The candidate enums are listed in the message. To fix: either (a) add a type annotation on the binding (`let x: Option<i64> = Some(42)`) so the compiler can pick the right enum from the expected type, or (b) qualify the constructor (`Option::Some(42)`). Per N22-PRB the check fires for ANY ambiguous match — stdlib enums do NOT receive precedence over user-defined enums; the user must commit to one explicitly.",
        category: Category::TypeCheck,
    },
    // ── HOF prerequisite: general closure-call dispatch ──
    CodeEntry {
        code: T237,
        title: "Linear closure passed to non-linear `Fn(T) -> U` parameter",
        default_hint: "HOF prerequisite / N4-HOF: a closure that captures one or more `Cap<_>` values (and is therefore `Type::Fn(_, _, true, _)` — linear, single-use) was passed where a non-linear `Fn(T) -> U` parameter is expected. The general closure-call dispatch only admits non-linear (multi-use) closures; linear closures must invoke through a `grant` block so the runtime can enforce single-use semantics. To fix: either (a) rewrite the closure to not capture the `Cap<_>` value (capture a non-cap projection if possible), or (b) invoke through `grant cap, |args| { ... }` — the existing grant-lifecycle dispatch handles linear closures safely. Note: this restriction is intentional for the prerequisite PR; a future PR may add runtime single-use tracking for general linear dispatch (AG-HOF-B documents the deferred work).",
        category: Category::TypeCheck,
    },
    // ── PR AF: bare slice operator requires `&` borrow ──
    CodeEntry {
        code: T238,
        title: "Slice operator requires a borrow",
        default_hint: "PR AF / N18-AF: the slice operator `arr[lo..hi]` (and its open-range relatives `[..hi]`, `[lo..]`, `[..]`) produces a `&[T]` view via view-semantics, so it MUST appear as the inner expression of an `&` borrow: write `&arr[lo..hi]` not `arr[lo..hi]`. The borrow makes the view's lifetime explicit and lets the type-checker treat the result as `Type::Slice(T)`. Owned slicing (moving a sub-range out of an array) is out of scope; future PR can lift this restriction if a real use-case emerges. Note: T238 fires from a SINGLE canonical site in `infer_slice_expr` based on the immediate-parent-is-borrow flag (set only by `BorrowContextGuard` from `infer_borrow_expr`'s recursion); let-annotations, return-type annotations, and function-arg expected-type DO NOT admit the bare form.",
        category: Category::TypeCheck,
    },
    // ── .contains() admitted for every ==-bearing scalar + str; composites rejected ──
    CodeEntry {
        code: T240,
        title: "`.contains()` not admitted for this element type",
        default_hint: "`.contains(x)` on an Array or Slice is admitted for every element type that has a built-in equality: the scalars {i32, u32, i64, u64, f64, bool} (scanned with a width-dispatched I32Eq/I64Eq/F64Eq) and `str` (compared by CONTENT via the `strings::__sigil_slice_str_contains` helper, which uses `str_bytes_eq` — length-equal + byte compare — the same semantics as `str ==`, which byte-compares since PR #699). T240 fires only for COMPOSITE element types that have no built-in element equality: record, enum, named, ref, tuple, nested array-or-slice, generic, or unit. For those, pattern-match on the contents directly or write a custom contains helper. (f64 IS admitted; note that `==` semantics mean NaN never matches itself — identical to the f64 `==` operator, so `.contains(nan)` is always false.)",
        category: Category::TypeCheck,
    },
    // ── Cap-smuggling through a generic aggregate at instantiation time ──
    CodeEntry {
        code: T242,
        title: "Generic aggregate instantiated with a capability-typed argument",
        default_hint: "Capabilities cannot ride through generic-aggregate slots — record fields (T183), enum variant payloads (T184), or array elements (T186) — even when the cap appears only AFTER type-arg substitution. The aggregate's declaration uses `Type::Generic(\"T\")` so the declaration-time cap check sees nothing to reject; at construction the substitution rewrites the slot to a concrete cap type, but pattern-destructuring or field-projection on the resulting value loses the cap's restriction provenance (Z3's authority tracker sees a fresh full-authority cap, same gap T183/T184/T186 close for concrete-payload cases). The same rejection applies to nested occurrences (`Option<Option<Cap>>`, `record R<T> { v: T }` instantiated with `T = Cap`, `[T; N]` monomorphized with cap-typed T, etc.) — the cap-containment check is recursive. To fix: pass the cap by name through actor messages or function arguments, or replace the payload with a non-cap surrogate (e.g., an `i64` amount). For Option/Result over caps specifically, use a non-cap surrogate inside the enum and dispatch on a separate cap held in actor state.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T243,
        title: "Invalid assignment target",
        default_hint: "The left side of `=` (or a compound `op=`) must be a place: a variable (`x`), a record field (`r.f`, `a.b.c`), or an array/slice element (`arr[i]`). Other forms denote values, not storage, so there is nowhere to write — a call (`f() = e`), an arithmetic/comparison result (`(a + b) = e`), a conditional, a literal, a closure, or a borrow (`&x = e`) are all rejected. To capture a computed value, bind it first (`let x = f(); …`) and assign through `x`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T244,
        title: "Ambiguous cross-module impl member",
        default_hint: "A method or associated function `Type::name` is not defined in the current module yet is defined by two or more sibling modules, so cross-module dispatch cannot choose one. A type's `impl` block must live in exactly one module — move the conflicting impls into a single module, or call the intended one from inside its own module. (Stdlib types like `Vec` define their impl in exactly one place; this fires on user-introduced collisions.)",
        category: Category::TypeCheck,
    },
    // ── Trait Wall: bound satisfaction ──
    CodeEntry {
        code: T245,
        title: "Type does not satisfy a trait bound",
        default_hint: "A type parameter is constrained by a trait (e.g. `<T: Hash>`), but the concrete type it was instantiated with has no impl of that trait. v1 provides built-in impls of `Hash` and `Eq` for the primitives `i64`, `str`, and `bool`; a user `record` satisfies a trait by declaring the trait's method(s) with the exact signature (structural satisfaction). To fix: instantiate with a type that has an impl, give the type the required method, or drop the bound.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T246,
        title: "Trait method signature mismatch",
        default_hint: "The type has a method with the trait's name, but its signature does not match what the trait requires — check the parameter types and the return type. For `Hash` the method must be exactly `fn hash(self: Self) -> i64`; for `Eq` it must be `fn eq(self: Self, other: Self) -> bool` (with `Self` being your type). Adjust the method signature to match, or drop the bound.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T248,
        title: "Unknown trait in a type-parameter bound",
        default_hint: "A type-parameter bound (e.g. `<T: Foo>`) names `Foo`, but no trait named `Foo` is declared or imported in this scope. Declare it (`trait Foo { … }`) or `use` the module that does. The built-in traits are `Hash` and `Eq`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T249,
        title: "Orphan trait impl",
        default_hint: "An explicit `impl Trait for Type` is only allowed when the implementing type is a record or enum declared in this program — you cannot write an explicit impl for a primitive (`i64`/`str`/`bool`) or other foreign type. The built-in `Hash`/`Eq` impls for the primitives are fixed and unoverridable. For your own record/enum, write the methods (structural satisfaction) or an `impl Trait for YourType` block. (The full cross-module authorship rule is deferred to the capability model.)",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T250,
        title: "Conflicting trait impls",
        default_hint: "The same `(trait, type)` pair is implemented by two or more explicit `impl Trait for Type` blocks. Coherence requires at most one impl of a trait for a given type — merge the blocks or delete the duplicate.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T251,
        title: "Mutation of a @ReadOnly value",
        default_hint: "A `@ReadOnly` parameter promises the function will not mutate the value passed in, so writing through it — `p.x = …`, `p[i] = …`, or a compound assignment — is rejected. Drop the `@ReadOnly` annotation if the function legitimately needs to mutate the argument, or copy the value first.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T252,
        title: "Partial @ReadOnly guarantee on a reference/view type",
        default_hint: "`@ReadOnly` on a reference or slice parameter (`&T` / `&[T]`) is a WARNING, not an error: SIGIL has no borrow/aliasing pass yet, so for an aliasable view the no-mutation promise is only partial — a different alias elsewhere could still mutate the pointee while this function holds it. The annotation IS honored as far as v1 enforces it (this function won't mutate through the handle, and the value can't escape to a mutable sink). The warning auto-clears once borrow checking lands. By-value heap params (records, `Vec`, `Map`) carry the same partial guarantee but are not per-site linted (the caveat lives in the spec).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T253,
        title: "Escape of a @ReadOnly value",
        default_hint: "A `@ReadOnly` value aliases an object the function promised not to mutate, so it may not escape to a mutable destination — returning it (or, later, passing it to a non-`@ReadOnly` parameter or storing it in a record) would hand a mutable handle to the caller. Return/pass a copy, or drop `@ReadOnly`. Returning a copy of a primitive field is fine.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T254,
        title: "Escape of a region-allocated value",
        default_hint: "A value heap-allocated inside a `region {}` block may not outlive the region: its memory is reclaimed when the block exits, so any surviving alias would dangle. The value cannot be the region's result, `return`ed, passed as a non-receiver argument, stored in a longer-lived record/place, or assigned to an outer binding. Copy a scalar out, or move the work that needs the value inside the region. (A region value MAY be read/mutated in place via the allowlisted stdlib collection methods — `v.push(x)`, `v.get(i)` — within the block.)",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T255,
        title: "Conflicting frozen and mutable arguments alias the same object",
        default_hint: "A call passes the same heap object as both a `@ReadOnly` (frozen) argument and a mutable argument: mutating it through the mutable handle would break the read-only view the frozen parameter promises. Pass a copy to one of the two arguments, or make both parameters `@ReadOnly`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T257,
        title: "Private `str_from_raw` called outside module `string`",
        default_hint: "`str_from_raw(ptr, len)` forges a `str` fat-pointer from raw memory — a wrong `len` would mint an out-of-bounds view that the `byte_at`/`substr` bounds-checks then trust — so it is stdlib-private to `string.sigil`. Build owned strings with `concat`/`join`/`itoa`, which allocate and fill the buffer for you.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T258,
        title: "Cannot construct a sealed bounded collection outside its module",
        default_hint: "Bounded collections (`BoundedVec_i64_8`, …) are construction-sealed: a direct record literal in user code could forge the length invariant (`{ len: 99 }`) that makes them safe. Build and mutate them only through their `new()` / `push` / `pop` / `get` / … API.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T259,
        title: "`for-in` iterator has a `next` of the wrong shape",
        default_hint: "The lean iterator protocol recognizes `for x in it` when `it`'s type has `next(self @Mut) -> Option<T>` — exactly one `@Mut self` parameter and an `Option<_>` return. Adjust `next` to that shape, or iterate an array / a `.iter()` view that yields it.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T260,
        title: "`break` / `continue` outside a loop",
        default_hint: "`break` and `continue` are loop-control statements; they are only valid inside a `while` or `for-in` loop body. Remove it, or move it into a loop.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T261,
        title: "Malformed tuple",
        default_hint: "A tuple needs at least two elements: `(a, b)`. A 1-tuple `(a,)` is rejected — a single parenthesized value `(a)` is just that value — as is the empty `()` and a tuple over MAX_TUPLE_ARITY (12) elements. For `let (x, y) = v;` destructuring, `v` must be a tuple whose arity matches the number of names: `let (x, y) = (1, 2);` binds two names, so the value must be a 2-tuple. v1 reads a tuple ONLY via `let (..) =` destructuring — `.0`/`.1` index access and tuple match-patterns are not yet supported.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T262,
        title: "Interpolation hole is not stringifiable",
        default_hint: "PR-E3: an interpolation hole `{e}` in an `f\"…\"` string must have type `str`, `i64`, or `bool` — a `str` hole is inserted as-is, an `i64` is converted with `.itoa()`, and a `bool` becomes \"true\"/\"false\". There is no Display/`to_string` for records, enums, or floats (AG-E1), so convert the value to one of those types first — e.g. interpolate a record's fields individually, or call a helper that returns a `str`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T263,
        title: "Cyclic type alias",
        default_hint: "PR-E4: a `type Name = …;` alias refers (directly or through a chain of other aliases) back to itself — e.g. `type A = A;` or `type A = B; type B = A;`. A type alias must resolve to a concrete, finite type. Break the cycle: point the alias at a real type (a scalar like `i64`, a record/enum, `Vec<T>`, a tuple/array/ref), not at itself or a mutually-recursive partner. A cyclic alias resolves to an opaque type rather than expanding, so uses of it will surface follow-on type errors until the cycle is removed.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T264,
        title: "Array pattern requires an array or slice scrutinee",
        default_hint: "PR P5: an array/slice destructuring pattern `[a, b, ..rest]` can only match a scrutinee whose type is an array `[T; N]` or a slice `&[T]`. Match the actual scrutinee type instead — for an enum use a variant pattern (`Variant(x)`), for a scalar use a literal/range/binding pattern, for a tuple use `let (a, b) = …` destructuring. Array patterns bind fixed positions by index and an optional `..rest` tail as a `&[T]` slice.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T265,
        title: "Array pattern length cannot match fixed-size array",
        default_hint: "PR P5: this array pattern can never match the scrutinee's fixed-size array `[T; N]`. A pattern with no `..rest` must have exactly `N` elements; a `[…, ..rest]` pattern's fixed prefix must have at most `N` elements. Adjust the element count to match `N`, or add/remove a `..rest` tail. (A slice `&[T]` has a runtime length, so any element count is accepted there.)",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T266,
        title: "Wrong-state operation",
        default_hint: "Typestate: this argument/receiver is the right protocol type but in the wrong state. The operation requires one state (e.g. `File<Open>`) and you supplied another (e.g. `File<Closed>`). Re-establish the required state via the protocol's transition operations, or call an operation valid in the current state.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T269,
        title: "Typestate construction has no pinned state",
        default_hint: "Typestate (ST-4): a typestate record was constructed with no expected type to fix its protocol state. The state is never defaulted. Pin it with a `let x: File<State> = …` annotation, a function return type, or by passing the value into a parameter of a specific state.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T275,
        title: "Typestate value stored in an aggregate",
        default_hint: "Typestate (ST-6): a typestate value is affine — storing it in a record field, enum payload, array, or generic aggregate would let you extract it twice and defeat the use-after-transition guarantee (the same smuggling channel T183/T184/T186/T242 close for capabilities). Pass the value by name through function arguments / return values instead of stashing it in an aggregate.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T276,
        title: "Undeclared state marker",
        default_hint: "Typestate (ST-5): a type argument in a protocol's state position names a marker that is not in its declared set. The state space is closed at the `state Name { … }` declaration. Use one of the declared markers, or add the marker to the `state` declaration.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T270,
        title: "Constructor arity does not match the trait's higher-kinded `Self`",
        default_hint: "HK2: this constructor was bound to a type parameter whose trait bound is higher-kinded (its `Self` is used applied, e.g. `Self<A>`), but the constructor's arity differs from that kind. A `* -> *` trait like `Functor` requires a one-parameter constructor (`Box<T>`); a two-parameter constructor (`Map<K, V>`) does not fit. Use a constructor of the matching arity.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T271,
        title: "Type name contains `__`, reserved for monomorphization names",
        default_hint: "R2 (HK3 hardening): a user-declared `record`/`enum`/`cap type` name may not contain `__` (double underscore). The compiler mangles a monomorphized generic instance to `Name__arg` (e.g. `Box<i64>` → `Box__i64`); a user type sharing that name would collide in the type registry, shadow the instance's fields, and crash AIR field lookup. Rename using a single underscore or camelCase (e.g. `Box_i64` or `BoxI64`).",
        category: Category::TypeCheck,
    },
    // ── Capabilities-as-values: `mint` ──
    CodeEntry {
        code: T272,
        title: "`mint` of a non-mintable capability type",
        default_hint: "Capabilities-as-values: `mint <Cap> for …` requires the cap type to declare a minting policy. Add `mintable_by <Authority>` to the declaration: `cap type FileAccess mintable_by Admin { read, write }`. Every cap type is non-mintable by default (fail-closed).",
        category: Category::Capability,
    },
    CodeEntry {
        code: T273,
        title: "`mint` site does not hold the minting authority",
        default_hint: "Capabilities-as-values: `mint <Cap>` requires the minting authority capability to be in scope as an immutable borrow. Take a `&cap <Authority>` parameter (matching the cap type's `mintable_by` policy) and ensure it is in scope at the mint site. You need a capability to grant a capability.",
        category: Category::Capability,
    },
    CodeEntry {
        code: T277,
        title: "`mint … for <target>` target is not a resource",
        default_hint: "Capabilities-as-values: the `for <target>` of a `mint` names the resource the capability authorizes and must be a nominal value (a record/actor type). Capabilities, primitives, references, and tuples are not valid mint targets.",
        category: Category::Capability,
    },
    CodeEntry {
        code: T279,
        title: "Diverging value (`never`) used as a value",
        default_hint: "F003 / value-position `trap()` (Tier A): a `never`-typed expression (`trap()`, an abortive `perform`) is used AS a value — bound to a `let`, stored in a tuple/array element, or passed as a call/record/enum argument. `never` is the bottom type: it has no value, so it is legal ONLY as a bare expression statement (`trap();`), where the return checker reads it as a terminating path. `trap()` aborts, it does not produce a value. To fix: use `trap();` as a standalone statement for its divergence (e.g. a guard `if bad { trap(); }` or the terminating tail of a function), and restructure so every non-diverging branch supplies the real value. This gate exists because a value-position `never` in an inference position (no expected type to reject it against) would otherwise reach AIR and ICE at the C-NEVER backstop.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T280,
        title: "Range-for bound is not `i64`",
        default_hint: "Range-for: both bounds of `for v in a..b` must be `i64` (an integer literal narrows automatically; `arr.len()` on a fixed-size array is accepted directly). Keeping the bounds single-width keeps the loop's compile-time bounds fact a plain i64 comparison — the Z3-free contract the `arr[v]` elision path relies on.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T281,
        title: "Unsupported reference or slice element type",
        default_hint: "References and slices of STRUCTURAL types — `&Fn(..)`, `&[Fn(..)]`, `&(A, B)`, `&[(A, B)]`, `&[T; N]` targets and their `&mut` forms — are not supported in v1: a function value is already a first-class reference-like value, and ref/slice-of-tuple/array/function storage has no checked runtime shape. Pass the value directly (`f: Fn(T) -> U ! { E }`, a tuple by value) or store it in a record field. Historically these shapes were SILENTLY DEGRADED (the parser dropped the element's structure, so a function element's effect row — and any typo in it — vanished without a diagnostic); they are now a hard error so no annotation can be lost.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T282,
        title: "Range pattern bound is not an integer literal",
        default_hint: "Both bounds of a `lo..=hi` match pattern must be INTEGER literals. The parser accepts a string or boolean literal there (`\"a\"..=\"z\"`, `true..=false`) because it shares one arm with ordinary literal patterns, but a range lowers to a pair of `>=` / `<=` comparisons against the scrutinee, and ordering comparisons are defined only for the machine integer types. Historically these bounds were SILENTLY COERCED to `0` during AIR lowering, which left a `Ptr >= I64` comparison that killed the build with an ICE at the wasm backstop instead of naming the real mistake. To match a set of strings, use one literal arm per case (`\"a\" => ...`); to match a boolean, use `true` / `false` arms.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T283,
        title: "`tool_main` is not `pub`",
        default_hint: "Only an externally callable function is exported from the compiled module, and a free function is externally callable only when it is declared `pub`. A private `tool_main` therefore compiles to a module with no entry point, which the runtime refuses to execute (`no tool_main entry point found`). Declare it `pub fn tool_main(...)`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T278,
        title: "Array index provably out of bounds",
        default_hint: "Refinement-typed array bounds: this index is provably out of range at compile time — a literal `k` outside `0..=N-1` for `[T; N]`, or (source c, range-for) a loop index whose composed proven interval lies entirely at or above `N`. The access would always trap when executed, so SIGIL rejects it at compile time (reject > trap). To fix: use an index in `0..=N-1`, enlarge the array `[T; N]`, or tighten the loop bound / guard the index so it is provably in range.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: R013,
        title: "Minted capability has a non-matching destination",
        default_hint: "Capabilities-as-values: a `CapMint` AIR statement must produce a value of exactly the minted cap type. Seeing this indicates an upstream lowering bug — the mint destination's value-kind did not match the cap type.",
        category: Category::Capability,
    },
    // ── PR OptTry: cross-carrier `?` mismatch ──
    CodeEntry {
        code: T241,
        title: "`?` operator used across mismatched carriers (Option vs Result)",
        default_hint: "PR OptTry / N8-OptTry: the `?`-operator's value uses one carrier type (Option<T> or Result<T, E>) but the enclosing function returns the OTHER carrier. SIGIL follows a strict same-carrier rule (AG-OptTry-A, AG-OptTry-W): `?` does NOT silently convert between Option and Result. To bridge: (a) Option<T>? in a Result-returning function — wrap the Option with `.ok_or(err)` to convert None → Err(err) before applying `?`, e.g. `let v = opt.ok_or(MyError)?;`. (b) Result<T, E>? in an Option-returning function — use `.ok()` to convert Err → None before applying `?`, e.g. `let v = res.ok()?;`. Note: T241 fires from a SINGLE canonical cross-carrier arm in `check_try_expr`, BEFORE the generic 'wrong return type' arm (T071, T181); cross-carrier mismatches MUST surface as T241 specifically so agents see actionable conversion-method hints.",
        category: Category::TypeCheck,
    },
    // ── PR P16: [T; N] array-type syntax size out of range or non-literal ──
    CodeEntry {
        code: T239,
        title: "Array-type size is out of range or not an integer literal",
        default_hint: "PR P16 / N3-P16: `[T; N]` array-type syntax admits only integer literals in `0..=65535` (inclusive). Negative literals (`[i64; -1]`), oversized literals (`[i64; 65536]`), non-literal expressions (`[i64; foo]`, `[i64; 1+2]`), or missing parts (omitted `;`, omitted `]`) all fire T239 at parse time. To fix: write the size as a non-negative integer literal, e.g. `[i64; 64]`. SIGIL does not admit const-expression sizes or const declarations in size position in this arc (AG-P16-A, AG-P16-B); use a literal. For larger arrays exceeding the 65535-element cap, redesign with a heap-allocated growable collection (Vec<T> with `! { Alloc }` effect) or split into fixed-size chunks. Note: the cap exists to prevent pathological memory exhaustion at compile time and to fit comfortably in a u32 index space; future PR can raise it if a real fixture demands.",
        category: Category::Parser,
    },
    // ── PR D: AIR-monomorphization for generic impl methods ──
    // (T235 reserved — removed pending a firing path; see codes.rs)
    // ── Type checking — actor / handler / spawn validation ──
    CodeEntry {
        code: T090,
        title: "Entry actor must be named `Main`",
        default_hint: "An `entry actor` must be declared as `entry actor Main { ... }` — rename the actor or move `entry` to a different one.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T091,
        title: "Multiple entry actors",
        default_hint: "Only one actor across the program may carry the `entry` keyword. Drop `entry` from all but one.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T092,
        title: "Actor capability state must be in `init`",
        default_hint: "Capability state fields cannot be implicitly created — they must be passed via an `init(<name>: <CapType>)` parameter.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T093,
        title: "`ask` timeout must be `i64`",
        default_hint: "`ask(msg, timeout: <i64>)` — the timeout is a number of milliseconds (i64).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T094,
        title: "Spawn init argument arity mismatch",
        default_hint: "Pass exactly the init arguments declared by the spawned actor's `init` block.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T095,
        title: "Spawn init argument type mismatch",
        default_hint: "Each spawn argument must match the declared `init` parameter type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T096,
        title: "Spawn supports cap-typed init args only",
        default_hint: "Today `spawn::<Actor>(...)` accepts only capability-typed init arguments. Restructure the actor to receive non-cap state via messages.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T097,
        title: "Message target must be `ActorRef<T>`",
        default_hint: "`x.send(...)` and `x.ask(...)` require `x: ActorRef<T>`. Pass an actor reference, not a primitive.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T098,
        title: "`ask` requires handler to return a value",
        default_hint: "`ask` is request/response — the handler must declare `-> <T>`. Use `send` for fire-and-forget, or add a return type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T099,
        title: "`ask` return type must be `Send`",
        default_hint: "Return types crossing the actor boundary must implement `Send`. Use bool, i64, ActorRef<T>, or a cap type.",
        category: Category::TypeCheck,
    },
    // ── Type checking — capability operations ──
    CodeEntry {
        code: T100,
        title: "`.restrict()` requires a capability",
        default_hint: "`x.restrict(<authority>)` requires `x` to be a capability. Pass an owned cap type rather than a primitive.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T101,
        title: "Unknown authority on `.restrict()`",
        default_hint: "The authority name does not match any declared by `cap type X { authority1, authority2, ... }`. Add the authority or fix the spelling.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T102,
        title: "`.split()` requires a capability",
        default_hint: "`x.split(<amount>)` requires `x` to be a capability. Pass a cap-typed value (typically `Fuel`).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T103,
        title: "`.split()` amount must be `i64`",
        default_hint: "The split amount is `i64`. Use a literal or cast.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T104,
        title: "`grant` requires `&cap T`, not a slice",
        default_hint: "`grant(&cap_value, ...)` — pass a single borrowed capability, not a slice or array.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T105,
        title: "`grant` requires `&cap T`",
        default_hint: "Borrow a capability with `&cap_value` (or `&self.cap`) for the first argument of `grant`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T106,
        title: "`grant` closure parameter type mismatch",
        default_hint: "The closure's parameter type must equal `&CapType` of the borrowed capability.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T107,
        title: "`grant` closure parameter arity",
        default_hint: "The `grant` closure takes exactly one parameter — the cap reference.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T108,
        title: "`grant` body must be a closure",
        default_hint: "Pass a closure as the second argument: `grant(&cap, fn(c: &CapType) -> T { ... })`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T109,
        title: "Cross-ring return error must be `ErrorCode`",
        default_hint: "Functions returning `Result` across ring boundaries must use `ErrorCode` (a `u32`). Use rich error types only within a single ring.",
        category: Category::TypeCheck,
    },
    // ── Type checking — declassify / region / message-arg details ──
    CodeEntry {
        code: T110,
        title: "`declassify` requires `Cap<Declassify>`",
        default_hint: "Pass an owned `Declassify` capability as the second argument: `declassify(value, declass_cap)`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T111,
        title: "`region` size limit must be numeric",
        default_hint: "Pass an integer literal or expression as the size argument: `region buf(1024) { ... }`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T112,
        title: "`ask` return type currently restricted",
        default_hint: "`ask` return values are limited to bool, i64, ActorRef<T>, and cap types in the current runtime ABI.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T113,
        title: "Message constructor required",
        default_hint: "`send` and `ask` expect a constructor call like `MessageName(arg1, arg2)`, not a free expression.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T114,
        title: "Message constructor must be a simple call",
        default_hint: "Use `Name(...)` — no chained calls, methods, or paths in the message constructor position.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T115,
        title: "Send/ask handler arity mismatch",
        default_hint: "Pass exactly the number of arguments the handler's `on Message(...)` signature declares.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T116,
        title: "Send/ask handler argument type mismatch",
        default_hint: "Each message argument must match the handler's declared parameter type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T117,
        title: "Send/ask argument is not `Send`",
        default_hint: "Message arguments crossing the actor boundary must implement `Send`. Use bool, i64, ActorRef<T>, or a cap type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T118,
        title: "Send/ask argument type currently restricted",
        default_hint: "Today the runtime ABI accepts bool, i64, ActorRef<T>, and cap-typed message arguments only.",
        category: Category::TypeCheck,
    },
    // ── Type checking — field access ──
    CodeEntry {
        code: T120,
        title: "Type has no such field",
        default_hint: "The named field is not declared on the record. Check the spelling or add the field to the `record` definition.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T121,
        title: "Type is not a record",
        default_hint: "Field access is only valid on `record` types. Use a different operation appropriate for this type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T122,
        title: "Cannot access field on non-record value",
        default_hint: "Field access (`.x`) is only valid on values of `record` types. Restructure to project from a record.",
        category: Category::TypeCheck,
    },
    // ── Type checking — actor state (immutable-after-init) ──
    CodeEntry {
        code: T123,
        title: "Cannot assign to actor state in a handler",
        default_hint: "Actor state is immutable after construction: a handler may only read it. Assign the field once in `init` instead. (Handler-time mutation is a separate, future feature.)",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T124,
        title: "Actor state field assigned more than once in `init`",
        default_hint: "Each actor state field must be assigned EXACTLY once in `init` — a second assignment to the same field is a double-init. Remove the redundant assignment (state is set once at construction, then immutable unless declared `mut`).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T125,
        title: "Actor state field not definitely assigned in `init`",
        default_hint: "Every actor state field must be assigned exactly once, UNCONDITIONALLY, at the top level of `init` before the actor runs — otherwise a handler would read an uninitialised (zero) value. Assign the field directly in `init` (not only inside an `if`/`while`), or remove it from the `state {}` block. (The entry actor's state is populated at bootstrap and is exempt.)",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T126,
        title: "An `init` block must not `return`",
        default_hint: "Definite assignment of a `mut` state field relies on `init` running to completion. An early `return` (bare, or guarded inside an `if`) can finish init while skipping the field's assignment, leaving it at an uninitialised (zero) value a handler would read back. Remove the `return` and assign every `mut` field unconditionally at the top level. (A `return` inside a `grant` closure is fine — it exits the closure, not init.)",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T128,
        title: "Cannot reassign a `mut` aggregate state field wholesale in a handler",
        default_hint: "A `mut` flat aggregate state field (a record/array/tuple of scalars) persists across dispatches only when mutated IN PLACE — `d.field = …` or `a[i] = …`, which write into the object allocated in `init`. A wholesale reassignment in a handler (`d = SomeRecord { … }`, `a = [ … ]`) allocates a fresh object in the per-dispatch scratch region, which the arena reset reclaims, so the field would not persist. Mutate the field in place, or assign the whole aggregate only in `init`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T127,
        title: "Closure cannot capture actor state",
        default_hint: "A closure is a lambda-lifted function with no access to the actor's state pointer, so state is unreachable inside its body. Read a data field into a local before the closure, or borrow a capability with `grant(&field, …)` (whose closure receives a `&Cap` parameter) instead of capturing the field.",
        category: Category::TypeCheck,
    },
    // ── Type checking — methods & borrows ──
    CodeEntry {
        code: T130,
        title: "Cannot call method on this type",
        default_hint: "The receiver type does not support method calls in this position. Use a free function or restructure the expression.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T131,
        title: "Method call arity mismatch",
        default_hint: "Pass exactly the number of arguments the method declares.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T132,
        title: "No such method on type",
        default_hint: "The receiver type has no method with this name. Check the spelling, or use a free function.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T133,
        title: "Cannot borrow primitive type",
        default_hint: "Only heap-allocated types (records, arrays, capabilities) can be borrowed. Pass primitives by value.",
        category: Category::TypeCheck,
    },
    // ── Type checking — array / index ──
    CodeEntry {
        code: T140,
        title: "Array element type mismatch",
        default_hint: "All elements of an array literal share the element type inferred from element 0. Three concrete fix paths: (1) cast the offending element with `<expr> as <expected>` (the message names the expected type), (2) change element 0 to match the rest, or (3) annotate the binding with the desired element type and cast as needed (e.g., `let xs: [i64] = [1 as i64, 2, 3];`).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T141,
        title: "Cannot index non-array value",
        default_hint: "Indexing (`arr[i]`) requires an array type. Use a different operation appropriate for this type.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T142,
        title: "Array index must be integer",
        default_hint: "Array indices must be integer types (`i32`/`u32`/`i64`/`u64`). Cast or change the index expression.",
        category: Category::TypeCheck,
    },
    // ── Type checking — generics & monomorphization ──
    CodeEntry {
        code: T150,
        title: "Could not infer type parameter",
        default_hint: "Use turbofish syntax to specify the type parameter explicitly: `f::<i64>(x)`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T151,
        title: "Monomorphization depth exceeded",
        default_hint: "A generic function instantiates itself (or its callees) too deeply. Restructure to break the recursion or simplify the generic chain.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T155,
        title: "Cross-module call to private function",
        default_hint: "Cross-module function calls require the callee to be `pub fn`. Either make the callee public in its defining module, or call it only from within its own module.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T156,
        title: "Module name shadowed by local variable",
        default_hint: "A `use sigil::<m>;` import is shadowed by a local binding of the same name. Either rename the local, or qualify the call as `sigil::<m>::<fn>(...)` to bypass the local-name lookup.",
        category: Category::TypeCheck,
    },
    // ── Type checking — extern declarations ──
    CodeEntry {
        code: T160,
        title: "Extern function must declare `FFI` effect",
        default_hint: "Add `! { FFI, Unsafe }` to the extern signature: `extern \"C\" fn x() -> i32 ! { FFI, Unsafe };`.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T161,
        title: "Extern function must declare `Unsafe` effect",
        default_hint: "Add `Unsafe` to the extern's effect row: `extern \"C\" fn x() -> i32 ! { FFI, Unsafe };`.",
        category: Category::TypeCheck,
    },
    // ── Type checking — supervision ──
    CodeEntry {
        code: T170,
        title: "Supervision `max_restarts` out of range",
        default_hint: "`supervision: Restart(n)` accepts n in 1..=255. Choose a value within range.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T171,
        title: "Supervision `max_restarts` must be integer literal",
        default_hint: "Pass a literal: `supervision: Restart(3)`. Variables and expressions are not supported here yet.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T172,
        title: "Supervision `max_restarts` must be compile-time literal",
        default_hint: "The `max_restarts` argument must be a compile-time integer literal so the supervision strategy is known statically.",
        category: Category::TypeCheck,
    },
    // ── Type checking — Result / try ──
    CodeEntry {
        code: T180,
        title: "`?` error type mismatch",
        default_hint: "The `?` operator's error type must match the enclosing function's `Result` error type. Convert via `.map_err(...)` or change one side.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T181,
        title: "`?` requires `Result` return type",
        default_hint: "`?` only works inside functions returning `Result<_, E>`. Change the function's return type or restructure to handle the error inline.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T182,
        title: "`?` requires a `Result` value",
        default_hint: "`?` can only be applied to `Result<T, E>` values. Wrap the value or restructure the call.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T183,
        title: "Record field cannot be capability-typed",
        default_hint: "Capabilities are linear values that must flow by name through the ownership and Z3 capability passes. Storing a cap in a record field routes it through `LoadField`, which today's Z3 treats as full authority by default — a smuggling channel for restricted caps. Pass the cap by name (or through actor messages / state) instead, or restructure the record to carry a non-cap surrogate (e.g., an i64 amount).",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T184,
        title: "Enum variant payload cannot be capability-typed",
        default_hint: "Capabilities cannot be carried by enum variant payloads. Pattern-destructure bindings (e.g., `Variant(c) => ...`) produce a fresh cap that Z3's authority tracker treats as full authority — the same aggregate-smuggling channel T183 closes for records. Pass the cap by name through actor messages or function arguments, or replace the payload with a non-cap surrogate (e.g., an i64 amount) and dispatch on a separate cap held in actor state.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T185,
        title: "Cap type declares too many authorities",
        default_hint: "Authority masks are 32-bit bitvectors in the Z3 capability layer; a cap type can declare at most 32 authorities. Either split the cap type into multiple narrower types (e.g., `cap type ReadFs { ... }` + `cap type WriteFs { ... }`), or factor the authority space differently if the policy genuinely needs >32 distinct gates.",
        category: Category::TypeCheck,
    },
    CodeEntry {
        code: T186,
        title: "Array element cannot be capability-typed",
        default_hint: "Capabilities cannot be the element type of an array. Indexing (`arr[i]`) produces a fresh cap binding that Z3's authority tracker treats as full authority — the same aggregate-smuggling channel T183 and T184 close for records and enum payloads. Pass each cap by name through actor messages or function arguments, or store the count as `[i64; N]` and look up the cap by index in actor state.",
        category: Category::TypeCheck,
    },
    // ── Internal compiler errors ──
    CodeEntry {
        code: I001,
        title: "Internal compiler invariant violation",
        default_hint: "This is a compiler bug: an internal representation violated a required invariant, such as AST/resolved-module correspondence or AIR control-flow integrity. Please file an issue with a minimal reproducer.",
        category: Category::Internal,
    },
    CodeEntry {
        code: I010,
        title: "Internal compiler error: source-name attribution lost",
        default_hint: "A diagnostic carried a `source_name` that the renderer's source set did not contain. This is a compiler bug in multi-file diagnostic plumbing (N6-W5S1). The original diagnostic is still emitted; this code is a fail-fast belt. Please file an issue with the multi-file inputs that triggered it.",
        category: Category::Internal,
    },
    CodeEntry {
        code: I011,
        title: "Internal compiler error: impl method missing from generic_impl_methods",
        default_hint: "An impl method is present in `function_sigs` but missing from `universe.generic_impl_methods`. PR D's sig-collection pass should populate both maps in lock-step for every generic impl method. This is a compiler bug; please file an issue with the offending source. The PR D `silent fallback to un-mangled callee` path is explicitly forbidden per N10-PRD — better to fail loud than re-introduce the AIR `Type::Generic` ICE.",
        category: Category::Internal,
    },
    CodeEntry {
        code: I012,
        title: "Internal compiler error: substituted_params arity mismatch with method AST",
        default_hint: "PR D's monomorphization helper expected `substituted_params.len() == method_def.params.len()` but the lengths differ. This is a sig-collection bug — the FunctionSig was built with a different param count than the source FnDef. Defensive emission per N9-PRD prevents `zip`-truncation from silently producing a malformed TypedParam list. Please file an issue with the offending impl method.",
        category: Category::Internal,
    },
    CodeEntry {
        code: I013,
        title: "Internal compiler error: formal CSIR verification failed",
        default_hint: "Compilation failed closed because typed/AIR projection, canonical CSIR encoding, the statically linked Lean runtime, or the proved version-8 joint verifier did not produce a successful verdict. This is a compiler/toolchain integrity failure, not a source policy diagnostic. Please file an issue with a minimal reproducer and the complete I013 message.",
        category: Category::Internal,
    },
    // ── Module-set / multi-file project (M-prefix, Wall 5 Step 1) ──
    CodeEntry {
        code: M001,
        title: "Filename does not match first module declaration",
        default_hint: "In project mode, each `.sigil` file must declare its first module with a name matching the filename stem. Rename either the file (`<name>.sigil`) or the leading `module <name>;` declaration so they agree. Inline `module foo { ... }` blocks declared AFTER the first module are unconstrained.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M002,
        title: "Duplicate module name across project",
        default_hint: "Module names must be unique across the whole project, whether declared as top-level `module foo;` or as inline `module foo { ... }` in another file. Rename one of the colliding modules, or merge their items into a single declaration.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M003,
        title: "No entry point found in project",
        default_hint: "A project must declare exactly one entry point: either `pub fn tool_main(input_ptr: i64, input_len: i64) -> i64` (forge ABI) OR `entry actor Main { ... }` (actor ABI). Add one to a module in the compilation set.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M004,
        title: "Multiple entry points found",
        default_hint: "Project has more than one entry candidate (`tool_main` and/or `entry actor` across modules). Pass `--entry <module-name>` to disambiguate, or remove the extra entries.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M005,
        title: "Module declares both `tool_main` and `entry actor`",
        default_hint: "A module must target one execution model: `pub fn tool_main` (ephemeral forge — fresh store per call) OR `entry actor` (persistent actor — long-lived store with supervision). These ABIs are mutually exclusive. Remove one or split into two modules.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M006,
        title: "Project mixes tool entry and actor entry",
        default_hint: "Project contains both a tool entry (`pub fn tool_main` in one module) and an actor entry (`entry actor` in another). A project must target one execution model — they are run by different drivers (`execute_ephemeral` vs the actor runtime). Pick one.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M007,
        title: "Duplicate source-file name",
        default_hint: "Each source file passed to `compile_project` must have a unique name. Check the command line for repeated filenames, or for files passed via both a directory expansion and an explicit positional argument.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M008,
        title: "Empty compilation set",
        default_hint: "`compile_project` was called with zero sources. Pass at least one `.sigil` file.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M009,
        title: "Invalid source-file name",
        default_hint: "Source file names must match `^[A-Za-z0-9_./\\-]+\\.sigil$`, contain no NUL bytes, no control characters, and no `..` path segments. Rename the file (or the path you passed) and retry.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M010,
        title: "`--entry` references unknown module",
        default_hint: "The module name passed to `--entry` was not found in the compilation set. Available modules are listed in the diagnostic message; pick one of them or drop the `--entry` flag if entry detection should be automatic.",
        category: Category::ModuleSet,
    },
    CodeEntry {
        code: M011,
        title: "Tool project declares an actor",
        default_hint: "A tool project (a compilation that declares `pub fn tool_main`) targets the ephemeral forge, which cannot run actors — the actor is dead code, and its `send`/`spawn`/capability machinery would trap. Remove the actor definition, or drop `tool_main` and build a persistent `entry actor` project instead. This fires on ANY actor in a tool project, entry or not, and on the single-file path that M005/M006 do not reach.",
        category: Category::ModuleSet,
    },
}

/// Look up a `CodeEntry` by `DiagnosticCode`. Returns `None` for unknown codes.
pub fn lookup(code: DiagnosticCode) -> Option<&'static CodeEntry> {
    CODES.iter().find(|entry| entry.code == code)
}

/// Look up a `CodeEntry` by raw code string (e.g. `"T060"`). Returns `None`
/// for unknown codes. Convenience for the MCP lookup tool and the CLI
/// `explain` subcommand, which receive the code as a string.
pub fn lookup_str(code: &str) -> Option<&'static CodeEntry> {
    CODES.iter().find(|entry| entry.code.as_str() == code)
}

/// Edit distance between two strings (classic two-row DP, char-based).
/// Shared so there is exactly ONE fuzzy-match implementation behind both the
/// MCP `sigil_lookup_error` tool and the CLI `explain` "did you mean?" hint.
pub fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut curr = vec![0usize; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        curr[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let cost = usize::from(ca != cb);
            curr[j + 1] = (prev[j + 1] + 1).min(curr[j] + 1).min(prev[j] + cost);
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[b.len()]
}

/// Up to 5 registry codes within edit-distance 2 of `target`, nearest first
/// (ties broken alphabetically). Empty when nothing is close — never a
/// misleading far-fetched suggestion. Powers the "did you mean?" hint in both
/// the MCP lookup tool and the CLI `explain` command.
pub fn did_you_mean_codes(target: &str) -> Vec<String> {
    let mut ranked: Vec<(usize, &str)> = CODES
        .iter()
        .map(|e| (levenshtein(target, e.code.as_str()), e.code.as_str()))
        .filter(|(distance, _)| *distance <= 2)
        .collect();
    ranked.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(b.1)));
    ranked
        .into_iter()
        .take(5)
        .map(|(_, c)| c.to_owned())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostics::codes::ALL_CODES;
    use proptest::prelude::*;
    use std::collections::HashSet;

    /// Format-validate a code string.
    fn is_well_formed_code(code: &str) -> bool {
        let bytes = code.as_bytes();
        bytes.len() == 4
            && bytes[0].is_ascii_uppercase()
            && bytes[1..].iter().all(u8::is_ascii_digit)
    }

    #[test]
    fn registry_is_well_formed() {
        let mut seen: HashSet<&'static str> = HashSet::new();
        for entry in CODES {
            let code_str = entry.code.as_str();
            assert!(
                is_well_formed_code(code_str),
                "code `{code_str}` does not match `^[A-Z][0-9]{{3}}$`"
            );
            assert!(!entry.title.is_empty(), "code `{code_str}` has empty title");
            assert!(
                !entry.default_hint.is_empty(),
                "code `{code_str}` has empty default_hint"
            );
            assert!(
                seen.insert(code_str),
                "duplicate code `{code_str}` in CODES table"
            );
        }
    }

    #[test]
    fn generated_constants_and_registry_are_identical() {
        let registered: Vec<DiagnosticCode> = CODES.iter().map(|entry| entry.code).collect();
        assert_eq!(ALL_CODES, registered);
    }

    proptest! {
        #[test]
        fn every_generated_code_round_trips_through_lookup(index in 0..ALL_CODES.len()) {
            let code = ALL_CODES[index];
            prop_assert_eq!(lookup(code).map(|entry| entry.code), Some(code));
            prop_assert_eq!(lookup_str(code.as_str()).map(|entry| entry.code), Some(code));
        }
    }

    #[test]
    fn did_you_mean_finds_near_codes_and_skips_far_ones() {
        // A 1-edit typo (letter O for digit 0) of a real code suggests it.
        let near = did_you_mean_codes("T06O");
        assert!(
            near.iter().any(|c| c == "T060"),
            "expected T060 in {near:?}"
        );
        // Pure garbage (and a length far from any 4-char code) yields nothing —
        // never a far-fetched suggestion.
        assert!(did_you_mean_codes("ZZZZZZ").is_empty());
        // Capped at 5 suggestions.
        assert!(did_you_mean_codes("T000").len() <= 5);
    }

    #[test]
    fn lookup_str_round_trips() {
        let first = CODES[0].code.as_str();
        assert_eq!(lookup_str(first).map(|e| e.code.as_str()), Some(first));
        assert!(lookup_str("ZZZZ").is_none());
    }

    #[test]
    fn no_z_prefix_codes_remain() {
        // The `Z` prefix was reserved for the transitional sentinel during
        // the PR 1-3 backfill. By PR 3 (Step 1 completion) it must be empty.
        for entry in CODES {
            assert!(
                !entry.code.as_str().starts_with('Z'),
                "Z-prefixed code `{}` snuck into the registry — these were transitional only",
                entry.code
            );
        }
    }
}
