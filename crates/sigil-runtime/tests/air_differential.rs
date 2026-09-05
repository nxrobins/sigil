//! Operand-exact differential coverage for the self-hosted AIR, memory, fuel,
//! WebAssembly, and execution stages.
//!
//! The Rust pipeline is the oracle. The self-hosted compiler is composed from
//! `lexer.sigil`, `parser.sigil`, `typecheck.sigil`, and `air.sigil`; unsupported
//! forms poison rather than emitting plausible bytes. Semantic preservation is
//! pinned by the corpus and evidence manifest, not by the number of Rust test
//! wrappers in this file.

#[path = "support/air_case_manifest.rs"]
mod air_case_manifest;

use sigil_compiler::CompileOptions;
use sigil_compiler::air::{self, AirFunctionKind, AirTerminator, AirType};
use sigil_compiler::compile_tool;
use sigil_compiler::fuel;
use sigil_compiler::memory;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::wasm;
use sigil_compiler::{name_resolution, type_check};
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");
const AIR: &str = include_str!("../../../selfhost/air.sigil");
const FUEL: u64 = 300_000_000;

// ─────────────────────────────────────────────────────────────────────────────
// Tool composition (clone of effect_check_differential).
// ─────────────────────────────────────────────────────────────────────────────

/// Strip the per-file `module X;` headers and concatenate into one `module tool;`.
fn ai_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let tc_defs = TYPECHECK.replace("\nmodule typecheck;\n", "\n");
    let air_defs = AIR.replace("\nmodule air;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{tc_defs}\n{air_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Oracle projection.
// ─────────────────────────────────────────────────────────────────────────────

fn airtype_tok(t: AirType) -> &'static str {
    match t {
        AirType::Unit => "Unit",
        AirType::Bool => "Bool",
        AirType::I32 => "I32",
        AirType::U32 => "U32",
        AirType::I64 => "I64",
        AirType::U64 => "U64",
        AirType::F64 => "F64",
        AirType::Ptr => "Ptr",
    }
}

/// The bare name = the tail after the LAST `::` (`m::add` -> `add`, `m::Pt__get` ->
/// `Pt__get`, a bare `add` -> `add`).
fn bare_tail(full: &str) -> &str {
    full.rsplit("::").next().unwrap_or(full)
}

/// Compile + lower `src` through the real pipeline. The corpus is parse-clean +
/// type-clean (the AG-R7 analog; ET-AIR-3): a parse/type error would let the oracle
/// "recover" and pass vacuously while the self-host walks a different tree.
fn lower_oracle(src: &str) -> air::AirProgram {
    let source = SourceFile::new("<air-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(
        pdiags.is_empty(),
        "SH-AIR fixture must be parse-clean: {src:?} -> {:?}",
        pdiags
            .iter()
            .map(|d| d.code().to_string())
            .collect::<Vec<_>>()
    );
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    let (typed, _reg) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .expect("fixture must type-check (the corpus is type-clean)");
    air::lower(&typed)
}

/// Cases retained from the retired skeleton projection. The final Wasm lane
/// classifies each one as byte-exact or explicitly poisoned.
const RETIRED_LANE_CORPUS: &[(&str, &str)] = &[
    (
        "add: straight-line return",
        "module m;\nfn add(a: i64, b: i64) -> i64 { return a + b; }\n",
    ),
    (
        "scalars + str/record Ptr + unit return",
        "module m;\nrecord R { v: i64 }\nfn sc(a: i32, b: u32, c: u64, d: bool, e: f64, g: i64) -> i32 { return a; }\nfn strp(s: str) -> bool { return true; }\nfn recp(r: R) -> i64 { return 0; }\nfn unitret(x: i64) { let y: i64 = x; }\n",
    ),
    (
        "both-branches-return (merge None)",
        "module m;\nfn br(c: bool) -> i64 { if c { return 1; } else { return 2; } }\n",
    ),
    (
        "empty branches + trailing return",
        "module m;\nfn eb(c: bool) -> i64 { if c { } else { } return 0; }\n",
    ),
    (
        "if with trailing statements (merge present)",
        "module m;\nfn it(c: bool) -> i64 { if c { let a: i64 = 1; } else { let b: i64 = 2; } return 0; }\n",
    ),
    (
        "nested if in while + trailing return",
        "module m;\nfn nw(c: bool) -> i64 { while c { if c { return 1; } else { } } return 0; }\n",
    ),
    (
        "while-only fn (Unit ret)",
        "module m;\nfn wl(c: bool) { while c { let a: i64 = 1; } }\n",
    ),
    (
        "one branch returns, other falls through (Unit ret)",
        "module m;\nfn of(c: bool) { if c { return; } else { let b: i64 = 2; } }\n",
    ),
    (
        "sequential sibling ifs",
        "module m;\nfn sq(c: bool) -> i64 { if c { let a: i64 = 1; } else { } if c { return 2; } else { return 3; } }\n",
    ),
    (
        "calls in expr position add no blocks",
        "module m;\nfn g() -> i64 { return 1; }\nfn ex() -> i64 { let x: i64 = g(); g(); return x; }\n",
    ),
    (
        "multi-fn manifest module",
        "module m;\n\
         fn f_add(a: i64, b: i64) -> i64 { return a + b; }\n\
         fn f_sub(a: i64, b: i64) -> i64 { return a - b; }\n\
         fn f_id(a: i64) -> i64 { return a; }\n\
         fn f_branch(c: bool) -> i64 { if c { return 1; } else { return 2; } }\n\
         fn f_loopy(c: bool) -> i64 { while c { let x: i64 = 1; } return 0; }\n\
         fn f_unit(x: i64) { let y: i64 = x; }\n\
         fn f_bool(b: bool) -> bool { return b; }\n\
         fn f_float(x: f64) -> f64 { return x; }\n\
         fn f_nested(c: bool) -> i64 { while c { if c { return 1; } else { } } return 0; }\n",
    ),
    (
        "impl method kept + free fn",
        "module m;\nrecord Pt { x: i64 }\nimpl Pt { fn get(self: Pt) -> i64 { return self.x; } }\nfn plain(a: i64) -> i64 { return a; }\n",
    ),
    (
        "multi-module free fns",
        "module a;\nfn aa(x: i64) -> i64 { return x; }\n#[ring(outer)]\nmodule b;\nfn bb(y: i64) -> i64 { return y; }\n",
    ),
    (
        "if-in-if + sibling while",
        "module m;\nfn dn(c: bool) -> i64 { if c { if c { let a: i64 = 1; } else { let b: i64 = 2; } } else { } while c { let w: i64 = 1; } return 0; }\n",
    ),
    (
        "nested while-in-while",
        "module m;\nfn ww(c: bool, d: bool) { while c { while d { let x: i64 = 1; } } }\n",
    ),
    (
        "if with while-then + assign-else (no remainder)",
        "module m;\nfn iw(c: bool, d: bool) { if c { while d { let x: i64 = 1; } } else { let y: i64 = 2; } }\n",
    ),
    (
        "three-level nested if (no remainder)",
        "module m;\nfn ti(a: bool, b: bool, e: bool) { if a { if b { if e { let x: i64 = 1; } else { } } else { } } else { } }\n",
    ),
    (
        "while body: if-with-remainder + trailing",
        "module m;\nfn wir(c: bool, d: bool) { while c { if d { let a: i64 = 1; } else { let b: i64 = 2; } let e: i64 = 3; } }\n",
    ),
    (
        "composite Ptr params: ref/tuple/array",
        "module m;\nfn refp(x: &i64) -> i64 { return 0; }\nfn tupp(p: (i64, i64)) -> i64 { return 0; }\nfn arrp(a: [i64; 4]) -> i64 { return 0; }\n",
    ),
    ("empty fn body", "module m;\nfn ef() { }\n"),
    (
        "while with empty body",
        "module m;\nfn web(c: bool) { while c { } }\n",
    ),
    (
        "while containing return",
        "module m;\nfn wr(c: bool) -> i64 { while c { return 1; } return 0; }\n",
    ),
    (
        "if-in-else with remainder (nested merges)",
        "module m;\nfn ier(a: bool, b: bool) -> i64 { if a { let x: i64 = 1; } else { if b { let y: i64 = 2; } else { } let z: i64 = 3; } let w: i64 = 4; return w; }\n",
    ),
    (
        "match: all-return + wildcard catch-all",
        "module m;\nfn classify(x: i64) -> i64 { match x { 0 => { return 100; }, 1 => { return 200; }, _ => { return 0; } } }\n",
    ),
    (
        "match: bool-exhaustive (is_last literal, no wildcard)",
        "module m;\nfn boolm(b: bool) -> i64 { match b { true => { return 1; }, false => { return 2; } } }\n",
    ),
    (
        "match: fall-through arms + remainder",
        "module m;\nfn fm(x: i64) -> i64 { let mut y: i64 = 0; match x { 0 => { y = 100; }, 1 => { y = 200; }, _ => { y = 9; } } return y; }\n",
    ),
    (
        "match: one arm + wildcard, fall-through + remainder",
        "module m;\nfn mr(x: i64) -> i64 { match x { 0 => { let a: i64 = 1; }, _ => { let b: i64 = 2; } } return 5; }\n",
    ),
    (
        "match: fall-through arms, last statement (Unit)",
        "module m;\nfn ml(x: i64) { match x { 0 => { let a: i64 = 1; }, _ => { let b: i64 = 2; } } }\n",
    ),
    (
        "match in while body",
        "module m;\nfn mw(x: i64, c: bool) -> i64 { while c { match x { 0 => { return 1; }, _ => { let z: i64 = 2; } } } return 0; }\n",
    ),
    (
        "match in if-then-arm",
        "module m;\nfn nm(x: i64, c: bool) -> i64 { if c { match x { 0 => { return 1; }, _ => { return 2; } } } else { return 3; } }\n",
    ),
    (
        "if in match arm",
        "module m;\nfn im(x: i64, c: bool) -> i64 { match x { 0 => { if c { return 1; } else { return 2; } }, _ => { return 0; } } }\n",
    ),
    (
        "match: string-literal + wildcard",
        "module m;\nfn sm(s: str) -> i64 { match s { \"a\" => { return 1; }, _ => { return 0; } } }\n",
    ),
    (
        "match: single wildcard arm",
        "module m;\nfn sw(x: i64) -> i64 { match x { _ => { return 0; } } }\n",
    ),
    (
        "match-in-match (nested Dispatch)",
        "module m;\nfn mm(x: i64, y: i64) -> i64 { match x { 0 => { match y { 1 => { return 1; }, _ => { return 2; } } }, _ => { return 0; } } }\n",
    ),
    (
        "match: 4-literal chain + wildcard",
        "module m;\nfn c4(x: i64) -> i64 { match x { 0 => { return 1; }, 1 => { return 2; }, 2 => { return 3; }, 3 => { return 4; }, _ => { return 0; } } }\n",
    ),
    (
        "match: while-body arm + remainder",
        "module m;\nfn wb(x: i64, c: bool) -> i64 { match x { 0 => { while c { let z: i64 = 1; } }, _ => { return 0; } } return 9; }\n",
    ),
    (
        "match in while in if (deep)",
        "module m;\nfn dn2(x: i64, c: bool) -> i64 { if c { while c { match x { 0 => { return 1; }, _ => { let z: i64 = 2; } } } } else { } return 0; }\n",
    ),
    (
        "for-in straight-line body",
        "module m;\nfn fs(arr: [i64; 4]) { for x in arr { let z: i64 = x; } }\n",
    ),
    (
        "for-in with immediate break",
        "module m;\nfn fb(arr: [i64; 4]) { for x in arr { break; } }\n",
    ),
    (
        "for-in with immediate continue",
        "module m;\nfn fc(arr: [i64; 4]) { for x in arr { continue; } }\n",
    ),
    (
        "while with break",
        "module m;\nfn wbk(c: bool) { while c { break; } }\n",
    ),
    (
        "while with continue",
        "module m;\nfn wct(c: bool) { while c { continue; } }\n",
    ),
    (
        "for-in with if-then-break",
        "module m;\nfn fib(arr: [i64; 4], c: bool) { for x in arr { if c { break; } else { } } }\n",
    ),
    (
        "for-in then remainder",
        "module m;\nfn ftr(arr: [i64; 4]) -> i64 { for x in arr { let z: i64 = x; } return 0; }\n",
    ),
    (
        "nested for-in",
        "module m;\nfn nf(a: [i64; 4], b: [i64; 4]) { for x in a { for y in b { let z: i64 = x; } } }\n",
    ),
    (
        "for-in if break-else-continue",
        "module m;\nfn fbc(arr: [i64; 4], c: bool) { for x in arr { if c { break; } else { continue; } } }\n",
    ),
    (
        "while if-continue + remainder",
        "module m;\nfn wic(c: bool, d: bool) { while c { if d { continue; } else { } let z: i64 = 1; } }\n",
    ),
    (
        "break then dead code",
        "module m;\nfn btd(c: bool) { while c { break; let z: i64 = 1; } }\n",
    ),
    (
        "range-for sum",
        "module m;\nfn rr(n: i64) -> i64 { let mut t: i64 = 0; for i in 0..n { t = t + i; } return t; }\n",
    ),
    (
        "match in for-in body",
        "module m;\nfn mf(arr: [i64; 4]) { for x in arr { match x { 0 => { let z: i64 = 1; }, _ => { let w: i64 = 2; } } } }\n",
    ),
    (
        "break/continue in match in for-in",
        "module m;\nfn bcm(arr: [i64; 4], c: bool) { for x in arr { match c { true => { break; }, false => { continue; } } } }\n",
    ),
    (
        "for-in inside a match arm",
        "module m;\nfn fma(x: i64, arr: [i64; 4]) -> i64 { match x { 0 => { for y in arr { let z: i64 = y; } }, _ => { return 0; } } return 9; }\n",
    ),
    (
        "trait impl method",
        "module m;\nrecord Sh { v: i64 }\ntrait Show { fn area(self: Sh) -> i64; }\nimpl Show for Sh { fn area(self: Sh) -> i64 { return self.v; } }\n",
    ),
    (
        "impl method: if body",
        "module m;\nrecord Pt { x: i64 }\nimpl Pt { fn pick(self: Pt, c: bool) -> i64 { if c { return 1; } else { return 2; } } }\n",
    ),
    (
        "impl method: while body",
        "module m;\nrecord C { n: i64 }\nimpl C { fn run(self: C, c: bool) -> i64 { while c { let z: i64 = 1; } return 0; } }\n",
    ),
    (
        "impl method: match body",
        "module m;\nrecord P { v: i64 }\nimpl P { fn cl(self: P, x: i64) -> i64 { match x { 0 => { return 1; }, _ => { return 0; } } } }\n",
    ),
    (
        "impl method: for-in body",
        "module m;\nrecord A { n: i64 }\nimpl A { fn sm(self: A, arr: [i64; 4]) -> i64 { for y in arr { let z: i64 = y; } return 0; } }\n",
    ),
    (
        "two impl methods in one block",
        "module m;\nrecord Tw { x: i64 }\nimpl Tw { fn a(self: Tw) -> i64 { return 1; } fn b(self: Tw) -> i64 { return 2; } }\n",
    ),
    (
        "multi-module impl",
        "module a;\nfn aa(x: i64) -> i64 { return x; }\n#[ring(outer)]\nmodule b;\nrecord Q { v: i64 }\nimpl Q { fn g(self: Q) -> i64 { return self.v; } }\n",
    ),
    (
        "unit-return method",
        "module m;\nrecord Uu { x: i64 }\nimpl Uu { fn touch(self: Uu) { let z: i64 = self.x; } }\n",
    ),
    (
        "method body: break in for-in",
        "module m;\nrecord Af { n: i64 }\nimpl Af { fn f(self: Af, arr: [i64; 4], c: bool) -> i64 { for y in arr { if c { break; } else { } } return 0; } }\n",
    ),
    (
        "closure: single",
        "module m;\nfn host() -> i64 { let g = fn(x: i64) -> i64 { return x; }; return 0; }\n",
    ),
    (
        "closure: capturing",
        "module m;\nfn host(n: i64) -> i64 { let g = fn(x: i64) -> i64 { return x + n; }; return 0; }\n",
    ),
    (
        "closure: unit ret",
        "module m;\nfn host() -> i64 { let g = fn(x: i64) { let z: i64 = x; }; return 0; }\n",
    ),
    (
        "closure: if body",
        "module m;\nfn host() -> i64 { let g = fn(x: i64, d: bool) -> i64 { if d { return x; } else { return 0; } }; return 0; }\n",
    ),
    (
        "closure: for-in body",
        "module m;\nfn host() -> i64 { let g = fn(a: [i64; 4]) -> i64 { for y in a { let z: i64 = y; } return 0; }; return 0; }\n",
    ),
    (
        "closure: two in one fn",
        "module m;\nfn host() -> i64 { let g = fn(x: i64) -> i64 { return x; }; let h = fn(y: i64) -> i64 { return y; }; return 0; }\n",
    ),
    (
        "closure: nested",
        "module m;\nfn host() -> i64 { let g = fn(x: i64) -> i64 { let h = fn(y: i64) -> i64 { return y; }; return x; }; return 0; }\n",
    ),
    (
        "closure: source order across fns",
        "module m;\nfn a() -> i64 { let g = fn(x: i64, d: bool) -> i64 { if d { return x; } else { return 0; } }; return 0; }\nrecord Pt { x: i64 }\nimpl Pt { fn m1(self: Pt) -> i64 { let h = fn(y: i64) -> i64 { return y; }; return 0; } }\nfn c() -> i64 { let k = fn() { let z: i64 = 0; }; return 0; }\n",
    ),
    (
        "closure: in impl method",
        "module m;\nrecord Pt { x: i64 }\nimpl Pt { fn mm(self: Pt) -> i64 { let g = fn(x: i64) -> i64 { return x; }; return 0; } }\n",
    ),
    (
        "closure: multi-module",
        "module a;\nfn af() -> i64 { let g = fn(x: i64) -> i64 { return x; }; return 0; }\n#[ring(outer)]\nmodule b;\nfn bf() -> i64 { let h = fn(y: i64) -> i64 { return y; }; return 0; }\n",
    ),
    (
        "closure: match body",
        "module m;\nfn host() -> i64 { let g = fn(x: i64) -> i64 { match x { 0 => { return 1; }, _ => { return 0; } } }; return 0; }\n",
    ),
    (
        "closure: for-in inside impl method",
        "module m;\nrecord Pt { x: i64 }\nimpl Pt { fn mm(self: Pt) -> i64 { let g = fn(a: [i64; 4]) -> i64 { for y in a { let z: i64 = y; } return 0; }; return 0; } }\n",
    ),
    (
        "closure: Fn-typed let",
        "module m;\nfn host() -> i64 { let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return x; }; return 0; }\n",
    ),
    (
        "actor: single handler",
        "module m;\nactor A { on Ping(v: i64) -> i64 { return v; } }\n",
    ),
    (
        "actor: scalar init",
        "module m;\nactor A { init(n: i64) {} on Ping(v: i64) -> i64 { return v; } }\n",
    ),
    (
        "actor: two handlers",
        "module m;\nactor A { on Ping(v: i64) -> i64 { return v; } on Pong(w: i64, b: bool) -> i64 { return w; } }\n",
    ),
    (
        "actor: handler if body",
        "module m;\nactor A { on Ping(v: i64, c: bool) -> i64 { if c { return v; } else { return 0; } } }\n",
    ),
    (
        "actor: unit-ret handler",
        "module m;\nactor A { on Ping(v: i64) { let z: i64 = v; } }\n",
    ),
    (
        "actor: stateful",
        "module m;\nactor A { state { count: i64 } on Ping(v: i64) -> i64 { return v; } }\n",
    ),
    (
        "actor: two actors",
        "module m;\nactor A { on Ping(v: i64) -> i64 { return v; } }\nactor B { on Pong(w: i64) -> i64 { return w; } }\n",
    ),
    (
        "actor: handler for-in",
        "module m;\nactor A { on Ping(arr: [i64; 4]) -> i64 { for y in arr { let z: i64 = y; } return 0; } }\n",
    ),
    (
        "actor: handler match body",
        "module m;\nactor A { on Ping(v: i64) -> i64 { match v { 0 => { return 1; }, _ => { return 0; } } } }\n",
    ),
    (
        "actor: zero-param init",
        "module m;\nactor A { init() {} on Ping(v: i64) -> i64 { return v; } }\n",
    ),
    (
        "actor: closure in handler",
        "module m;\nactor A { on Ping(v: i64) -> i64 { let g = fn(x: i64) -> i64 { return x; }; return v; } }\n",
    ),
    (
        "actor: closure counter spans handler",
        "module m;\nfn host() -> i64 { let f = fn(a: i64) -> i64 { return a; }; return 0; }\nactor A { on Ping(v: i64) -> i64 { let g = fn(x: i64) -> i64 { return x; }; return v; } }\n",
    ),
    (
        "actor: kitchen sink",
        "module m;\nfn freefn(a: i64) -> i64 { return a; }\nrecord R { x: i64 }\nimpl R { fn m(self: R) -> i64 { return self.x; } }\nactor A { init(n: i64) {} on Ping(v: i64) -> i64 { return v; } }\n",
    ),
    (
        "dead remainder after both-return if",
        "module m;\nfn drr(a: i64, c: bool) -> i64 { if c { return a; } else { return 0; } let z: i64 = 1; return z; }\n",
    ),
    (
        "nested dead remainder",
        "module m;\nfn ndr(a: i64, c: bool, d: bool) -> i64 { if c { if d { return a; } else { return 0; } let z: i64 = a; return z; } else { return 1; } }\n",
    ),
    (
        "both-break keeps remainder",
        "module m;\nfn bbk(a: i64, c: bool) -> i64 { while c { if a < 1 { break; } else { break; } let z: i64 = 1; } return 0; }\n",
    ),
    ("trap sole", "module m;\nfn f() -> i64 { trap(); }\n"),
    (
        "trap after partial return",
        "module m;\nfn f(c: bool) -> i64 { if c { return 1; } trap(); }\n",
    ),
    (
        "trap one branch",
        "module m;\nfn f(c: bool) -> i64 { if c { trap(); } else { return 1; } }\n",
    ),
    (
        "trap both branches diverge",
        "module m;\nfn f(c: bool) -> i64 { if c { trap(); } else { trap(); } }\n",
    ),
    (
        "trap in while body",
        "module m;\nfn f(c: bool) -> i64 { while c { trap(); } return 0; }\n",
    ),
    (
        "trap in match arm",
        "module m;\nfn f(m: i64) -> i64 { match m { 0 => { trap(); }, _ => { return 1; } } }\n",
    ),
    (
        "trap in for-in body",
        "module m;\nfn f(arr: [i64; 3]) -> i64 { for x in arr { trap(); } return 0; }\n",
    ),
    (
        "trap then dead code",
        "module m;\nfn f() -> i64 { trap(); return 0; }\n",
    ),
];

const RETIRED_LANE_POISON_CASES: &[&str] = &[
    "match: string-literal + wildcard",
    "closure: single",
    "closure: capturing",
    "closure: unit ret",
    "closure: if body",
    "closure: for-in body",
    "closure: two in one fn",
    "closure: nested",
    "closure: source order across fns",
    "closure: in impl method",
    "closure: multi-module",
    "closure: match body",
    "closure: for-in inside impl method",
    "closure: Fn-typed let",
    "actor: stateful",
    "actor: closure in handler",
    "actor: closure counter spans handler",
];
const RETIRED_LANE_OUTER_EXACT_CASES: &[&str] = &["multi-module free fns", "multi-module impl"];

/// Scalar straight-line fixtures exercised through exact AIR, memory, fuel, and Wasm.
const BODY_CORPUS: &[(&str, &str)] = &[
    (
        "ret_local",
        "module m;\nfn f(a: i64) -> i64 { return a; }\n",
    ),
    ("ret_lit", "module m;\nfn f() -> i64 { return 5; }\n"),
    (
        "ret_bin_ll",
        "module m;\nfn f(a: i64, b: i64) -> i64 { return a + b; }\n",
    ),
    (
        "ret_bin_lit",
        "module m;\nfn f(a: i64) -> i64 { return a + 1; }\n",
    ),
    (
        "ret_lit_lit",
        "module m;\nfn f() -> i64 { return 1 + 2; }\n",
    ),
    (
        "let_local",
        "module m;\nfn f(a: i64) -> i64 { let z: i64 = a; return z; }\n",
    ),
    (
        "let_lit",
        "module m;\nfn f() -> i64 { let z: i64 = 5; return z; }\n",
    ),
    (
        "let_bin_ll",
        "module m;\nfn f(a: i64, b: i64) -> i64 { let z: i64 = a + b; return z; }\n",
    ),
    (
        "let_bin_lit",
        "module m;\nfn f(a: i64) -> i64 { let z: i64 = a + 1; return z; }\n",
    ),
    (
        "let_lit_lit",
        "module m;\nfn f() -> i64 { let z: i64 = 1 + 2; return z; }\n",
    ),
    (
        "assign_local",
        "module m;\nfn f(a: i64) -> i64 { let mut z: i64 = 0; z = a; return z; }\n",
    ),
    (
        "assign_bin_lit",
        "module m;\nfn f(a: i64) -> i64 { let mut z: i64 = 0; z = a + 1; return z; }\n",
    ),
    (
        "expr_stmt",
        "module m;\nfn f(a: i64) -> i64 { a + 1; return a; }\n",
    ),
    ("unit_ret", "module m;\nfn f(a: i64) { let z: i64 = a; }\n"),
    ("bool", "module m;\nfn f(a: bool) -> bool { return a; }\n"),
    (
        "f64",
        "module m;\nfn f(a: f64, b: f64) -> f64 { return a + b; }\n",
    ),
    (
        "chain",
        "module m;\nfn f(a: i64) -> i64 { let x: i64 = a + 1; let y: i64 = x + 2; return y; }\n",
    ),
    (
        "actor_handler",
        "module m;\nactor A { on Ping(v: i64) -> i64 { let z: i64 = v + 1; return z; } }\n",
    ),
    // ── adversarial-sweep folds (SH-AIR-6a) ──
    // a non-add scalar op (division traps natively in wasm, NOT a Call) → single Assign.
    (
        "div",
        "module m;\nfn f(a: i64, b: i64) -> i64 { return a / b; }\n",
    ),
    // a compound assign `z += 1` — the parser desugars to `z = z + 1` (a flat binary INTO z), so it
    // takes the `into` path: let z=a (1) + materialize 1 (1) + binary-into-z (1) = 3 Assigns.
    (
        "compound_assign",
        "module m;\nfn f(a: i64) -> i64 { let mut z: i64 = a; z += 1; return z; }\n",
    ),
    // a chain of bare local-copies (each `let w = <local>` is one Var-copy Assign).
    (
        "local_copy_chain",
        "module m;\nfn f(a: i64) -> i64 { let z: i64 = a; let w: i64 = z; return w; }\n",
    ),
];
const BODY_CF_CORPUS: &[(&str, &str)] = &[
    (
        "cf_if_else",
        "module m;\nfn f(a: i64, c: bool) -> i64 { if c { return a; } else { return 0; } }\n",
    ),
    (
        "cf_if_rem",
        "module m;\nfn f(a: i64, c: bool) -> i64 { let mut z: i64 = 0; if c { z = a; } else { z = 1; } return z; }\n",
    ),
    (
        "cf_if_comp",
        "module m;\nfn f(a: i64, b: i64) -> i64 { if a < b { return a; } else { return b; } }\n",
    ),
    (
        "cf_while",
        "module m;\nfn f(a: i64, c: bool) -> i64 { while c { let z: i64 = a; } return 0; }\n",
    ),
    (
        "cf_while_unit",
        "module m;\nfn f(c: bool) { while c { } }\n",
    ),
    (
        "cf_while_comp",
        "module m;\nfn f(a: i64, b: i64) -> i64 { while a < b { let z: i64 = a; } return 0; }\n",
    ),
    (
        "cf_nested_if2",
        "module m;\nfn f(a: i64, c: bool, d: bool) -> i64 { if c { if d { return a; } else { return 0; } } else { return 1; } }\n",
    ),
    (
        "cf_while_break",
        "module m;\nfn f(a: i64, c: bool, d: bool) -> i64 { while c { if d { break; } else { } let z: i64 = 1; } return 0; }\n",
    ),
    (
        "cf_while_body_if",
        "module m;\nfn f(a: i64, c: bool, d: bool) -> i64 { while c { let p: i64 = a; if d { let q: i64 = 1; } else { } let r: i64 = 2; } return 0; }\n",
    ),
    // ── adversarial-sweep folds (SH-AIR-6b) ──
    // the cur-leak stress: an if-with-remainder (non-empty merge) INSIDE a while body.
    (
        "cf_if_rem_in_while",
        "module m;\nfn f(a: i64, c: bool, d: bool) -> i64 { while c { let p: i64 = a; if d { let q: i64 = 1; } else { let r: i64 = 2; } let s: i64 = 3; } return 0; }\n",
    ),
    // a while INSIDE an if branch.
    (
        "cf_while_in_if",
        "module m;\nfn f(a: i64, c: bool) -> i64 { if c { while c { let z: i64 = a; } return 1; } else { return 0; } }\n",
    ),
    // continue (distinct from break) inside a while.
    (
        "cf_continue",
        "module m;\nfn f(a: i64, c: bool, d: bool) -> i64 { while c { if d { continue; } else { } let z: i64 = 1; } return 0; }\n",
    ),
    // multiple stmts before the if (head accumulation).
    (
        "cf_multi_head",
        "module m;\nfn f(a: i64, c: bool) -> i64 { let x: i64 = a; let y: i64 = 1; if c { return x; } else { return y; } }\n",
    ),
    // a computed while cond + a body that materializes (cond-mat in COND, body Assigns).
    (
        "cf_comp_while_body",
        "module m;\nfn f(a: i64, b: i64) -> i64 { while a < b { let z: i64 = a + 1; } return 0; }\n",
    ),
    // DEAD-REMAINDER: a both-RETURN inner if + a (dead) remainder inside the outer then-branch. The
    // type-checker drops the dead remainder, so the oracle emits NO merge block; the body lane elides
    // it too (the ai_emit_body_blocks fix). Regression guard — before the fix, the shadow over-emitted.
    (
        "cf_nested_dead_remainder",
        "module m;\nfn f(a: i64, c: bool, d: bool) -> i64 { if c { if d { return a; } else { return 0; } let z: i64 = a; return z; } else { return 1; } }\n",
    ),
    // SH-AIR trap (body lane): a `trap();` block projects `Assign,TrapIf` (the __trap mat + the TrapIf stmt).
    ("t_sole", "module m;\nfn f() -> i64 { trap(); }\n"),
    (
        "t_after_ret",
        "module m;\nfn f(c: bool) -> i64 { if c { return 1; } trap(); }\n",
    ),
    (
        "t_one_branch",
        "module m;\nfn f(c: bool) -> i64 { if c { trap(); } else { return 1; } }\n",
    ),
    (
        "t_both_branch",
        "module m;\nfn f(c: bool) -> i64 { if c { trap(); } else { trap(); } }\n",
    ),
    (
        "t_in_while",
        "module m;\nfn f(c: bool) -> i64 { while c { trap(); } return 0; }\n",
    ),
    (
        "t_in_match",
        "module m;\nfn f(m: i64) -> i64 { match m { 0 => { trap(); }, _ => { return 1; } } }\n",
    ),
    (
        "t_in_forin",
        "module m;\nfn f(arr: [i64; 3]) -> i64 { for x in arr { trap(); } return 0; }\n",
    ),
    // sweep (body): dead code after trap is elided — same projection as t_sole, different source.
    (
        "t_dead_code",
        "module m;\nfn f() -> i64 { trap(); return 0; }\n",
    ),
];
const BODY_MATCH_CORPUS: &[(&str, &str)] = &[
    (
        "bm_lit_wild",
        "module m;\nfn f(x: i64) -> i64 { match x { 0 => { return 1; }, _ => { return 0; } } }\n",
    ),
    (
        "bm_two_lit_wild",
        "module m;\nfn f(x: i64) -> i64 { match x { 0 => { return 1; }, 1 => { return 2; }, _ => { return 0; } } }\n",
    ),
    (
        "bm_bool_exhaustive",
        "module m;\nfn f(b: bool) -> i64 { match b { true => { return 1; }, false => { return 2; } } }\n",
    ),
    (
        "bm_fallthrough_rem",
        "module m;\nfn f(x: i64) -> i64 { let mut y: i64 = 0; match x { 0 => { y = 100; }, _ => { y = 9; } } return y; }\n",
    ),
    (
        "bm_last_stmt_unit",
        "module m;\nfn f(x: i64) { match x { 0 => { let a: i64 = 1; }, _ => { let b: i64 = 2; } } }\n",
    ),
    (
        "bm_if_in_arm",
        "module m;\nfn f(x: i64, c: bool) -> i64 { match x { 0 => { if c { return 1; } else { return 2; } }, _ => { return 0; } } }\n",
    ),
    (
        "bm_single_wild",
        "module m;\nfn f(x: i64) -> i64 { match x { _ => { return 0; } } }\n",
    ),
    (
        "bm_4lit",
        "module m;\nfn f(x: i64) -> i64 { match x { 0 => { return 1; }, 1 => { return 2; }, 2 => { return 3; }, _ => { return 0; } } }\n",
    ),
    // folded from the adversarial sweep: a FLAT-BINARY scrutinee (`a + 1`) — the wrapper carries the
    // 2-`Assign` scrutinee mat (Phase-0 finding: the shadow admits it; no wrapper-count fence needed).
    (
        "bm_flat_binary_scrut",
        "module m;\nfn f(a: i64) -> i64 { match a + 1 { 0 => { return 1; }, _ => { return 0; } } }\n",
    ),
    // a NESTED match (match in an arm body) — exercises the ai_emit_body_blocks / ai_match_body_in_subset
    // mutual recursion through P_K_MATCH on BOTH sides.
    (
        "bm_nested_match",
        "module m;\nfn f(x: i64, y: i64) -> i64 { match x { 0 => { match y { 1 => { return 1; }, _ => { return 2; } } }, _ => { return 3; } } }\n",
    ),
    // a `break` inside a match arm inside a while — the arm body's break (return-code 2) must propagate.
    (
        "bm_break_in_arm",
        "module m;\nfn f(x: i64, c: bool) -> i64 { while c { match x { 0 => { break; }, _ => { let z: i64 = 1; } } } return 0; }\n",
    ),
];
const BODY_FORIN_CORPUS: &[(&str, &str)] = &[
    (
        "bf_basic",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { for y in arr { let z: i64 = y; } return 0; }\n",
    ),
    // a preceding `let mut s` rides the HEAD; an accumulating assign body; return-local empty exit.
    (
        "bf_sum",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { let mut s: i64 = 0; for y in arr { s = s + y; } return s; }\n",
    ),
    (
        "bf_empty",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { for y in arr { } return 0; }\n",
    ),
    // nested for-in (the inner for-in is the outer body's only stmt; both recurse).
    (
        "bf_nest",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { for y in arr { for z in arr { let w: i64 = z; } } return 0; }\n",
    ),
    // a `continue` inside the for-in body INJECTS the increment (2 Assigns) before the Jump.
    (
        "bf_cont",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { for y in arr { if y > 0 { continue; } else { } let z: i64 = y; } return 0; }\n",
    ),
    // a `break` injects NOTHING (the then-branch is an empty segment).
    (
        "bf_break",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { for y in arr { if y > 0 { break; } else { } let z: i64 = y; } return 0; }\n",
    ),
    // a for-in nested inside an if branch.
    (
        "bf_in_if",
        "module m;\nfn f(arr: [i64; 4], c: bool) -> i64 { if c { for y in arr { let z: i64 = y; } } else { } return 0; }\n",
    ),
    // a for-in nested inside a match arm.
    (
        "bf_in_match",
        "module m;\nfn f(arr: [i64; 4], x: i64) -> i64 { match x { 0 => { for y in arr { let z: i64 = y; } }, _ => { } } return 0; }\n",
    ),
    // folded from the adversarial sweep: a WHILE inside a for-in — the while-continue must NOT inject
    // (the while is the innermost loop), even though we are inside a for-in. The hardest in_forin case.
    (
        "bf_while_in",
        "module m;\nfn f(arr: [i64; 4], c: bool) -> i64 { for y in arr { while c { if c { continue; } else { } let z: i64 = y; } } return 0; }\n",
    ),
    // a for-in inside a WHILE — the for-in-continue DOES inject (the dual of bf_while_in).
    (
        "bf_in_while",
        "module m;\nfn f(arr: [i64; 4], c: bool) -> i64 { while c { for y in arr { if y > 0 { continue; } else { } let z: i64 = y; } } return 0; }\n",
    ),
    // two Ptr params (a record + the array) — the record is untouched; the param-gate relaxation keeps
    // both, and `forin_loads_ok` only sees the for-in's loads.
    (
        "bf_rec_and_arr",
        "module m;\nrecord R { x: i64 }\nfn f(r: R, arr: [i64; 4]) -> i64 { for y in arr { let z: i64 = y; } return 0; }\n",
    ),
    // a match INSIDE the for-in body (SH-AIR-6c ⊂ 6d, the dual of bf_in_match).
    (
        "bf_match_in",
        "module m;\nfn f(arr: [i64; 4], x: i64) -> i64 { for y in arr { match x { 0 => { let z: i64 = y; }, _ => { let w: i64 = 1; } } } return 0; }\n",
    ),
];
const BODY_FORRANGE_CORPUS: &[(&str, &str)] = &[
    // the basic accumulating sum over a literal range.
    (
        "rf_basic",
        "module m;\nfn f() -> i64 { let mut acc: i64 = 0; for i in 0..5 { acc = acc + i; } return acc; }\n",
    ),
    // RF-M2 ELIDED read: `a[i]` under `0..3` over `[i64; 3]` (K == N) — bare LoadDynamic.
    (
        "rf_elide",
        "module m;\nfn f(a: [i64; 3]) -> i64 { let mut acc: i64 = 0; for i in 0..3 { let v: i64 = a[i]; acc = acc + v; } return acc; }\n",
    ),
    // NOT elided (straddle): K=5 > N=3 — the full runtime bounds chain stays.
    (
        "rf_straddle",
        "module m;\nfn f(a: [i64; 3]) -> i64 { let mut acc: i64 = 0; for i in 0..5 { let v: i64 = a[i]; acc = acc + v; } return acc; }\n",
    ),
    // the len-bound headline: `0..a.len()` — the CHECKER substitutes the static size, so
    // the oracle pre-header mats the CONSTANT 3 (no len load) and the read elides.
    (
        "rf_len",
        "module m;\nfn f(a: [i64; 3]) -> i64 { let mut acc: i64 = 0; for i in 0..a.len() { let v: i64 = a[i]; acc = acc + v; } return acc; }\n",
    ),
    // the array is a LET (array literal), not a param — the decl-site N resolution.
    (
        "rf_let_arr",
        "module m;\nfn f() -> i64 { let a: [i64; 3] = [10, 20, 30]; let mut acc: i64 = 0; for i in 0..3 { let v: i64 = a[i]; acc = acc + v; } return acc; }\n",
    ),
    // break: injects NOTHING (the then-branch is an empty segment ending in Jump-to-exit).
    (
        "rf_break",
        "module m;\nfn f() -> i64 { let mut acc: i64 = 0; for i in 0..9 { if i > 3 { break; } else { } acc = acc + i; } return acc; }\n",
    ),
    // continue: injects the I64 increment (2 Assigns) before the Jump-to-cond.
    (
        "rf_cont",
        "module m;\nfn f() -> i64 { let mut acc: i64 = 0; for i in 0..9 { if i > 3 { continue; } else { } acc = acc + i; } return acc; }\n",
    ),
    // nested distinct-name range loops.
    (
        "rf_nest",
        "module m;\nfn f() -> i64 { let mut acc: i64 = 0; for i in 0..3 { for j in 0..4 { acc = acc + j; } acc = acc + i; } return acc; }\n",
    ),
    // VARIABLE bounds: lowering-only (no elision anywhere — no fact without literal-0 start).
    (
        "rf_var_bounds",
        "module m;\nfn f(s: i64, e: i64) -> i64 { let mut acc: i64 = 0; for i in s..e { acc = acc + i; } return acc; }\n",
    ),
    // a range-for inside a WHILE — the range-continue DOES inject (I64).
    (
        "rf_in_while",
        "module m;\nfn f(c: bool) -> i64 { let mut acc: i64 = 0; while c { for i in 0..4 { if i > 1 { continue; } else { } acc = acc + i; } } return acc; }\n",
    ),
    // a WHILE inside a range-for — the while-continue must NOT inject.
    (
        "rf_while_in",
        "module m;\nfn f(c: bool) -> i64 { let mut acc: i64 = 0; for i in 0..4 { while c { if c { continue; } else { } acc = acc + 1; } acc = acc + i; } return acc; }\n",
    ),
    // a range-for (I64 frame) nested in a for-in (U32 frame): the inner continue's
    // injected `__one` takes the INNER frame's width — I64.
    (
        "rf_in_forin",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { let mut acc: i64 = 0; for y in arr { for i in 0..2 { if i > 0 { continue; } else { } acc = acc + y; } } return acc; }\n",
    ),
    // an ELIDED index WRITE under the covered loop.
    (
        "rf_write",
        "module m;\nfn f(a: [i64; 3] @Mut) -> i64 { for i in 0..3 { a[i] = i; } return 0; }\n",
    ),
];
const BODY_FIELD_CORPUS: &[(&str, &str)] = &[
    (
        "fld_let",
        "module m;\nrecord R { x: i64 }\nfn f(r: R) -> i64 { let z: i64 = r.x; return z; }\n",
    ),
    (
        "fld_ret",
        "module m;\nrecord R { x: i64 }\nfn f(r: R) -> i64 { return r.x; }\n",
    ),
    (
        "fld_2nd",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(r: R) -> i64 { return r.y; }\n",
    ),
    (
        "fld_two",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(r: R) -> i64 { let a: i64 = r.x; let b: i64 = r.y; return a; }\n",
    ),
    // a u32 first field — offset 0 + ty U32, identical to the for-in len-load EXCEPT jumps_to_loop=false
    // (the census case proving the body_stmts_recognized discriminator is loop-context, not offset/ty).
    (
        "fld_u32",
        "module m;\nrecord R { x: u32 }\nfn f(r: R) -> u32 { return r.x; }\n",
    ),
    // the record-copy let-LOCAL source: `let r: R = pr;` (-> 1 Assign) then `r.x` (-> 1 LoadField).
    (
        "fld_local",
        "module m;\nrecord R { x: i64 }\nfn f(pr: R) -> i64 { let r: R = pr; return r.x; }\n",
    ),
    (
        "fld_in_if",
        "module m;\nrecord R { x: i64 }\nfn f(r: R, c: bool) -> i64 { if c { return r.x; } else { return 0; } }\n",
    ),
    (
        "fld_in_while",
        "module m;\nrecord R { x: i64 }\nfn f(r: R, c: bool) -> i64 { while c { let z: i64 = r.x; } return 0; }\n",
    ),
    (
        "fld_in_match",
        "module m;\nrecord R { x: i64 }\nfn f(r: R, m: i64) -> i64 { match m { 0 => { let z: i64 = r.x; }, _ => { } } return 0; }\n",
    ),
    // the strongest: a field-read LoadField in a for-in body alongside the for-in len-LoadField
    // (jumps_to_loop) + element-LoadDynamic — exercises the body_stmts_recognized discriminator.
    (
        "fld_in_forin",
        "module m;\nrecord R { x: i64 }\nfn f(r: R, arr: [i64; 4]) -> i64 { for y in arr { let z: i64 = r.x; } return 0; }\n",
    ),
    // folded from the adversarial sweep: TWO distinct record params (per-name binding resolution).
    (
        "fld_two_recs",
        "module m;\nrecord A { p: i64 }\nrecord B { q: i64 }\nfn f(a: A, b: B) -> i64 { let x: i64 = a.p; let y: i64 = b.q; return x; }\n",
    ),
    // a field read as an ASSIGN value (distinct from a let value).
    (
        "fld_assign_val",
        "module m;\nrecord R { x: i64 }\nfn f(r: R) -> i64 { let mut z: i64 = 0; z = r.x; return z; }\n",
    ),
    // const/variant non-collision: f (field read) kept; g (enum unit variant E::A) is NOT a field read
    // and is dropped on both sides — so the parity SET is just f's line.
    (
        "fld_const_coexist",
        "module m;\nrecord R { x: i64 }\nenum E { A }\nfn f(r: R) -> i64 { return r.x; }\nfn g() -> E { return E::A; }\n",
    ),
];
const BODY_WRITE_CORPUS: &[(&str, &str)] = &[
    (
        "w_var",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut, v: i64) -> i64 { r.x = v; return 0; }\n",
    ),
    (
        "w_lit",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut) -> i64 { r.x = 5; return 0; }\n",
    ),
    (
        "w_2nd",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(r: R @Mut, v: i64) -> i64 { r.y = v; return 0; }\n",
    ),
    (
        "w_then_read",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut, v: i64) -> i64 { r.x = v; return r.x; }\n",
    ),
    (
        "w_two",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(r: R @Mut, v: i64) -> i64 { r.x = v; r.y = v; return 0; }\n",
    ),
    (
        "w_in_if",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut, c: bool, v: i64) -> i64 { if c { r.x = v; } else { } return 0; }\n",
    ),
    (
        "w_in_while",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut, c: bool, v: i64) -> i64 { while c { r.x = v; } return 0; }\n",
    ),
    // a field-to-field copy: the RHS is a field-read WHOLE value (a to_var leaf -> 1 LoadField) + StoreField.
    (
        "w_field_to_field",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(r: R @Mut) -> i64 { r.x = r.y; return 0; }\n",
    ),
    // the @Mut-param field READ (slice-1 territory — works because tc_seed_params binds the @Mut param).
    (
        "w_read_mut",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut) -> i64 { return r.x; }\n",
    ),
    // folded from the adversarial sweep: a flat-binary RHS -> the a+b mat Assign + StoreField.
    (
        "w_binary_rhs",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut, a: i64, b: i64) -> i64 { r.x = a + b; return 0; }\n",
    ),
    // a mixed field READ + field WRITE (LoadField then StoreField).
    (
        "w_read_write",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(r: R @Mut) -> i64 { let z: i64 = r.x; r.y = z; return 0; }\n",
    ),
    // a write inside a for-in body — a StoreField alongside the for-in len/elem loads (the
    // body_stmts_recognized StoreField arm co-existing with the for-in arms).
    (
        "w_in_forin",
        "module m;\nrecord R { x: i64 }\nfn f(r: R @Mut, arr: [i64; 4]) -> i64 { for y in arr { r.x = y; } return 0; }\n",
    ),
];
const BODY_CALL_CORPUS: &[(&str, &str)] = &[
    (
        "c_local",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { let z: i64 = g(a); return z; }\n",
    ),
    (
        "c_ret",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { return g(a); }\n",
    ),
    (
        "c_lit",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f() -> i64 { let z: i64 = g(5); return z; }\n",
    ),
    (
        "c_two",
        "module m;\nfn g(a: i64, b: i64) -> i64 { return a; }\nfn f(a: i64, b: i64) -> i64 { let z: i64 = g(a, b); return z; }\n",
    ),
    (
        "c_binary_arg",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { let z: i64 = g(a + 1); return z; }\n",
    ),
    (
        "c_field_arg",
        "module m;\nrecord R { x: i64 }\nfn g(a: i64) -> i64 { return a; }\nfn f(r: R) -> i64 { let z: i64 = g(r.x); return z; }\n",
    ),
    (
        "c_noarg",
        "module m;\nfn g() -> i64 { return 7; }\nfn f() -> i64 { let z: i64 = g(); return z; }\n",
    ),
    // a NESTED call `g(h(a))` -> Call,Call (the inner call materializes to-var first).
    (
        "c_nested",
        "module m;\nfn h(a: i64) -> i64 { return a; }\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { let z: i64 = g(h(a)); return z; }\n",
    ),
    (
        "c_in_if",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64, c: bool) -> i64 { if c { return g(a); } else { return 0; } }\n",
    ),
    (
        "c_in_while",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64, c: bool) -> i64 { while c { let z: i64 = g(a); } return 0; }\n",
    ),
    // RECURSION: `f` calls `f` (f is in sigs, so tc_sig_find resolves it).
    (
        "c_recursion",
        "module m;\nfn f(a: i64) -> i64 { if a > 0 { let z: i64 = f(a); return z; } else { return 0; } }\n",
    ),
    // folded from the adversarial sweep: a call as a field-write RHS (reg2 + reg3 compose).
    (
        "c_into_field",
        "module m;\nrecord R { x: i64 }\nfn g(a: i64) -> i64 { return a; }\nfn f(r: R @Mut, a: i64) -> i64 { r.x = g(a); return 0; }\n",
    ),
    // a deeply NESTED call g(h(k(a))) -> Call,Call,Call (the emit recursion).
    (
        "c_deep_nest",
        "module m;\nfn k(a: i64) -> i64 { return a; }\nfn h(a: i64) -> i64 { return a; }\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { let z: i64 = g(h(k(a))); return z; }\n",
    ),
    // heterogeneous args: a field-read arg + a literal arg -> LoadField,Assign,Call.
    (
        "c_mixed_args",
        "module m;\nrecord R { x: i64 }\nfn g(a: i64, b: i64) -> i64 { return a; }\nfn f(r: R) -> i64 { let z: i64 = g(r.x, 5); return z; }\n",
    ),
    // a call in a for-in body — a Call alongside the for-in len/elem loads.
    (
        "c_in_forin",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64, arr: [i64; 4]) -> i64 { for y in arr { let z: i64 = g(y); } return 0; }\n",
    ),
];
const BODY_CONSTRUCT_CORPUS: &[(&str, &str)] = &[
    (
        "ct_lit_read",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f() -> i64 { let r: R = R { x: 1, y: 2 }; return r.x; }\n",
    ),
    // the no-read latent hole: all-`Assign`, the oracle already keeps it; slice 4 makes the shadow agree.
    (
        "ct_no_read",
        "module m;\nrecord R { x: i64 }\nfn f(c: bool) -> i64 { let r: R = R { x: 1 }; return 0; }\n",
    ),
    (
        "ct_local_fields",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(a: i64, b: i64) -> i64 { let r: R = R { x: a, y: b }; return r.x; }\n",
    ),
    (
        "ct_one_field",
        "module m;\nrecord R { x: i64 }\nfn f(a: i64) -> i64 { let r: R = R { x: a }; return r.x; }\n",
    ),
    // a field-read FIELD VALUE: R{x: s.x} -> LoadField (s.x) + Assign (RecordConstruct).
    (
        "ct_field_val",
        "module m;\nrecord R { x: i64 }\nfn f(s: R) -> i64 { let r: R = R { x: s.x }; return r.x; }\n",
    ),
    // folded from the adversarial sweep: a CALL field value (reg3 + reg4 compose).
    (
        "ct_call_field",
        "module m;\nrecord R { x: i64 }\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { let r: R = R { x: g(a) }; return r.x; }\n",
    ),
    // a construct as a CALL ARG (reg3 + reg4 compose the other way): field mats + construct Assign + Call.
    (
        "ct_as_arg",
        "module m;\nrecord R { x: i64 }\nfn g(r: R) -> i64 { return r.x; }\nfn f() -> i64 { let z: i64 = g(R { x: 1 }); return z; }\n",
    ),
    // a NESTED record construct `R{ inner: I{..} }` — composes via the ai_value_in_subset recursion.
    (
        "ct_nested",
        "module m;\nrecord I { v: i64 }\nrecord R { inner: I }\nfn f(a: i64) -> i64 { let r: R = R { inner: I { v: a } }; return 0; }\n",
    ),
    // SH-AIR-8 sweep: a 3-LEVEL nested construct — each level expands (FuelDecrement,BumpAlloc,StoreField),
    // innermost FIRST (the recursion composes to arbitrary depth).
    (
        "ct_deep_nest",
        "module m;\nrecord I { v: i64 }\nrecord J { i: I }\nrecord R { j: J }\nfn f(a: i64) -> i64 { let r: R = R { j: J { i: I { v: a } } }; return a; }\n",
    ),
    // SH-AIR-8 sweep: a construct in a for-in BODY (reg8 × SH-AIR-6d compose; parity-only, multi-block).
    (
        "ct_in_forin",
        "module m;\nrecord R { x: i64 }\nfn f(a: i64, brr: [i64; 3]) -> i64 { for y in brr { let r: R = R { x: a }; } return a; }\n",
    ),
];
const BODY_ARRAY_CORPUS: &[(&str, &str)] = &[
    (
        "arr_lit2",
        "module m;\nfn f() -> i64 { let a: [i64; 2] = [1, 2]; return 0; }\n",
    ),
    (
        "arr_local2",
        "module m;\nfn f(x: i64, y: i64) -> i64 { let a: [i64; 2] = [x, y]; return 0; }\n",
    ),
    (
        "arr_lit1",
        "module m;\nfn f() -> i64 { let a: [i64; 1] = [7]; return 0; }\n",
    ),
    (
        "arr_mixed",
        "module m;\nfn f(x: i64) -> i64 { let a: [i64; 2] = [x, 9]; return 0; }\n",
    ),
    // E-ELEM recursion: a CALL element (array -> reg3 call).
    (
        "arr_nest_call",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { let arr: [i64; 1] = [g(a)]; return 0; }\n",
    ),
    // E-ELEM recursion: a RECORD-construct element (array -> reg4 construct); a depth-1 nest.
    (
        "arr_nest_rec",
        "module m;\nrecord R { x: i64 }\nfn f() -> i64 { let a: [R; 1] = [R { x: 1 }]; return 0; }\n",
    ),
    // folded from the adversarial sweep — the empty array (0 elements): just the len store, no element loop.
    (
        "arr_empty",
        "module m;\nfn f() -> i64 { let a: [i64; 0] = []; return 0; }\n",
    ),
    // folded from the sweep — a 2-element record-construct array (each element its own construct expansion).
    (
        "arr_of_rec2",
        "module m;\nrecord R { x: i64 }\nfn f() -> i64 { let a: [R; 2] = [R { x: 1 }, R { x: 2 }]; return 0; }\n",
    ),
    // folded from the sweep — an array-of-arrays (depth-2 aggregate; each inner array its own expansion).
    (
        "arr_of_arr",
        "module m;\nfn f() -> i64 { let a: [[i64; 1]; 2] = [[1], [2]]; return 0; }\n",
    ),
];
const BODY_STRING_CORPUS: &[(&str, &str)] = &[
    (
        "str_local",
        "module m;\nfn f(a: i64) -> i64 { let s: str = \"x\"; return a; }\n",
    ),
    (
        "str_two",
        "module m;\nfn f(a: i64) -> i64 { let s: str = \"x\"; let t: str = \"yy\"; return a; }\n",
    ),
    // string as a record field value (mats-FIRST: the header before the record BumpAlloc).
    (
        "str_in_rec",
        "module m;\nrecord R { s: str }\nfn f() -> i64 { let r: R = R { s: \"x\" }; return 0; }\n",
    ),
    // string as a call arg (reg3 compose): header mats, then the Call.
    (
        "str_as_arg",
        "module m;\nfn g(s: str) -> i64 { return 0; }\nfn f() -> i64 { let z: i64 = g(\"x\"); return z; }\n",
    ),
    // 2a×2b compose: a string ELEMENT of an array literal (array header + per-element string header).
    (
        "str_in_arr",
        "module m;\nfn f() -> i64 { let a: [str; 2] = [\"x\", \"yy\"]; return 0; }\n",
    ),
    // folded from the sweep — the empty string `""` (byte_len 0): SAME fixed 6-token header.
    (
        "str_empty",
        "module m;\nfn f(a: i64) -> i64 { let s: str = \"\"; return a; }\n",
    ),
    // folded from the sweep — two string fields of a record (both headers mats-first, then the record).
    (
        "str_two_rec",
        "module m;\nrecord R { s: str, t: str }\nfn f() -> i64 { let r: R = R { s: \"x\", t: \"y\" }; return 0; }\n",
    ),
];
const BODY_ENUM_CORPUS: &[(&str, &str)] = &[
    (
        "en_unit",
        "module m;\nenum E { A, B(i64) }\nfn f() -> i64 { let e: E = E::A; return 0; }\n",
    ),
    (
        "en_lit",
        "module m;\nenum E { A, B(i64) }\nfn f() -> i64 { let e: E = E::B(5); return 0; }\n",
    ),
    (
        "en_local",
        "module m;\nenum E { A, B(i64) }\nfn f(a: i64) -> i64 { let e: E = E::B(a); return 0; }\n",
    ),
    (
        "en_two",
        "module m;\nenum E { A, B(i64, i64) }\nfn f(a: i64) -> i64 { let e: E = E::B(a, 7); return 0; }\n",
    ),
    // enum as a record field value (enum → reg4 record compose).
    (
        "en_in_rec",
        "module m;\nenum E { A, B(i64) }\nrecord R { e: E }\nfn f() -> i64 { let r: R = R { e: E::A }; return 0; }\n",
    ),
    // enum as a call arg (enum → reg3 call compose).
    (
        "en_as_arg",
        "module m;\nenum E { A, B(i64) }\nfn g(e: E) -> i64 { return 0; }\nfn f() -> i64 { let z: i64 = g(E::A); return z; }\n",
    ),
    // folded from the sweep — an array of enums (2a×2c: array header + per-element enum construct).
    (
        "en_in_arr",
        "module m;\nenum E { A, B(i64) }\nfn f() -> i64 { let a: [E; 2] = [E::A, E::B(1)]; return 0; }\n",
    ),
    // folded from the sweep — a RECORD-payload variant `E::B(P{..})` (enum → reg4 record payload compose).
    (
        "en_rec_payload",
        "module m;\nrecord P { x: i64 }\nenum E { A, B(P) }\nfn f() -> i64 { let e: E = E::B(P { x: 1 }); return 0; }\n",
    ),
];
const BODY_INDEX_CORPUS: &[(&str, &str)] = &[
    (
        "ix_read",
        "module m;\nfn f(arr: [i64; 4], i: i64) -> i64 { let z: i64 = arr[i]; return z; }\n",
    ),
    (
        "ix_u32",
        "module m;\nfn f(arr: [i64; 4], i: u32) -> i64 { let z: i64 = arr[i]; return z; }\n",
    ),
    (
        "ix_const",
        "module m;\nfn f(arr: [i64; 4]) -> i64 { let z: i64 = arr[0]; return z; }\n",
    ),
    (
        "ix_ret",
        "module m;\nfn f(arr: [i64; 4], i: i64) -> i64 { return arr[i]; }\n",
    ),
    (
        "ix_two",
        "module m;\nfn f(arr: [i64; 4], i: i64, j: i64) -> i64 { let a: i64 = arr[i]; let b: i64 = arr[j]; return a; }\n",
    ),
    (
        "ix_write",
        "module m;\nfn f(arr: [i64; 4] @Mut, i: i64, v: i64) -> i64 { arr[i] = v; return 0; }\n",
    ),
    (
        "ix_write_lit",
        "module m;\nfn f(arr: [i64; 4] @Mut, i: i64) -> i64 { arr[i] = 5; return 0; }\n",
    ),
    // SH-AIR-8 (#442): a LITERAL-index WRITE `arr[0] = v` — the oracle elides the bounds check (parity-only).
    (
        "ix_write_const",
        "module m;\nfn f(arr: [i64; 4] @Mut, v: i64) -> i64 { arr[0] = v; return 0; }\n",
    ),
    (
        "ix_as_arg",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(arr: [i64; 4], i: i64) -> i64 { let z: i64 = g(arr[i]); return z; }\n",
    ),
    // composition (parity-validated; no pin): index read in a match arm, index write in an if.
    (
        "ix_in_match",
        "module m;\nfn f(arr: [i64; 4], i: i64, m: i64) -> i64 { match m { 0 => { let z: i64 = arr[i]; }, _ => { } } return 0; }\n",
    ),
    (
        "ix_write_in_if",
        "module m;\nfn f(arr: [i64; 4] @Mut, i: i64, v: i64, c: bool) -> i64 { if c { arr[i] = v; } else { } return 0; }\n",
    ),
];
// The operand-exact render (docs/specs/sh-air.md).
// One line per fn: `tail|params|ret|locals|blocks` — params/locals as space-separated `vN:Ty`;
// blocks in PUSH order (ids explicit — the match snap proves emission order ≠ id order:
// a Dispatch's exit block is ALLOCATED before the arm chain but PUSHED last), `#`-separated;
// each block `bID:stmt;stmt>TERM`. EXCLUDED fields, each with a reason: `entry_block` (an
// invariant — asserted == 0 instead of rendered), ring/kind/export_name (covered at the final
// module boundary), value_kinds/debug_names/debug_spans (non-semantic metadata).
// ─────────────────────────────────────────────────────────────────────────────

/// SH-AIR-CV-0 (X8): a `StrLit` renders RAW, so its content must be ASCII-printable and free of
/// the format's structural delimiters (`|` `#` `;` `>`) and `\`. Both renderers (this one and the
/// future selfhost serializer) share this rule — an injectable literal panics at render time on
/// BOTH sides, so two different programs can never render equal.
fn cv_check_strlit(s: &str) {
    let ok = s
        .chars()
        .all(|c| (' '..='~').contains(&c) && !matches!(c, '|' | '#' | ';' | '>' | '\\'));
    assert!(
        ok,
        "CV render (X8): StrLit contains a format delimiter / non-ASCII-printable: {s:?}"
    );
}

/// SH-AIR-CV-0: render ONE AirValue. X7: every covered variant destructured with NO `..` — a new
/// field in air.rs breaks this compile. The match is exhaustive (no wildcard), so a NEW AirValue
/// variant is a compile error, not a silent skip. FloatLit is out of the CV surface
/// (AG-CV-FLOATLIT: Rust `{:?}` f64 vs SIGIL float formatting would diverge; zero float literals
/// exist in any fixture) — it panics loud if ever fixtured.
fn cv_render_value(val: &air::AirValue) -> String {
    match val {
        air::AirValue::IntLit(n) => format!("Int({n})"),
        air::AirValue::FloatLit(x) => {
            panic!("CV render: FloatLit({x}) is out of the CV surface (AG-CV-FLOATLIT)")
        }
        air::AirValue::BoolLit(b) => format!("Bool({b})"),
        air::AirValue::StrLit(s) => {
            cv_check_strlit(s);
            format!("Str({s})")
        }
        air::AirValue::UnitLit => "Unit".to_string(),
        air::AirValue::Var(v) => format!("Var(v{})", v.0),
        air::AirValue::Binary { lhs, op, rhs } => format!("Bin(v{} {op:?} v{})", lhs.0, rhs.0),
        air::AirValue::RecordConstruct { fields } => {
            let fs = fields
                .iter()
                .map(|(n, v)| format!("{n}=v{}", v.0))
                .collect::<Vec<_>>()
                .join(" ");
            format!("Rec({fs})")
        }
    }
}

/// SH-AIR-CV-0: render ONE AirStmt. X7: the covered variants destructure with NO `..` (a new
/// field breaks the compile); X2: an uncovered variant reaching the renderer panics naming
/// itself — never a silent omission. Covered = exactly the KIND-lane alphabet.
fn cv_render_stmt(s: &air::AirStmt) -> String {
    match s {
        air::AirStmt::Assign { dst, val } => format!("As v{}={}", dst.0, cv_render_value(val)),
        air::AirStmt::LoadField {
            dst,
            base_ptr,
            offset,
            ty,
        } => format!(
            "LF v{}<-v{}@{}:{}",
            dst.0,
            base_ptr.0,
            offset,
            airtype_tok(*ty)
        ),
        air::AirStmt::StoreField {
            base_ptr,
            offset,
            val,
            ty,
        } => format!(
            "SF v{}@{}<-v{}:{}",
            base_ptr.0,
            offset,
            val.0,
            airtype_tok(*ty)
        ),
        air::AirStmt::LoadDynamic {
            dst,
            base_ptr,
            index,
            elem_size,
            ty,
            offset,
        } => format!(
            "LD v{}<-v{}[v{}]*{}+{}:{}",
            dst.0,
            base_ptr.0,
            index.0,
            elem_size,
            offset,
            airtype_tok(*ty)
        ),
        air::AirStmt::StoreDynamic {
            base_ptr,
            index,
            elem_size,
            val,
            ty,
            offset,
        } => format!(
            "SD v{}[v{}]*{}+{}<-v{}:{}",
            base_ptr.0,
            index.0,
            elem_size,
            offset,
            val.0,
            airtype_tok(*ty)
        ),
        air::AirStmt::Call { dst, func, args } => {
            let a = args
                .iter()
                .map(|v| format!("v{}", v.0))
                .collect::<Vec<_>>()
                .join(" ");
            match dst {
                Some(d) => format!("Call v{}=f{}({a})", d.0, func.0),
                None => format!("Call f{}({a})", func.0),
            }
        }
        air::AirStmt::WrapI64 { dst, src } => format!("Wrap v{}<-v{}", dst.0, src.0),
        air::AirStmt::TrapIf { cond } => format!("Trap v{}", cond.0),
        air::AirStmt::FuelDecrement { amount } => format!("Fuel {amount}"),
        // PPS-0: `persistent` is deliberately NOT rendered. The census compares the Rust
        // lowering against the self-hosted one over state-FREE inputs, where the flag is
        // always false; rendering it would change every BA line and break parity for a
        // dimension the differential corpus cannot exercise.
        air::AirStmt::BumpAlloc {
            dst,
            size_bytes,
            align,
            persistent: _,
        } => format!("BA v{} {}/{}", dst.0, size_bytes, align),
        other => {
            panic!("CV render (X2): uncovered AirStmt variant reached the renderer: {other:?}")
        }
    }
}

/// SH-AIR-CV-0: render ONE terminator. Exhaustive with NO wildcard — a new AirTerminator variant
/// in air.rs is a compile error here (the X2 mechanism, compiler-enforced).
fn cv_render_term(t: &AirTerminator) -> String {
    match t {
        AirTerminator::Return(Some(v)) => format!("Ret v{}", v.0),
        AirTerminator::Return(None) => "Ret".to_string(),
        AirTerminator::Jump(b) => format!("Jmp b{}", b.0),
        AirTerminator::Loop {
            cond,
            body_block,
            exit_block,
        } => format!("Loop v{} b{} b{}", cond.0, body_block.0, exit_block.0),
        AirTerminator::Branch {
            cond,
            then_block,
            else_block,
            merge_block,
        } => {
            let m = match merge_block {
                Some(b) => format!("b{}", b.0),
                None => "_".to_string(),
            };
            format!("Br v{} b{} b{} m={}", cond.0, then_block.0, else_block.0, m)
        }
        AirTerminator::Dispatch { start, exit } => format!("Disp b{} b{}", start.0, exit.0),
        AirTerminator::Unreachable => "Unr".to_string(),
    }
}

/// SH-AIR-CV-0: render ONE AirFunction to the CV format line. `entry_block == 0` is asserted (an
/// invariant, not rendered); blocks serialize in PUSH order with explicit ids.
fn cv_render_fn(f: &air::AirFunction) -> String {
    assert_eq!(
        f.entry_block.0, 0,
        "CV render: entry_block invariant broken for {}",
        f.name
    );
    let tail = bare_tail(&f.name);
    let params = f
        .params
        .iter()
        .map(|(v, t)| format!("v{}:{}", v.0, airtype_tok(*t)))
        .collect::<Vec<_>>()
        .join(" ");
    let locals = f
        .locals
        .iter()
        .map(|(v, t)| format!("v{}:{}", v.0, airtype_tok(*t)))
        .collect::<Vec<_>>()
        .join(" ");
    let blocks = f
        .blocks
        .iter()
        .map(|b| {
            let sts = b
                .stmts
                .iter()
                .map(cv_render_stmt)
                .collect::<Vec<_>>()
                .join(";");
            format!("b{}:{}>{}", b.id.0, sts, cv_render_term(&b.terminator))
        })
        .collect::<Vec<_>>()
        .join("#");
    format!(
        "{}|{}|{}|{}|{}",
        tail,
        params,
        airtype_tok(f.ret),
        locals,
        blocks
    )
}

/// SH-AIR-CV-0: the CV-lane ORACLE projection — every non-ModuleInit fn rendered operand-exactly,
/// sorted. X3 (staging): `post_memory=false` renders `air::lower` output (CV-1..4);
/// `post_memory=true` renders after `memory::lower` (CV-5 ONLY).
fn oracle_cv_projection(src: &str, post_memory: bool) -> Vec<String> {
    let mut program = lower_oracle(src);
    if post_memory {
        let (p, _) = memory::lower(program);
        program = p;
    }
    let mut v: Vec<String> = program
        .functions
        .iter()
        .filter(|f| !matches!(f.kind, AirFunctionKind::ModuleInit))
        .map(cv_render_fn)
        .collect();
    v.sort();
    v
}

/// SH-SURFACE ST-1: BARE (unqualified) enum variants — `A` (unit) / `B(x)` (payload), which the
/// oracle lowers byte-identically to `E::A` / `E::B(x)`. Covered in the CV + wasm + execution
/// lanes only (AG-ST1-KINDLANE: the KIND stmt-kind lane stays qualified-only — bare and qualified
/// produce identical kind sequences, so it adds no discriminating power). Variant names are
/// enum-unique (AG-ST-AMBIGVARIANT).
const BODY_BARE_ENUM_CORPUS: &[(&str, &str)] = &[
    (
        "bare_unit",
        "module m;\nenum E { A, B(i64) }\nfn f() -> E { return A; }\n",
    ),
    (
        "bare_payload",
        "module m;\nenum E { A, B(i64) }\nfn f(x: i64) -> E { return B(x); }\n",
    ),
    (
        "bare_unit_let",
        "module m;\nenum E { A, B(i64) }\nfn f() -> i64 { let e: E = A; return 0; }\n",
    ),
    (
        "bare_payload_let",
        "module m;\nenum E { A, B(i64) }\nfn f(x: i64) -> i64 { let e: E = B(x); return 0; }\n",
    ),
    (
        "bare_local_shadows_variant",
        "module m;\nenum E { A, B(i64) }\nfn f(A: i64) -> i64 { return A; }\n",
    ),
    (
        "bare_in_if",
        "module m;\nenum E { A, B(i64) }\nfn f(c: bool, x: i64) -> E { if c { return A; } else { return B(x); } }\n",
    ),
    (
        "bare_freefn_beats_variant",
        "module m;\nenum E { A, B(i64) }\nfn A() -> i64 { return 7; }\nfn f() -> i64 { return A(); }\n",
    ),
    (
        "bare_two_enums_disjoint",
        "module m;\nenum E { A, B(i64) }\nenum F { C, D(i64) }\nfn f(x: i64) -> F { return D(x); }\n",
    ),
    (
        "bare_unit_multi",
        "module m;\nenum E { A, B(i64), C }\nfn f(k: bool) -> E { if k { return A; } else { return C; } }\n",
    ),
];

/// The primary exact-AIR surface. Retired actor/closure boundary cases live separately in
/// `RETIRED_LANE_CORPUS`, where each is required to be exact or explicit poison.
const CV_CORPORA: &[&[(&str, &str)]] = &[
    BODY_CORPUS,
    BODY_CF_CORPUS,
    BODY_MATCH_CORPUS,
    BODY_FORIN_CORPUS,
    BODY_FORRANGE_CORPUS,
    BODY_FIELD_CORPUS,
    BODY_WRITE_CORPUS,
    BODY_CALL_CORPUS,
    BODY_CONSTRUCT_CORPUS,
    BODY_ARRAY_CORPUS,
    BODY_STRING_CORPUS,
    BODY_ENUM_CORPUS,
    BODY_INDEX_CORPUS,
    BODY_BARE_ENUM_CORPUS,
    BODY_METHOD_CORPUS,
    BODY_TUPLE_CORPUS,
];

/// SH-SURFACE ST-3: tuples. A tuple construct `(a, b)` lowers exactly like a record
/// (`$tupleN__..`, positional fields, widths from the element value types); `let (x, y) = t`
/// desugars to per-element LoadFields. A tuple RHS in a `let` is lowered via lower_expr_to_var
/// (construct into a temp, then copy to the local) — the temp+copy the oracle emits.
const BODY_TUPLE_CORPUS: &[(&str, &str)] = &[
    (
        "t_construct_return",
        "module m;\nfn f(a: i64, b: i64) -> (i64, i64) { return (a, b); }\n",
    ),
    (
        "t_destr_sum",
        "module m;\nfn f(a: i64, b: i64) -> i64 { let t: (i64, i64) = (a, b); let (x, y) = t; return x + y; }\n",
    ),
    (
        "t_mixed_width",
        "module m;\nfn f(a: i64, b: bool) -> i64 { let t: (i64, bool) = (a, b); let (x, y) = t; if y { return x; } return 0; }\n",
    ),
    (
        "t_expr_elems",
        "module m;\nfn f(a: i64, b: i64) -> i64 { let t: (i64, i64) = (a + 1, b * 2); let (x, y) = t; return x + y; }\n",
    ),
    (
        "t_triple",
        "module m;\nfn f(a: i64, b: i64, c: i64) -> i64 { let t: (i64, i64, i64) = (a, b, c); let (x, y, z) = t; return x + y + z; }\n",
    ),
    (
        "t_u32_elems",
        "module m;\nfn f(a: u32, b: u32) -> u32 { let t: (u32, u32) = (a, b); let (x, y) = t; return x + y; }\n",
    ),
    (
        "t_bool_first_align",
        "module m;\nfn f(a: bool, b: i64) -> i64 { let t: (bool, i64) = (a, b); let (x, y) = t; if x { return y; } return 0; }\n",
    ),
    (
        "t_triple_trail_bool",
        "module m;\nfn f(a: i64, b: i64, c: bool) -> i64 { let t: (i64, i64, bool) = (a, b, c); let (x, y, z) = t; if z { return x + y; } return 0; }\n",
    ),
    (
        "t_destr_in_loop",
        "module m;\nfn f(a: i64, b: i64, n: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < n { let t: (i64, i64) = (a, b); let (x, y) = t; s = s + x + y; i = i + 1; } return s; }\n",
    ),
];

/// SH-SURFACE ST-2: dot-method calls `p.get()` — the oracle desugars to a plain Call(Type__method,
/// [receiver, ...args]). Covered in CV + wasm + execution. Two registries: the FuncId key is the
/// `Type__method` mangle (fids), the ret-type key is `Type::method` (tc_build_sigs).
const BODY_METHOD_CORPUS: &[(&str, &str)] = &[
    (
        "m_getter",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nfn f(p: P) -> i64 { return p.get(); }\n",
    ),
    (
        "m_with_arg",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn add(self: P, y: i64) -> i64 { return self.x + y; } }\nfn f(p: P) -> i64 { return p.add(5); }\n",
    ),
    (
        "m_let_result",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nfn f(p: P) -> i64 { let v: i64 = p.get(); return v + 1; }\n",
    ),
    (
        "m_u32_ret",
        "module m;\nrecord P { x: u32 }\nimpl P { pub fn get(self: P) -> u32 { return self.x; } }\nfn f(p: P) -> u32 { return p.get(); }\n",
    ),
    (
        "m_mut_recv",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn bump(self: P @Mut) -> i64 { self.x = 9; return self.x; } }\nfn f(p: P @Mut) -> i64 { return p.bump(); }\n",
    ),
    (
        "m_two_methods",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } pub fn twice(self: P) -> i64 { return self.x + self.x; } }\nfn f(p: P) -> i64 { let a: i64 = p.get(); let b: i64 = p.twice(); return a + b; }\n",
    ),
    (
        "m_method_plus_freefn",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nfn g(n: i64) -> i64 { return n + 1; }\nfn f(p: P) -> i64 { let a: i64 = p.get(); return g(a); }\n",
    ),
    (
        "m_two_records",
        "module m;\nrecord P { x: i64 }\nrecord Q { y: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nimpl Q { pub fn get(self: Q) -> i64 { return self.y; } }\nfn f(p: P, q: Q) -> i64 { return p.get() + q.get(); }\n",
    ),
    (
        "m_method_in_loop",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nfn f(p: P, n: i64) -> i64 { let mut i: i64 = 0; let mut t: i64 = 0; while i < n { t = t + p.get(); i = i + 1; } return t; }\n",
    ),
    (
        "m_method_result_bin",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nfn f(p: P) -> i64 { let v: i64 = p.get() * 3; return v; }\n",
    ),
    (
        "m_two_args",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn combine(self: P, a: i64, b: i64) -> i64 { return self.x + a + b; } }\nfn f(p: P) -> i64 { return p.combine(3, 4); }\n",
    ),
];

/// SH-AIR-CV-0 totality + determinism: the render is TOTAL (no panic) and non-empty over the
/// whole CV surface at BOTH stages, and byte-identical across two independent lowers (the
/// oracle-side half of X11; the shadow-side double-run lands with the CV-1 tool).
#[test]
fn cv0_render_total_and_deterministic() {
    for corpus in CV_CORPORA {
        for (label, src) in *corpus {
            let pre = oracle_cv_projection(src, false);
            let post = oracle_cv_projection(src, true);
            assert!(
                !pre.is_empty() && !post.is_empty(),
                "CV-0 {label}: empty render:\n{src}"
            );
            assert_eq!(
                pre,
                oracle_cv_projection(src, false),
                "CV-0 {label}: pre-memory render non-deterministic:\n{src}"
            );
            assert_eq!(
                post,
                oracle_cv_projection(src, true),
                "CV-0 {label}: post-memory render non-deterministic:\n{src}"
            );
        }
    }
}

/// SH-AIR-CV-0 pinned renders — the format's ground truth, one per axis of the epic:
/// `ret_bin_ll` = params + the X6 interleave on a binary (dst v2 allocated last here — operands
/// are params, no mats); `cf_if_rem` = Branch with a VISIBLE merge target + block push order;
/// `ix_const` = the #442 elision AND the interleave in one line (v1 = the LD dst is allocated
/// BEFORE v2 = the index mat, while the stmts run mat-first); `ct_one_field_post` = the CV-5
/// stage (post-memory record expansion with real offsets/sizes). A format change or an oracle
/// drift fails here naming the pin.
#[test]
fn cv0_pinned_renders() {
    let picks: &[(&str, &str, bool, &str)] = &[
        (
            "ret_bin_ll",
            "module m;\nfn f(a: i64, b: i64) -> i64 { return a + b; }\n",
            false,
            "f|v0:I64 v1:I64|I64|v2:I64|b0:As v2=Bin(v0 Add v1)>Ret v2",
        ),
        (
            "cf_if_rem",
            "module m;\nfn f(a: i64, c: bool) -> i64 { let mut z: i64 = 0; if c { z = a; } else { z = 1; } return z; }\n",
            false,
            "f|v0:I64 v1:Bool|I64|v2:I64|b0:As v2=Int(0)>Br v1 b1 b2 m=b3#b1:As v2=Var(v0)>Jmp b3#b2:As v2=Int(1)>Jmp b3#b3:>Ret v2",
        ),
        (
            "ix_const",
            "module m;\nfn f(arr: [i64; 4]) -> i64 { let z: i64 = arr[0]; return z; }\n",
            false,
            "f|v0:Ptr|I64|v1:I64 v2:I64|b0:As v2=Int(0);LD v1<-v0[v2]*8+4:I64>Ret v1",
        ),
        (
            "ct_one_field_post",
            "module m;\nrecord R { x: i64 }\nfn f(a: i64) -> i64 { let r: R = R { x: a }; return r.x; }\n",
            true,
            "f|v0:I64|I64|v1:Ptr v2:I64|b0:Fuel 1;BA v1 8/8;SF v1@0<-v0:I64;LF v2<-v1@0:I64>Ret v2",
        ),
    ];
    for (label, src, post, expected) in picks {
        let rendered = oracle_cv_projection(src, *post);
        assert_eq!(
            rendered.first().map(String::as_str),
            Some(*expected),
            "CV-0 {label}: pinned render drifted:\n{src}"
        );
        assert_eq!(rendered.len(), 1, "CV-0 {label}: expected exactly one fn");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-AIR-CV-1: the selfhost operand-exact lane — the third tool blob (`ai_encode_cv`).
// ─────────────────────────────────────────────────────────────────────────────

/// The CV tool body: lex → parse → `ai_encode_cv` (the operand-exact builder in selfhost/air.sigil).
fn ai_cv_tool_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = ai_encode_cv(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

fn ai_cv_wasm() -> &'static [u8] {
    static WCV: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    WCV.get_or_init(|| {
        compile_tool(&ai_tool(ai_cv_tool_body()))
            .expect("air CV tool should compile")
            .wasm
    })
}

/// Run the CV tool. X5: asserts fuel headroom — the CV lane must stay under 50% of FUEL (300M);
/// if a future slice crosses this, raise FUEL explicitly in its own commit.
fn cv_full_output(src: &str) -> String {
    let result = execute_ephemeral(ai_cv_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("air CV tool executes");
    assert!(
        result.fuel_consumed < 150_000_000,
        "CV tool fuel {} >= 50% of FUEL (X5): raise FUEL deliberately",
        result.fuel_consumed
    );
    String::from_utf8(result.output).expect("CV tool output is UTF-8")
}

/// The selfhost CV projection: one operand-exact line per fn, sorted (the shadow half of the
/// exact-equality comparison).
fn sigil_cv_projection(src: &str) -> Vec<String> {
    let mut v: Vec<String> = cv_full_output(src)
        .split('\n')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v
}

/// SH-AIR-CV-1 (the first exact-parity bijection): for every scalar straight-line fixture the
/// selfhost render — real VarIds, types, operands — EQUALS the oracle render, string-exact (X1).
#[test]
fn cv1_scalar_parity() {
    for (label, src) in BODY_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-1 {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// X11 (the shadow half): the CV tool is byte-deterministic across two runs.
#[test]
fn cv_shadow_deterministic() {
    for (_, src) in BODY_CORPUS {
        assert_eq!(
            cv_full_output(src),
            cv_full_output(src),
            "CV shadow non-deterministic: {src}"
        );
    }
}

/// CV-1 sweep folds — forms the KIND corpus never discriminated, permanent. `cv_expr_local` is THE
/// sweep catch: a bare-local EXPR STATEMENT diverges to_var (elides — no stmt) from the oracle's
/// `lower_expr_stmt` = fresh + INTO (`As vD=Var(src)`); the corpus's binary expr-stmt renders
/// identically under both, so only this case separates them. The rest: interleave stress
/// (nested/left-assoc binaries), corpus-absent literals (bool/negative), a comparison (Bool dst),
/// shadowing (env last-wins), and a two-fn module.
const CV1_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "cv_expr_local",
        "module m;\nfn f(a: i64) -> i64 { a; return a; }\n",
    ),
    (
        "cv_nested_bin",
        "module m;\nfn f(a: i64, b: i64, c: i64, d: i64) -> i64 { return (a + b) + (c + d); }\n",
    ),
    (
        "cv_left_assoc",
        "module m;\nfn f(a: i64) -> i64 { return a + 1 + 2; }\n",
    ),
    (
        "cv_bool_lit",
        "module m;\nfn f() -> bool { return true; }\n",
    ),
    (
        "cv_neg_lit",
        "module m;\nfn f() -> i64 { let z: i64 = -5; return z; }\n",
    ),
    (
        "cv_cmp",
        "module m;\nfn f(a: i64, b: i64) -> bool { return a < b; }\n",
    ),
    (
        "cv_shadow",
        "module m;\nfn f(a: i64) -> i64 { let z: i64 = a; let z: i64 = z + 1; return z; }\n",
    ),
    (
        "cv_two_fns",
        "module m;\nfn f(a: i64) -> i64 { return a; }\nfn g() -> i64 { return 2; }\n",
    ),
];

/// The CV-1 sweep-fold parity: same exact-equality bijection over the extra corpus.
#[test]
fn cv1_extra_parity() {
    for (label, src) in CV1_EXTRA_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-1 {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-2 (the block-structure bijection): control flow at exact parity — real block ids,
/// targets, and merge, with blocks serialized in PUSH order (≠ id order). Covers if/while (+ the
/// dead-remainder divergence + break/continue + trap `Unr`), match (Dispatch + the exhaustive
/// last-literal rule), and the full for-in operand chain.
#[test]
fn cv2_cf_parity() {
    for (label, src) in BODY_CF_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-2 CF {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv2_match_parity() {
    for (label, src) in BODY_MATCH_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-2 MATCH {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv2_forin_parity() {
    for (label, src) in BODY_FORIN_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-2 FORIN {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// RF-M4 (the range-for operand-exact bijection): the full fresh-local ORDER (start-mat,
/// end-mat, v, __r_end, __for_cond, __one — I64 throughout), the b-head/cond/incr/body/exit
/// block PUSH order (incr BEFORE the body, no preamble block), the I64 continue injection,
/// and the RF-M2 elision (rf_elide/rf_len/rf_let_arr/rf_write bare LD/SD; rf_straddle's full
/// LF/Wrap/GtEq/Trap chain) at exact VarId/BlockId parity.
#[test]
fn cv2_forrange_parity() {
    for (label, src) in BODY_FORRANGE_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-2 FORRANGE {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// CV-2 sweep folds — the truncation boundary + nesting stress, permanent. `cv2_dead_after_match`
/// exercises the match-arms-all-return truncation (the typed AST drops the trailing stmts — the
/// shadow's `cv_match_arms_diverge` mirrors statements.rs:2492+886); `cv2_mixed_div_if` pins the
/// boundary's OTHER side (one live branch → the remainder is LIVE and gets a merge block);
/// `cv2_both_trap_if` = both branches diverge via trap; the rest are nesting/elem-width stress.
const CV2_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "cv2_dead_after_match",
        "module m;\nfn f(x: i64) -> i64 { match x { 0 => { return 1; }, _ => { return 2; } } let z: i64 = 9; return z; }\n",
    ),
    (
        "cv2_mixed_div_if",
        "module m;\nfn f(c: bool, a: i64) -> i64 { if c { return a; } else { } let z: i64 = 1; return z; }\n",
    ),
    (
        "cv2_both_trap_if",
        "module m;\nfn f(c: bool) -> i64 { if c { trap(); } else { trap(); } }\n",
    ),
    (
        "cv2_if_in_if_in_while",
        "module m;\nfn f(c: bool, d: bool, e: bool) -> i64 { while c { if d { if e { break; } else { continue; } } else { } } return 0; }\n",
    ),
    (
        "cv2_trap_in_if_in_forin",
        "module m;\nfn f(arr: [i64; 3], d: bool) -> i64 { for x in arr { if d { trap(); } else { return 1; } } return 0; }\n",
    ),
    (
        "cv2_match_in_while",
        "module m;\nfn f(c: bool, x: i64) -> i64 { let mut t: i64 = 0; while c { match x { 0 => { t = 1; }, _ => { t = 2; } } } return t; }\n",
    ),
    (
        "cv2_while_after_while",
        "module m;\nfn f(c: bool, d: bool) -> i64 { while c { } while d { } return 0; }\n",
    ),
    (
        "cv2_forin_u32",
        "module m;\nfn f(arr: [u32; 2]) -> i64 { for x in arr { } return 0; }\n",
    ),
];

/// The CV-2 sweep-fold parity: same exact-equality bijection over the extra corpus.
#[test]
fn cv2_extra_parity() {
    for (label, src) in CV2_EXTRA_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-2 {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-3: fields + calls at operand-exact parity — real LoadField/StoreField offsets (the
/// decl-order width math), `Call{dst, func: FuncId, args}` with the decl-index FuncId basis, the
/// Unit-dst rule (a void call renders dst-less; its fresh Unit dst is a phantom local), and the
/// pre-memory enum-UNIT construct (forced into this corpus by `fld_const_coexist`).
#[test]
fn cv3_field_parity() {
    for (label, src) in BODY_FIELD_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-3 FIELD {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv3_write_parity() {
    for (label, src) in BODY_WRITE_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-3 WRITE {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv3_call_parity() {
    for (label, src) in BODY_CALL_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-3 CALL {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// CV-3 sweep folds, permanent. Mixed-width offsets (`u32,i64,bool` → @0/@4/@12), a bool field, a
/// field as a call arg, a 3-deep call chain, the enum-unit construct in a LET, an enum whose
/// OTHER variant carries a payload (cell size = 4 + max payload = 20), a call in a branch, and a
/// field read as a binary operand. (A VOID expr-stmt call and a call-RHS field write both PANIC
/// the oracle — uncomparable, AG-CV3-VOIDCALL / AG-CV3-CALLRHS-WRITE.)
const CV3_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "cv3_mixed_width",
        "module m;\nrecord R { a: u32, b: i64, c: bool }\nfn f(r: R) -> i64 { return r.b; }\n",
    ),
    (
        "cv3_bool_field",
        "module m;\nrecord R { a: u32, b: i64, c: bool }\nfn f(r: R) -> bool { return r.c; }\n",
    ),
    (
        "cv3_call_field_arg2",
        "module m;\nrecord R { x: i64 }\nfn g(a: i64, b: i64) -> i64 { return a; }\nfn f(r: R) -> i64 { return g(r.x, 2); }\n",
    ),
    (
        "cv3_call_chain3",
        "module m;\nfn a1(x: i64) -> i64 { return x; }\nfn b1(x: i64) -> i64 { return a1(x); }\nfn f(x: i64) -> i64 { return b1(a1(x)); }\n",
    ),
    (
        "cv3_enum_unit_let",
        "module m;\nenum E { A, B }\nfn f() -> i64 { let e: E = E::B; return 0; }\n",
    ),
    (
        "cv3_enum_payload_sz",
        "module m;\nenum E { A, B(i64, i64) }\nfn g() -> E { return E::A; }\nfn f() -> i64 { return 0; }\n",
    ),
    (
        "cv3_call_in_if",
        "module m;\nfn g(x: i64) -> i64 { return x; }\nfn f(c: bool, x: i64) -> i64 { if c { return g(x); } else { } return 0; }\n",
    ),
    (
        "cv3_field_in_binary",
        "module m;\nrecord R { x: i64 }\nfn f(r: R) -> i64 { return r.x + 1; }\n",
    ),
];

/// The CV-3 sweep-fold parity.
#[test]
fn cv3_extra_parity() {
    for (label, src) in CV3_EXTRA_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-3 {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-4: constructs + index at PRE-memory shapes (X3: vs `lower_oracle` only) — the record
/// `Rec(...)` Assign (written-order field names), the array/string/enum-payload BumpAlloc
/// expansions WITHOUT FuelDecrement, and the index bounds chain (+ the #442 literal elision, the
/// original-index LD/SD, the RHS-mat-after-TrapIf write order).
#[test]
fn cv4_construct_parity() {
    for (label, src) in BODY_CONSTRUCT_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-4 CT {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv4_array_parity() {
    for (label, src) in BODY_ARRAY_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-4 ARR {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv4_string_parity() {
    for (label, src) in BODY_STRING_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-4 STR {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv4_enum_parity() {
    for (label, src) in BODY_ENUM_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-4 EN {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

#[test]
fn cv4_index_parity() {
    for (label, src) in BODY_INDEX_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-4 IX {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

/// CV-4 sweep folds, permanent: WRITTEN-order construct fields, index on array LETS (the
/// CvBind.elem let-path, var + elided-literal), u32 arrays (w=4), mixed enum payload offsets
/// (i64+bool → @4/@12), record-in-array-in-record nesting, a str payload (Ptr), an array as the
/// return value. (A u32-index WRITE on a non-@Mut param PANICS the oracle — uncomparable,
/// AG-CV4-NONMUT-WRITE.)
const CV4_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "cv4_ord_swapped",
        "module m;\nrecord R { x: i64, y: i64 }\nfn f(a: i64, b: i64) -> i64 { let r: R = R { y: b, x: a }; return 0; }\n",
    ),
    (
        "cv4_ix_on_let_arr",
        "module m;\nfn f(i: i64) -> i64 { let a: [i64; 2] = [1, 2]; let z: i64 = a[i]; return z; }\n",
    ),
    (
        "cv4_ix_const_let_arr",
        "module m;\nfn f() -> i64 { let a: [i64; 2] = [1, 2]; return a[0]; }\n",
    ),
    (
        "cv4_u32_arr_ix",
        "module m;\nfn f(arr: [u32; 3], i: u32) -> u32 { return arr[i]; }\n",
    ),
    (
        "cv4_mixed_payload",
        "module m;\nenum E { A, B(i64, bool) }\nfn f(x: i64, c: bool) -> i64 { let e: E = E::B(x, c); return 0; }\n",
    ),
    (
        "cv4_rec_in_arr_in_rec",
        "module m;\nrecord P { x: i64 }\nrecord Q { a: [i64; 1] }\nfn f() -> i64 { let q: Q = Q { a: [5] }; return 0; }\n",
    ),
    (
        "cv4_str_payload",
        "module m;\nenum E { A, B(str) }\nfn f() -> i64 { let e: E = E::B(\"hi\"); return 0; }\n",
    ),
    (
        "cv4_arr_as_ret",
        "module m;\nfn f() -> [i64; 2] { return [1, 2]; }\n",
    ),
];

/// The CV-4 sweep-fold parity.
#[test]
fn cv4_extra_parity() {
    for (label, src) in CV4_EXTRA_CORPUS {
        let sigil = sigil_cv_projection(src);
        let oracle = oracle_cv_projection(src, false);
        assert_eq!(
            sigil, oracle,
            "CV-4 {label}: operand-exact projection diverged:\n{src}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-AIR-CV-5: the selfhost memory pass — the 4th tool blob (`ai_encode_cv_mem`
// = build → cv_mem_lower → serialize, the first selfhost stage composition),
// compared vs `memory::lower(lower_oracle(src))` (X3: the ONLY post-memory lane).
// ─────────────────────────────────────────────────────────────────────────────

/// The CV-MEM tool body: lex → parse → `ai_encode_cv_mem` (the CV builder + the
/// selfhost memory transform in selfhost/air.sigil).
fn ai_cv_mem_tool_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = ai_encode_cv_mem(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

fn ai_cv_mem_wasm() -> &'static [u8] {
    static WCVM: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    WCVM.get_or_init(|| {
        compile_tool(&ai_tool(ai_cv_mem_tool_body()))
            .expect("air CV-MEM tool should compile")
            .wasm
    })
}

/// Run the CV-MEM tool. X5: the same 50%-of-FUEL headroom bound as the CV lane.
fn cv_mem_full_output(src: &str) -> String {
    let result = execute_ephemeral(ai_cv_mem_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("air CV-MEM tool executes");
    assert!(
        result.fuel_consumed < 150_000_000,
        "CV-MEM tool fuel {} >= 50% of FUEL (X5): raise FUEL deliberately",
        result.fuel_consumed
    );
    String::from_utf8(result.output).expect("CV-MEM tool output is UTF-8")
}

/// The selfhost POST-memory CV projection (the shadow half of the CV-5 comparison).
fn sigil_cv_mem_projection(src: &str) -> Vec<String> {
    let mut v: Vec<String> = cv_mem_full_output(src)
        .split('\n')
        .filter(|s| !s.is_empty() && !s.starts_with("MEMREPORT"))
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v
}

/// SH-AIR-CV-5: record constructs at post-memory exact parity — the selfhost
/// transform's `Fuel + BA + SF×N` expansion (real sizes, real offsets, SF ty from
/// the VALUE var) equals `memory::lower(lower_oracle)`.
#[test]
fn cv5_construct_mem_parity() {
    for (label, src) in BODY_CONSTRUCT_CORPUS {
        assert_eq!(
            sigil_cv_mem_projection(src),
            oracle_cv_projection(src, true),
            "CV-5 {label}: post-memory projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-5: array literals — the Fuel prepend before the array BumpAlloc.
#[test]
fn cv5_array_mem_parity() {
    for (label, src) in BODY_ARRAY_CORPUS {
        assert_eq!(
            sigil_cv_mem_projection(src),
            oracle_cv_projection(src, true),
            "CV-5 {label}: post-memory projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-5: string literals — the Fuel prepend before the string BumpAlloc.
#[test]
fn cv5_string_mem_parity() {
    for (label, src) in BODY_STRING_CORPUS {
        assert_eq!(
            sigil_cv_mem_projection(src),
            oracle_cv_projection(src, true),
            "CV-5 {label}: post-memory projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-5: enum constructs — the Fuel prepend before the enum-cell BumpAlloc.
#[test]
fn cv5_enum_mem_parity() {
    for (label, src) in BODY_ENUM_CORPUS {
        assert_eq!(
            sigil_cv_mem_projection(src),
            oracle_cv_projection(src, true),
            "CV-5 {label}: post-memory projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-5: the index bounds chain is UNTOUCHED by memory (copy-verbatim).
#[test]
fn cv5_index_mem_parity() {
    for (label, src) in BODY_INDEX_CORPUS {
        assert_eq!(
            sigil_cv_mem_projection(src),
            oracle_cv_projection(src, true),
            "CV-5 {label}: post-memory projection diverged:\n{src}"
        );
    }
}

/// SH-AIR-CV-5 — THE COVERAGE-PARITY DECLARATION: every CV corpus fixture (the 12
/// KIND-surface corpora + all four sweep-fold extras) renders post-memory
/// string-exactly on both sides. With this, the CV lane covers the KIND lanes'
/// entire surface at BOTH stages.
#[test]
fn cv5_all_corpora_mem_parity() {
    for corpus in CV_CORPORA {
        for (label, src) in *corpus {
            assert_eq!(
                sigil_cv_mem_projection(src),
                oracle_cv_projection(src, true),
                "CV-5 (all) {label}: post-memory projection diverged:\n{src}"
            );
        }
    }
    for corpus in [
        CV1_EXTRA_CORPUS,
        CV2_EXTRA_CORPUS,
        CV3_EXTRA_CORPUS,
        CV4_EXTRA_CORPUS,
    ] {
        for (label, src) in corpus {
            assert_eq!(
                sigil_cv_mem_projection(src),
                oracle_cv_projection(src, true),
                "CV-5 (extra) {label}: post-memory projection diverged:\n{src}"
            );
        }
    }
}

/// SH-AIR-CV-5 composition sanity: the transform is IDENTITY on BumpAlloc-free
/// fns — the mem projection of the scalar corpus equals the pre-memory one.
#[test]
fn cv5_scalar_mem_identity() {
    for (label, src) in BODY_CORPUS {
        assert_eq!(
            sigil_cv_mem_projection(src),
            sigil_cv_projection(src),
            "CV-5 {label}: memory not identity on a BumpAlloc-free fn:\n{src}"
        );
    }
}

/// X11 for the 4th blob: the CV-MEM tool is byte-deterministic across two runs
/// (over the heaviest, expansion-bearing corpus).
#[test]
fn cv5_mem_shadow_deterministic() {
    for (_, src) in BODY_CONSTRUCT_CORPUS {
        assert_eq!(
            cv_mem_full_output(src),
            cv_mem_full_output(src),
            "CV-MEM shadow non-deterministic: {src}"
        );
    }
}

/// CV-5 sweep folds — transform-specific stress, permanent. Expansion inside
/// non-entry blocks (loop body, match arm — the stmt-range rebuild must tile
/// per block while ids/terms stay); all four BumpAlloc kinds interleaved in one
/// fn; the `Fuel 2` integer-division boundary (BA 132); a 3-deep nested
/// construct; width-4 accumulation (bool+i64+u32 → @0/@4/@12, size 16); a
/// str-valued field (the field ty resolves Ptr via the LOCALS path of
/// `cv_var_tytok`); and the #457 decl-normalized swapped construct through the
/// transform (the Phase-0 miscompile's shape, now consistent end-to-end).
const CV5_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "cv5_rec_in_loop",
        "module m;\nrecord R { x: i64 }\nfn f(n: i64) -> i64 { let mut i: i64 = 0; let mut acc: i64 = 0; while i < n { let r: R = R { x: i }; acc = acc + r.x; i = i + 1; } return acc; }\n",
    ),
    (
        "cv5_rec_in_match",
        "module m;\nrecord R { x: i64 }\nfn f(n: i64) -> i64 { match n { 0 => { let r: R = R { x: 1 }; return r.x; }, _ => { return 0; } } }\n",
    ),
    (
        "cv5_mixed_bas",
        "module m;\nrecord R { x: i64 }\nenum E { A, B(i64) }\nfn f(a: i64) -> i64 { let s: str = \"hi\"; let xs: [i64; 2] = [1, 2]; let e: E = E::B(a); let r: R = R { x: a }; return r.x; }\n",
    ),
    (
        "cv5_fuel2_arr",
        "module m;\nfn f() -> i64 { let xs: [i64; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]; return xs[0]; }\n",
    ),
    (
        "cv5_rec3_nested",
        "module m;\nrecord A { v: i64 }\nrecord B { a: A, w: i64 }\nrecord C { b: B, z: i64 }\nfn f(p: i64, q: i64, t: i64) -> i64 { let c: C = C { b: B { a: A { v: p }, w: q }, z: t }; return c.z; }\n",
    ),
    (
        "cv5_rec_bool_u32",
        "module m;\nrecord P { a: bool, b: i64, c: u32 }\nfn f(x: bool, y: i64, z: u32) -> i64 { let p: P = P { a: x, b: y, c: z }; return p.b; }\n",
    ),
    (
        "cv5_rec_str_field",
        "module m;\nrecord S { name: str, n: i64 }\nfn f(a: i64) -> i64 { let s: S = S { name: \"nm\", n: a }; return s.n; }\n",
    ),
    (
        "cv5_actor_handler_rec",
        "module m;
record R { x: i64 }
actor A {
  init() { }
  on ping(a: i64) -> i64 { let r: R = R { x: a }; return r.x; }
}
",
    ),
    (
        "cv5_swapped_mixed",
        "module m;\nrecord R { x: i64, y: u32 }\nfn f(a: i64, b: u32) -> i64 { let r: R = R { y: b, x: a }; return r.x; }\n",
    ),
];

/// The CV-5 fold parity — both stages: post-memory vs the oracle AND the
/// pre-memory lane stays exact on the same sources (the folds join both suites).
#[test]
fn cv5_extra_parity() {
    for (label, src) in CV5_EXTRA_CORPUS {
        assert_eq!(
            sigil_cv_mem_projection(src),
            oracle_cv_projection(src, true),
            "CV-5 extra {label}: post-memory projection diverged:\n{src}"
        );
        assert_eq!(
            sigil_cv_projection(src),
            oracle_cv_projection(src, false),
            "CV-5 extra {label}: PRE-memory projection diverged:\n{src}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-MEM M1: report parity — the remaining two differential oracles of the
// SH-MEM rung (`inserted_allocations` + `total_bytes_allocated`; the stmt
// sequence at insertion sites is CV-5's operand-exact lane).
// ─────────────────────────────────────────────────────────────────────────────

/// The shadow's memory report: the `MEMREPORT|<strategy>|A<allocs>|B<bytes>` line
/// the mem lane appends (stripped from the fn projection above).
fn sigil_mem_report(src: &str) -> String {
    cv_mem_full_output(src)
        .split('\n')
        .find(|s| s.starts_with("MEMREPORT"))
        .expect("mem lane emits a MEMREPORT line")
        .to_string()
}

/// The oracle's report, formatted identically from `memory::lower`'s returned
/// `MemoryLowering` (X1: one format, oracle-derived).
fn oracle_mem_report(src: &str) -> String {
    let (_, r) = memory::lower(lower_oracle(src));
    format!(
        "MEMREPORT|{:?}|A{}|B{}",
        r.allocation_strategy, r.inserted_allocations, r.total_bytes_allocated
    )
}

/// SH-MEM M1: allocation-count + byte-total parity over the entire CV surface
/// (the 12 corpora + all fold sets). ModuleInit contributes zero on this surface
/// (Phase-0-pinned); a spawn/send fixture would diff the line loudly (AG-M1-SPAWN).
#[test]
fn m1_mem_report_parity() {
    for corpus in CV_CORPORA {
        for (label, src) in *corpus {
            assert_eq!(
                sigil_mem_report(src),
                oracle_mem_report(src),
                "M1 {label}: memory report diverged:\n{src}"
            );
        }
    }
    for corpus in [
        CV1_EXTRA_CORPUS,
        CV2_EXTRA_CORPUS,
        CV3_EXTRA_CORPUS,
        CV4_EXTRA_CORPUS,
        CV5_EXTRA_CORPUS,
    ] {
        for (label, src) in corpus {
            assert_eq!(
                sigil_mem_report(src),
                oracle_mem_report(src),
                "M1 extra {label}: memory report diverged:\n{src}"
            );
        }
    }
}

/// SH-MEM M1: a REAL stdlib module at full parity — `abi.sigil` (pure-compute
/// bit-ops helpers) renders operand-exactly at BOTH stages and its memory
/// report matches (0 allocations — Alloc-free module, pinned).
#[test]
fn m1_stdlib_abi_parity() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../stdlib/sigil/abi.sigil");
    let src = std::fs::read_to_string(path).expect("abi.sigil readable");
    assert_eq!(
        sigil_cv_mem_projection(&src),
        oracle_cv_projection(&src, true),
        "abi.sigil post-memory projection"
    );
    assert_eq!(
        sigil_cv_projection(&src),
        oracle_cv_projection(&src, false),
        "abi.sigil pre-memory projection"
    );
    let report = sigil_mem_report(&src);
    assert_eq!(report, oracle_mem_report(&src), "abi.sigil memory report");
    assert_eq!(
        report, "MEMREPORT|ArenaPerActor|A0|B0",
        "abi.sigil is Alloc-free (pinned)"
    );
}

/// SH-MEM M1 stdlib armor: the census-pinned trivially-covered modules (their
/// fns are all generic/impl forms — ZERO free mono fns on both sides today).
/// If a free monomorphic fn is ever added to one, it enters the lane
/// automatically and any divergence (projection or report) fails here loudly.
#[test]
fn m1_stdlib_trivial_parity() {
    for name in ["arena", "option", "result", "vec"] {
        let path = format!(
            "{}/../../stdlib/sigil/{name}.sigil",
            env!("CARGO_MANIFEST_DIR")
        );
        let src = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(
            sigil_cv_mem_projection(&src),
            oracle_cv_projection(&src, true),
            "stdlib {name}: post-memory projection"
        );
        assert_eq!(
            sigil_mem_report(&src),
            oracle_mem_report(&src),
            "stdlib {name}: memory report"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-FUEL F1: the fuel pass — the SECOND stage composition (`ai_encode_cv_fuel`
// = build → cv_mem_lower → cv_fuel_insert → serialize), compared vs
// `fuel::insert(memory::lower(lower_oracle(src)))`. With this the AIR pipeline
// is shadowed operand-exactly end-to-end up to `wasm::emit`.
// ─────────────────────────────────────────────────────────────────────────────

/// The CV-FUEL tool body: lex → parse → `ai_encode_cv_fuel`.
fn ai_cv_fuel_tool_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = ai_encode_cv_fuel(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

fn ai_cv_fuel_wasm() -> &'static [u8] {
    static WCVF: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    WCVF.get_or_init(|| {
        compile_tool(&ai_tool(ai_cv_fuel_tool_body()))
            .expect("air CV-FUEL tool should compile")
            .wasm
    })
}

/// Run the CV-FUEL tool. X5: the same 50%-of-FUEL headroom bound.
fn cv_fuel_full_output(src: &str) -> String {
    let result = execute_ephemeral(ai_cv_fuel_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("air CV-FUEL tool executes");
    assert!(
        result.fuel_consumed < 150_000_000,
        "CV-FUEL tool fuel {} >= 50% of FUEL (X5): raise FUEL deliberately",
        result.fuel_consumed
    );
    String::from_utf8(result.output).expect("CV-FUEL tool output is UTF-8")
}

/// The selfhost POST-FUEL projection (both report lines stripped).
fn sigil_cv_fuel_projection(src: &str) -> Vec<String> {
    let mut v: Vec<String> = cv_fuel_full_output(src)
        .split('\n')
        .filter(|s| !s.is_empty() && !s.starts_with("MEMREPORT") && !s.starts_with("FUELREPORT"))
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v
}

/// The shadow's fuel report (`FUELREPORT|S<sites>|R<budget>`).
fn sigil_fuel_report(src: &str) -> String {
    cv_fuel_full_output(src)
        .split('\n')
        .find(|s| s.starts_with("FUELREPORT"))
        .expect("fuel lane emits a FUELREPORT line")
        .to_string()
}

/// The oracle's post-fuel projection: `fuel::insert(memory::lower(lower_oracle))`.
fn oracle_cv_fuel_projection(src: &str) -> Vec<String> {
    let (mem_p, _) = memory::lower(lower_oracle(src));
    let (fuel_p, _) = fuel::insert(mem_p);
    let mut v: Vec<String> = fuel_p
        .functions
        .iter()
        .filter(|f| !matches!(f.kind, AirFunctionKind::ModuleInit))
        .map(cv_render_fn)
        .collect();
    v.sort();
    v
}

/// The oracle's fuel report, formatted identically from `FuelPlan`.
/// SH-FUEL F2: R is the WCC budget and C the workload-ceiling flag.
fn oracle_fuel_report(src: &str) -> String {
    let (mem_p, _) = memory::lower(lower_oracle(src));
    let (_, plan) = fuel::insert(mem_p);
    format!(
        "FUELREPORT|S{}|R{}|C{}",
        plan.inserted_sites,
        plan.recommended_budget,
        if plan.is_workload_ceiling { 1 } else { 0 }
    )
}

/// SH-FUEL F1 — the composed-pipeline parity declaration: every CV corpus fixture
/// (the 12 corpora + all 5 fold sets) renders POST-FUEL string-exactly — two
/// selfhost transforms deep.
#[test]
fn f1_all_corpora_fuel_parity() {
    for corpus in CV_CORPORA {
        for (label, src) in *corpus {
            assert_eq!(
                sigil_cv_fuel_projection(src),
                oracle_cv_fuel_projection(src),
                "F1 {label}: post-fuel projection diverged:\n{src}"
            );
        }
    }
    for corpus in [
        CV1_EXTRA_CORPUS,
        CV2_EXTRA_CORPUS,
        CV3_EXTRA_CORPUS,
        CV4_EXTRA_CORPUS,
        CV5_EXTRA_CORPUS,
    ] {
        for (label, src) in corpus {
            assert_eq!(
                sigil_cv_fuel_projection(src),
                oracle_cv_fuel_projection(src),
                "F1 extra {label}: post-fuel projection diverged:\n{src}"
            );
        }
    }
}

/// SH-FUEL F1: FuelPlan parity (`inserted_sites` + the `128 + sites × 8` budget)
/// over the same surface.
#[test]
fn f1_fuel_report_parity() {
    for corpus in CV_CORPORA {
        for (label, src) in *corpus {
            assert_eq!(
                sigil_fuel_report(src),
                oracle_fuel_report(src),
                "F1 {label}: fuel report diverged:\n{src}"
            );
        }
    }
    for corpus in [
        CV1_EXTRA_CORPUS,
        CV2_EXTRA_CORPUS,
        CV3_EXTRA_CORPUS,
        CV4_EXTRA_CORPUS,
        CV5_EXTRA_CORPUS,
    ] {
        for (label, src) in corpus {
            assert_eq!(
                sigil_fuel_report(src),
                oracle_fuel_report(src),
                "F1 extra {label}: fuel report diverged:\n{src}"
            );
        }
    }
}

/// X11 for the 5th blob (over the loop-heaviest corpora).
#[test]
fn f1_fuel_shadow_deterministic() {
    for (_, src) in BODY_CF_CORPUS.iter().chain(BODY_CALL_CORPUS) {
        assert_eq!(
            cv_fuel_full_output(src),
            cv_fuel_full_output(src),
            "CV-FUEL shadow non-deterministic: {src}"
        );
    }
}

/// F1 sweep folds — fuel-transform stress, permanent. A call in a LOOP HEADER's
/// cond (call-fuel prepend + the back-edge append land in ONE block); recursion
/// (a self-referential FuncId call site); a call in a match arm inside a loop
/// (fuel through the composed CF walk); two calls in one expression (two
/// prepends from one stmt walk).
const F1_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "f1_call_in_cond",
        "module m;\nfn g(a: i64) -> i64 { return a + 1; }\nfn f(n: i64) -> i64 { let mut i: i64 = 0; while g(i) < n { i = i + 1; } return i; }\n",
    ),
    (
        "f1_recursion",
        "module m;\nfn f(n: i64) -> i64 { if n < 1 { return 0; } return f(n - 1); }\n",
    ),
    (
        "f1_call_in_match_in_loop",
        "module m;\nfn g(a: i64) -> i64 { return a + 1; }\nfn f(n: i64) -> i64 { let mut i: i64 = 0; let mut t: i64 = 0; while i < n { match i { 0 => { t = g(t); }, _ => { t = t + 1; } } i = i + 1; } return t; }\n",
    ),
    (
        "f1_two_calls_one_stmt",
        "module m;\nfn g(a: i64) -> i64 { return a + 1; }\nfn f(a: i64) -> i64 { return g(a) + g(a); }\n",
    ),
    // ── The ALLOCATING folds ────────────────────────────────────────────────
    // Without these the alloc-weight half of the budget is vacuous: every other
    // corpus leaves `macc` empty, so the mem-lane term never runs.
    // `f1_record_narrow` pins the max(1, ·) clamp (16 bytes / 64 == 0 -> 1);
    // `f1_record_wide` pins the division itself (a 16-field record is 128
    // bytes -> weight 2, so the two cannot be confused).
    (
        "f1_record_narrow",
        "module m;\nrecord P { x: i64, y: i64 }\nfn f(a: i64) -> i64 { let p: P = P { x: a, y: a }; return p.x; }\n",
    ),
    (
        "f1_record_wide",
        "module m;\nrecord W { a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: i64, j: i64, k: i64, l: i64, m: i64, n: i64, o: i64, p: i64 }\nfn f(z: i64) -> i64 { let w: W = W { a: z, b: z, c: z, d: z, e: z, f: z, g: z, h: z, i: z, j: z, k: z, l: z, m: z, n: z, o: z, p: z }; return w.a; }\n",
    ),
    // Alloc fuel AND fuel's own sites in one program: pins that the budget SUMS
    // the two channels rather than letting one shadow the other.
    (
        "f1_record_plus_call_in_loop",
        "module m;\nrecord P { x: i64, y: i64 }\nfn g(a: i64) -> i64 { return a + 1; }\nfn f(n: i64) -> i64 { let mut i: i64 = 0; while i < n { let p: P = P { x: i, y: i }; i = g(p.x); } return i; }\n",
    ),
    // ── SH-FUEL F2 (WCC) folds ──────────────────────────────────────────────
    // Cross-function multiplication: g is called from a ×8 bounded loop, so
    // cost(f) = own(f) + 8×cost(g) — the call-graph propagation channel. C1.
    // g's record construct gives it NONZERO own cost (the alloc decrement), so
    // a corrupted edge weight is observable in R (with cost(g)=0 the channel
    // would carry zero and no corruption could surface).
    (
        "f1_call_chain_in_bounded_loop",
        "module m;\nrecord Q { x: i64, y: i64 }\nfn g(a: i64) -> i64 { let q: Q = Q { x: a, y: a }; return q.x + 1; }\nfn f(z: i64) -> i64 { let mut t: i64 = z; for i in 0..8 { t = g(t); } return t; }\n",
    ),
    // Nested bounded ranges overflowing the 2^40 clamp: 2^20 × 2^20 × 2^20 =
    // 2^60 → both sides must clamp to EXACTLY 2^40 (the i64-vs-u64 divergence
    // trap this fixture exists to spring).
    (
        "f1_clamp_overflow",
        "module m;\nfn f(z: i64) -> i64 { let mut t: i64 = z; for i in 0..1048576 { for j in 0..1048576 { for k in 0..1048576 { t = t + 1; } } } return t; }\n",
    ),
    // A runtime START with a static end is NOT bounded (negative starts trip
    // more than the end) — the review's finding-6 soundness pin. C0.
    (
        "f1_runtime_start_static_end",
        "module m;\nfn f(s: i64) -> i64 { let mut t: i64 = 0; for i in s..8 { t = t + 1; } return t; }\n",
    ),
    // A statically-EMPTY range: k = max(0, 2-5) = 0 — body cost multiplies to
    // zero, the cond still charges ×1, and the program stays a ceiling. C1.
    (
        "f1_zero_trip_range",
        "module m;\nfn f(z: i64) -> i64 { let mut t: i64 = z; for i in 5..2 { t = t + 100; } return t; }\n",
    ),
];

/// The F1 fold parity — post-fuel projection + report on each.
#[test]
fn f1_extra_parity() {
    for (label, src) in F1_EXTRA_CORPUS {
        assert_eq!(
            sigil_cv_fuel_projection(src),
            oracle_cv_fuel_projection(src),
            "F1 extra {label}: post-fuel projection diverged:\n{src}"
        );
        assert_eq!(
            sigil_fuel_report(src),
            oracle_fuel_report(src),
            "F1 extra {label}: fuel report diverged:\n{src}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-WASM W0: the whole-module byte-equality rig (harness-only — zero selfhost
// code this slice). Criterion: `wasm::emit` over the CV-verified pipeline,
// compared as RAW bytes. The annotated byte cheat sheet lives in
// docs/specs/sh-wasm.md.
// ─────────────────────────────────────────────────────────────────────────────

/// The oracle's whole-module bytes: the composed pipeline + `wasm::emit`.
/// X-W7 (single-ring armor): the covered surface never produces an outer ring.
fn oracle_wasm_bytes(src: &str) -> Vec<u8> {
    let (mem_p, _) = memory::lower(lower_oracle(src));
    let (fuel_p, _) = fuel::insert(mem_p);
    let out = wasm::emit(&fuel_p);
    assert!(
        out.outer.is_none(),
        "X-W7: unexpected outer-ring module:\n{src}"
    );
    out.inner
}

/// STRICT hex decode (X-W4): panics on odd length or any non-hex char, naming
/// the fixture — a garbled shadow output can never "compare equal".
fn wasm_hex_decode(hex: &str, label: &str) -> Vec<u8> {
    let bytes = hex.as_bytes();
    assert!(
        bytes.len().is_multiple_of(2),
        "W {label}: odd-length hex ({} chars)",
        bytes.len()
    );
    bytes
        .chunks(2)
        .map(|pair| {
            let hi = (pair[0] as char)
                .to_digit(16)
                .unwrap_or_else(|| panic!("W {label}: non-hex byte {:#04x}", pair[0]));
            let lo = (pair[1] as char)
                .to_digit(16)
                .unwrap_or_else(|| panic!("W {label}: non-hex byte {:#04x}", pair[1]));
            (hi * 16 + lo) as u8
        })
        .collect()
}

/// Byte-equality with the X-W6 diff printer: on mismatch, the first divergent
/// offset + ±32-byte hex windows + best-effort WAT of both sides (wrapped so a
/// WAT render failure can never mask the byte assert).
fn assert_wasm_eq(sigil: &[u8], oracle: &[u8], label: &str) {
    if sigil == oracle {
        return;
    }
    let n = sigil.len().min(oracle.len());
    let at = (0..n).find(|&i| sigil[i] != oracle[i]).unwrap_or(n);
    let lo = at.saturating_sub(32);
    let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
    let swin = hex(&sigil[lo..sigil.len().min(at + 32)]);
    let owin = hex(&oracle[lo..oracle.len().min(at + 32)]);
    let wat = |b: &[u8]| {
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            sigil_test_utils::snapshot::wat_of(b)
        }))
        .unwrap_or_else(|_| "<WAT render failed>".to_string())
    };
    panic!(
        "W {label}: wasm bytes diverge at offset {at} (sigil {} bytes, oracle {} bytes)\n  sigil [{lo}..]: {swin}\n  oracle[{lo}..]: {owin}\n--- sigil WAT ---\n{}\n--- oracle WAT ---\n{}",
        sigil.len(),
        oracle.len(),
        wat(sigil),
        wat(oracle)
    );
}

/// W0 pins: whole-module hex of three oracle modules, hand-decoded in
/// docs/specs/sh-wasm.md — the oracle-side stability armor. An oracle or
/// wasm-encoder drift fails HERE naming itself, before any selfhost work.
#[test]
fn w0_pinned_modules() {
    let pins: &[(&str, &str, &str)] = &[
        (
            "smallest",
            "module m;\nfn f() -> i64 { return 0; }\n",
            "0061736d0100000001370960017f0060047f7f7f7f0060057f7f7f7f7e017e60057f7f7f7f7f017f60017f017f60027f7f017f60027f7e017f6000017f6000017e0285010805736967696c0e6675656c5f64656372656d656e74000005736967696c0473656e64000105736967696c0361736b000205736967696c05737061776e000305736967696c05616c6c6f63000405736967696c0c6361705f7265737472696374000505736967696c096361705f73706c6974000605736967696c086361705f6d696e740007030201080405017001010105030100010607017f014180080b071502066d656d6f727902000842554d505f5054520300090901020041000b0001080a0d010b01017e4200210020000f0b",
        ),
        (
            "call_pair",
            "module m;\nfn g(a: i64) -> i64 { return a + 1; }\nfn f(a: i64) -> i64 { return g(a); }\n",
            "0061736d01000000013d0a60017f0060047f7f7f7f0060057f7f7f7f7e017e60057f7f7f7f7f017f60017f017f60027f7f017f60027f7e017f6000017f60017e017e60017e017e0285010805736967696c0e6675656c5f64656372656d656e74000005736967696c0473656e64000105736967696c0361736b000205736967696c05737061776e000305736967696c05616c6c6f63000405736967696c0c6361705f7265737472696374000505736967696c096361705f73706c6974000605736967696c086361705f6d696e74000703030208090405017001020205030100010607017f014180080b071502066d656d6f727902000842554d505f5054520300090a01020041000b000208090a28021402017e017e42012102200020027c210120010f0b1101017e4101100020001008210120010f0b",
        ),
        (
            "str_fn",
            "module m;\nfn f(a: i64) -> i64 { let s: str = \"hi\"; return a; }\n",
            "0061736d0100000001380960017f0060047f7f7f7f0060057f7f7f7f7e017e60057f7f7f7f7f017f60017f017f60027f7f017f60027f7e017f6000017f60017e017e0285010805736967696c0e6675656c5f64656372656d656e74000005736967696c0473656e64000105736967696c0361736b000205736967696c05737061776e000305736967696c05616c6c6f63000405736967696c0c6361705f7265737472696374000505736967696c096361705f73706c6974000605736967696c086361705f6d696e740007030201080405017001010105030100010607017f014188080b071502066d656d6f727902000842554d505f5054520300090901020041000b0001080a2e012c03017f017f017f41011000410810042101418008210220012002360200410221032001200336020420000f0b0b0901004180080b026869",
        ),
    ];
    for (label, src, expected_hex) in pins {
        let expected = wasm_hex_decode(expected_hex, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&expected, &oracle, label);
    }
}

/// X-W8 (the oracle half): wasm bytes are byte-stable across two independent
/// pipeline runs, over the scalar corpus.
#[test]
fn w0_oracle_wasm_deterministic() {
    for (label, src) in BODY_CORPUS {
        assert_eq!(
            oracle_wasm_bytes(src),
            oracle_wasm_bytes(src),
            "W0 {label}: oracle wasm nondeterministic"
        );
    }
}

/// X-W7 sweep: the oracle wasm rig is TOTAL over every CV corpus (no outer
/// ring, no panic) — the wasm lane's future corpus is pre-cleared.
#[test]
fn w0_oracle_wasm_total_over_cv_corpora() {
    for corpus in CV_CORPORA {
        for (label, src) in *corpus {
            let bytes = oracle_wasm_bytes(src);
            assert!(!bytes.is_empty(), "W0 {label}: empty module");
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-WASM W1: the selfhost wasm lane — the 6th tool blob (`ai_encode_wasm` =
// build → mem → fuel → emit → module assembly), compared as WHOLE-MODULE
// byte-equality vs `wasm::emit` over the same pipeline.
// ─────────────────────────────────────────────────────────────────────────────

/// The WASM tool body: lex → parse → `ai_encode_wasm` (the module hex, or `!!`).
fn ai_wasm_tool_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = ai_encode_wasm(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

fn ai_wasm_wasm() -> &'static [u8] {
    static WW: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    WW.get_or_init(|| {
        compile_tool(&ai_tool(ai_wasm_tool_body()))
            .expect("air WASM tool should compile")
            .wasm
    })
}

/// Run the WASM tool. X-W5: the same 50%-of-FUEL headroom bound.
fn wasm_full_output(src: &str) -> String {
    let result = execute_ephemeral(ai_wasm_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("air WASM tool executes");
    assert!(
        result.fuel_consumed < 150_000_000,
        "WASM tool fuel {} >= 50% of FUEL (X-W5): raise FUEL deliberately",
        result.fuel_consumed
    );
    String::from_utf8(result.output).expect("WASM tool output is UTF-8")
}

/// The SELFHOST-emitted module bytes (the strict hex decode — X-W4).
fn sigil_wasm_bytes(src: &str, label: &str) -> Vec<u8> {
    wasm_hex_decode(&wasm_full_output(src), label)
}

/// The W1 wasm corpus: BODY_CORPUS minus the actor fixture (AG-W-ACTOR) plus
/// the CV-1 folds — every scalar straight-line module.
fn w1_corpus() -> Vec<(&'static str, &'static str)> {
    BODY_CORPUS
        .iter()
        .chain(CV1_EXTRA_CORPUS)
        .filter(|(_, src)| !src.contains("actor"))
        .copied()
        .collect()
}

/// SH-WASM W1 — THE FIRST MODULES EVER EMITTED BY SIGIL ITSELF: whole-module
/// byte-equality over the scalar surface.
#[test]
fn w1_scalar_module_byte_equality() {
    for (label, src) in w1_corpus() {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// X-W8 (the shadow half): the wasm lane is byte-deterministic across two runs.
#[test]
fn w1_wasm_shadow_deterministic() {
    for (label, src) in w1_corpus() {
        assert_eq!(
            wasm_full_output(src),
            wasm_full_output(src),
            "W1 {label}: wasm shadow non-deterministic"
        );
    }
}

/// W1 sweep folds — LEB-boundary + structural stress at whole-module byte
/// equality, permanent. SLEB widths across 63/64/127/128/16384; a >512-byte
/// module (multi-byte body-size + code-section ULEBs); a three-fn module
/// (type/export/table/element scaling); long module/fn names through the
/// mangle; the pinned u32 (div_u/rem_u) and f64 (add) opcodes; shifts + bit
/// ops; a mixed-valtype signature.
const W1_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "w1_sleb_bounds",
        "module m;\nfn f() -> i64 { let a: i64 = 63; let b: i64 = 64; let c: i64 = 127; let d: i64 = 128; let e: i64 = 16384; return a; }\n",
    ),
    (
        "w1_big_body",
        "module m;\nfn f(a: i64) -> i64 { let x1: i64 = a + 1; let x2: i64 = x1 + 2; let x3: i64 = x2 + 3; let x4: i64 = x3 + 4; let x5: i64 = x4 + 5; let x6: i64 = x5 + 6; let x7: i64 = x6 + 7; let x8: i64 = x7 + 8; let x9: i64 = x8 + 9; let x10: i64 = x9 + 10; let x11: i64 = x10 + 11; let x12: i64 = x11 + 12; let x13: i64 = x12 + 13; let x14: i64 = x13 + 14; let x15: i64 = x14 + 15; let x16: i64 = x15 + 16; let x17: i64 = x16 + 17; let x18: i64 = x17 + 18; let x19: i64 = x18 + 19; let x20: i64 = x19 + 20; return x20; }\n",
    ),
    (
        "w1_three_fns",
        "module m;\nfn a(x: i64) -> i64 { return x + 1; }\nfn b(x: i64) -> i64 { return x * 2; }\nfn c(x: bool) -> bool { return x; }\n",
    ),
    (
        "w1_mangle",
        "module longmodname;\nfn somewhat_longer_fn_name(a: i64) -> i64 { return a; }\n",
    ),
    (
        "w1_u32_ops",
        "module m;\nfn f(a: u32, b: u32) -> u32 { let q: u32 = a / b; let r: u32 = a % b; return q; }\n",
    ),
    (
        "w1_f64_add",
        "module m;\nfn f(a: f64, b: f64) -> f64 { let s: f64 = a + b; return s; }\n",
    ),
    (
        "w1_shifts_bits",
        "module m;\nfn f(a: i64, b: i64) -> i64 { let sl: i64 = a << 3; let sr: i64 = b >> 1; let an: i64 = sl & sr; let orv: i64 = an | a; return orv; }\n",
    ),
];

/// The W1 fold parity — whole-module byte equality on each.
#[test]
fn w1_extra_byte_equality() {
    for (label, src) in W1_EXTRA_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-WASM W2: control flow at whole-module byte equality — the emit_block
/// mirror (the block{loop} sandwich, if/else + merge computation incl. the
/// fallthrough/common-successor fallback, dispatch blocks with arm-br depths,
/// TrapIf, typed Ret-None defaults, back-edge fuel).
#[test]
fn w2_cf_module_byte_equality() {
    for corpus in [BODY_CF_CORPUS, BODY_MATCH_CORPUS] {
        for (label, src) in corpus.iter() {
            let sigil = sigil_wasm_bytes(src, label);
            let oracle = oracle_wasm_bytes(src);
            assert_wasm_eq(&sigil, &oracle, label);
        }
    }
}

/// W2 sweep folds — nested-CF byte-equality stress, permanent. The rules each
/// pins: a loop in a MATCH ARM (dispatch_exit DROPPED for the loop body, KEPT
/// for the post-loop continuation — wasm.rs:781-784); if-in-if-in-loop (the
/// `.nested()` depth chain 2 deep); a triple loop (block{loop} sandwiches ×3);
/// dead-after-if (`unreachable` after `end` when merge=None); trap-in-if (the
/// TrapIf if{unreachable} inside an arm + the Unreachable terminator); an
/// all-arms-return match (the dispatch exit's typed Ret-None default 42 00 0f);
/// a bool match (the i32-class eq arm tests).
const W2_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "w2_loop_in_match_arm",
        "module m;\nfn f(x: i64, n: i64) -> i64 { let mut t: i64 = 0; match x { 0 => { let mut i: i64 = 0; while i < n { t = t + 2; i = i + 1; } t = t + 100; }, _ => { t = 1; } } return t; }\n",
    ),
    (
        "w2_if_in_if_in_loop",
        "module m;\nfn f(n: i64) -> i64 { let mut i: i64 = 0; let mut t: i64 = 0; while i < n { if t < 100 { if i < 5 { t = t + 3; } else { t = t + 2; } } else { t = t + 1; } i = i + 1; } return t; }\n",
    ),
    (
        "w2_triple_loop",
        "module m;\nfn f(n: i64) -> i64 { let mut a: i64 = 0; let mut t: i64 = 0; while a < n { let mut b: i64 = 0; while b < n { let mut c: i64 = 0; while c < n { t = t + 1; c = c + 1; } b = b + 1; } a = a + 1; } return t; }\n",
    ),
    (
        "w2_dead_after_if",
        "module m;\nfn f(c: bool) -> i64 { if c { return 1; } else { return 2; } }\n",
    ),
    (
        "w2_trap_in_if",
        "module m;\nfn f(a: i64) -> i64 { if a < 0 { trap(); } else { } return a; }\n",
    ),
    (
        "w2_match_all_return",
        "module m;\nfn f(x: i64) -> i64 { match x { 0 => { return 10; }, 1 => { return 20; }, _ => { return 0; } } }\n",
    ),
    (
        "w2_bool_match",
        "module m;\nfn f(b: bool) -> i64 { match b { true => { return 1; }, false => { return 2; } } }\n",
    ),
];

/// The W2 fold parity — whole-module byte equality on each.
#[test]
fn w2_extra_byte_equality() {
    for (label, src) in W2_EXTRA_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-WASM W3: memory ops + constructs + the data section at whole-module byte
/// equality — the full remaining stmt alphabet (LF/SF/LD/SD/Wrap/BA/StrLit)
/// over the construct/array/string/enum/index + for-in corpora.
#[test]
fn w3_mem_module_byte_equality() {
    for corpus in [
        BODY_FORIN_CORPUS,
        BODY_FORRANGE_CORPUS,
        BODY_FIELD_CORPUS,
        BODY_WRITE_CORPUS,
        BODY_CONSTRUCT_CORPUS,
        BODY_ARRAY_CORPUS,
        BODY_STRING_CORPUS,
        BODY_ENUM_CORPUS,
        BODY_INDEX_CORPUS,
    ] {
        for (label, src) in corpus.iter() {
            let sigil = sigil_wasm_bytes(src, label);
            let oracle = oracle_wasm_bytes(src);
            assert_wasm_eq(&sigil, &oracle, label);
        }
    }
}

/// W3 sweep folds — data-layout + write/operand literal-typing stress at
/// whole-module byte equality, permanent. The alignment pair brackets the
/// 8-align bump-start boundary; dedup3 pins content dedup with an interleaved
/// unique; the three `*_lit_*` cases are the LITERAL-TYPING regression suite
/// (the W3 byte-diff caught the shadow defaulting literal write-RHS and binary
/// operands to I64 where the oracle types them from the PLACE/operand — fixed
/// in cv_to_var/cv_into/cv_expr_tytok + both write arms).
const W3_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "w3_str_align7",
        "module m;\nfn f(a: i64) -> i64 { let s: str = \"seven77\"; return a; }\n",
    ),
    (
        "w3_str_align8",
        "module m;\nfn f(a: i64) -> i64 { let s: str = \"eight888\"; return a; }\n",
    ),
    (
        "w3_str_dedup3",
        "module m;\nfn f(a: i64) -> i64 { let s: str = \"dup\"; let t: str = \"uniq\"; let u: str = \"dup\"; return a; }\n",
    ),
    (
        "w3_rec_str_field",
        "module m;\nrecord S { name: str, n: i64 }\nfn f(a: i64) -> i64 { let s: S = S { name: \"nm\", n: a }; return s.n; }\n",
    ),
    (
        "w3_ix_in_loop",
        "module m;\nfn f(arr: [i64; 4], n: i64) -> i64 { let mut i: i64 = 0; let mut t: i64 = 0; while i < n { let v: i64 = arr[i]; t = t + v; i = i + 1; } return t; }\n",
    ),
    (
        "w3_u32_arr_write_lit",
        "module m;\nfn f(arr: [u32; 4] @Mut, i: i64) -> u32 { arr[i] = 5; return arr[i]; }\n",
    ),
    (
        "w3_u32_field_write_lit",
        "module m;\nrecord R { x: i64, y: u32 }\nfn f(r: R @Mut) -> u32 { r.y = 7; return r.y; }\n",
    ),
    (
        "w3_u32_lit_bin",
        "module m;\nfn f(a: u32) -> u32 { let q: u32 = a + 1; return q; }\n",
    ),
];

/// The W3 fold parity — whole-module byte equality on each.
#[test]
fn w3_extra_byte_equality() {
    for (label, src) in W3_EXTRA_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-WASM W4: calls + multi-fn at whole-module byte equality — the Call
/// instruction (get args, `call(8 + FuncId)`, set dst) over the call corpus.
#[test]
fn w4_call_module_byte_equality() {
    for (label, src) in BODY_CALL_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-WASM W4 — THE ALL-CORPORA BYTE-EQUALITY DECLARATION: every free-fn CV
/// corpus fixture (the 12 corpora + all fold sets) emits a whole module
/// byte-identical to `wasm::emit`. Actor fixtures ride the dedicated
/// `w4_actor_module_byte_equality` (their export/index basis differs).
#[test]
fn w4_all_corpora_byte_equality() {
    for corpus in CV_CORPORA {
        for (label, src) in corpus.iter().filter(|(_, s)| !s.contains("actor")) {
            let sigil = sigil_wasm_bytes(src, label);
            let oracle = oracle_wasm_bytes(src);
            assert_wasm_eq(&sigil, &oracle, label);
        }
    }
    for corpus in [
        CV1_EXTRA_CORPUS,
        CV2_EXTRA_CORPUS,
        CV3_EXTRA_CORPUS,
        CV4_EXTRA_CORPUS,
        CV5_EXTRA_CORPUS,
        W1_EXTRA_CORPUS,
        W2_EXTRA_CORPUS,
        W3_EXTRA_CORPUS,
    ] {
        for (label, src) in corpus.iter().filter(|(_, s)| !s.contains("actor")) {
            let sigil = sigil_wasm_bytes(src, label);
            let oracle = oracle_wasm_bytes(src);
            assert_wasm_eq(&sigil, &oracle, label);
        }
    }
}

/// SH-WASM W4: actor modules join the wasm lane — the `{actor}__{fn}` export
/// mangle + the full-vec FuncId basis (init/handlers occupy call indices).
#[test]
fn w4_actor_module_byte_equality() {
    let cases: &[(&str, &str)] = &[
        (
            "act_handler_rec",
            "module m;\nrecord R { x: i64 }\nactor A {\n  init() { }\n  on ping(a: i64) -> i64 { let r: R = R { x: a }; return r.x; }\n}\n",
        ),
        (
            "act_plus_free_call",
            "module m;\nactor A {\n  init() { }\n  on ping(a: i64) -> i64 { return a; }\n}\nfn g(x: i64) -> i64 { return x + 1; }\nfn f(x: i64) -> i64 { return g(x); }\n",
        ),
    ];
    for (label, src) in cases {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-WASM W4: a REAL stdlib module as a whole WASM module — `abi.sigil`
/// (3 bit-ops helpers) emits byte-identical bytecode (the SH-MEM census's
/// abi parity, now at the wasm rung).
#[test]
fn w4_stdlib_abi_module() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../stdlib/sigil/abi.sigil");
    let src = std::fs::read_to_string(path).expect("abi.sigil readable");
    let sigil = sigil_wasm_bytes(&src, "abi");
    let oracle = oracle_wasm_bytes(&src);
    assert_wasm_eq(&sigil, &oracle, "abi");
}

/// W4 sweep folds — call + multi-fn + actor byte-equality stress, permanent.
/// 3-arg calls (arg-order emission); chained calls (a call result feeding the
/// next); a call in a loop body (Call + the F1 back-edge fuel coexisting); a
/// bin-expr call arg (the arg mats before the call); recursion (self-FuncId);
/// a multi-handler actor (two handler exports + the full-vec index); an actor
/// with an init body; a five-fn chain (the FuncId basis scales); a call with a
/// live string literal (the DATA section + calls together).
const W4_EXTRA_CORPUS: &[(&str, &str)] = &[
    (
        "w4_call_3args",
        "module m;\nfn g(a: i64, b: i64, c: i64) -> i64 { return a + b + c; }\nfn f(a: i64) -> i64 { return g(a, 2, 3); }\n",
    ),
    (
        "w4_chained_calls",
        "module m;\nfn g(a: i64) -> i64 { return a + 1; }\nfn h(a: i64) -> i64 { return a * 2; }\nfn f(a: i64) -> i64 { let x: i64 = g(a); let y: i64 = h(x); return y; }\n",
    ),
    (
        "w4_call_in_loop",
        "module m;\nfn g(a: i64) -> i64 { return a + 1; }\nfn f(n: i64) -> i64 { let mut i: i64 = 0; let mut t: i64 = 0; while i < n { t = g(t); i = i + 1; } return t; }\n",
    ),
    (
        "w4_recursion",
        "module m;\nfn f(n: i64) -> i64 { if n < 1 { return 0; } return f(n - 1); }\n",
    ),
    (
        "w4_multi_handler",
        "module m;\nactor A {\n  init() { }\n  on ping(a: i64) -> i64 { return a + 1; }\n  on pong(a: i64) -> i64 { return a * 2; }\n}\n",
    ),
    (
        "w4_five_fns",
        "module m;\nfn a(x: i64) -> i64 { return x + 1; }\nfn b(x: i64) -> i64 { return a(x); }\nfn c(x: i64) -> i64 { return b(x); }\nfn d(x: i64) -> i64 { return c(x); }\nfn e(x: i64) -> i64 { return d(x); }\n",
    ),
    (
        "w4_call_str_arg",
        "module m;\nfn g(a: i64) -> i64 { return a; }\nfn f(a: i64) -> i64 { let s: str = \"hi\"; return g(a); }\n",
    ),
];

/// The W4 fold parity — whole-module byte equality on each.
#[test]
fn w4_extra_byte_equality() {
    for (label, src) in W4_EXTRA_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-WASM W5: the execution capstone. The SELFHOST-emitted modules RUN via
// execute_ephemeral (the production runtime) and produce outputs identical to
// the oracle build — byte-equality already implies it, but this is the
// end-to-end proof that SIGIL-emitted WASM actually EXECUTES. The rung flips.
// ─────────────────────────────────────────────────────────────────────────────

/// Run a `tool_main` module via the production runtime and recover the value
/// from the negative-sentinel trap (`return 0 - value;` -> "tool returned error
/// (value)"). Mirrors array_contains.rs's neg().
fn w5_run_neg_sentinel(bytes: &[u8], label: &str) -> i64 {
    match execute_ephemeral(bytes, b"", FUEL, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("W5 {label}: expected a neg-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("W5 {label}: malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("W5 {label}: can't parse {message:?}: {e}"))
        }
        Err(other) => panic!("W5 {label}: non-trap error: {other:?}"),
        Ok(_) => panic!("W5 {label}: expected a negative sentinel, got a positive packed pointer"),
    }
}

/// The W5 tool corpus: `tool_main`-shaped, covered-surface, value-returning via
/// the neg-sentinel. Each exercises a different slice of the emitter.
const W5_TOOL_CORPUS: &[(&str, &str, i64)] = &[
    (
        "w5_arith",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = 40; let b: i64 = 2; let s: i64 = a + b; return 0 - s; }\n",
        42,
    ),
    (
        "w5_loop_sum",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut i: i64 = 0; let mut acc: i64 = 0; while i < 5 { acc = acc + i; i = i + 1; } return 0 - acc; }\n",
        10,
    ),
    (
        "w5_branch",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: i64 = 7; if x > 5 { return 0 - 100; } else { return 0 - 200; } }\n",
        100,
    ),
    (
        "w5_call",
        "module tool;\nfn dbl(x: i64) -> i64 { return x * 2; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: i64 = dbl(21); return 0 - r; }\n",
        42,
    ),
    (
        "w5_match",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let k: i64 = 1; match k { 0 => { return 0 - 5; }, 1 => { return 0 - 55; }, _ => { return 0 - 999; } } }\n",
        55,
    ),
    (
        "w5_array",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let xs: [i64; 3] = [11, 22, 33]; let v: i64 = xs[1]; return 0 - v; }\n",
        22,
    ),
    (
        "w5_record",
        "module tool;\nrecord R { x: i64, y: i64 }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: R = R { x: 7, y: 35 }; return 0 - r.y; }\n",
        35,
    ),
    (
        "w5_recursion",
        "module tool;\nfn sum(n: i64) -> i64 { if n < 1 { return 0; } let r: i64 = sum(n - 1); return n + r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: i64 = sum(9); return 0 - s; }\n",
        45,
    ),
    (
        "w5_field_write",
        "module tool;\nrecord R { x: i64 }\nfn bump(r: R @Mut) -> i64 { r.x = 88; return r.x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: R = R { x: 1 }; let v: i64 = bump(r); return 0 - v; }\n",
        88,
    ),
    (
        "w5_arr_write",
        "module tool;\nfn setget(a: [i64; 3] @Mut) -> i64 { a[2] = 77; return a[2]; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let xs: [i64; 3] = [1, 2, 3]; let v: i64 = setget(xs); return 0 - v; }\n",
        77,
    ),
    (
        "w5_nested_loop",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut i: i64 = 0; let mut t: i64 = 0; while i < 3 { let mut j: i64 = 0; while j < 3 { t = t + 1; j = j + 1; } i = i + 1; } return 0 - t; }\n",
        9,
    ),
];

/// SH-WASM W5 — THE CAPSTONE: for each tool fixture, the selfhost-emitted bytes
/// are byte-identical to the oracle's AND, run on the production runtime, they
/// compute the expected value (and the oracle bytes compute the same). SIGIL
/// emits WASM that RUNS.
#[test]
fn w5_selfhost_execution() {
    for (label, src, expected) in W5_TOOL_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
        let sv = w5_run_neg_sentinel(&sigil, label);
        assert_eq!(
            sv, *expected,
            "W5 {label}: selfhost module computed wrong value"
        );
        let ov = w5_run_neg_sentinel(&oracle, label);
        assert_eq!(
            sv, ov,
            "W5 {label}: selfhost vs oracle runtime result diverged"
        );
    }
}

/// X-W8 (the shadow half) — the wasm lane is byte-deterministic across two runs
/// over the ENTIRE covered surface (every free-fn CV corpus + fold set), and the
/// X-W5 fuel-headroom assert (inside wasm_full_output) rides every call: this
/// doubles as the fuel-headroom census.
#[test]
fn w5_wasm_shadow_deterministic_and_fuel_census() {
    for corpus in CV_CORPORA {
        for (_, src) in corpus.iter().filter(|(_, s)| !s.contains("actor")) {
            assert_eq!(
                wasm_full_output(src),
                wasm_full_output(src),
                "W5: wasm shadow non-deterministic:\n{src}"
            );
        }
    }
    for corpus in [
        CV1_EXTRA_CORPUS,
        CV2_EXTRA_CORPUS,
        CV3_EXTRA_CORPUS,
        CV4_EXTRA_CORPUS,
        CV5_EXTRA_CORPUS,
        W1_EXTRA_CORPUS,
        W2_EXTRA_CORPUS,
        W3_EXTRA_CORPUS,
        W4_EXTRA_CORPUS,
    ] {
        for (_, src) in corpus.iter().filter(|(_, s)| !s.contains("actor")) {
            assert_eq!(
                wasm_full_output(src),
                wasm_full_output(src),
                "W5: wasm shadow non-deterministic:\n{src}"
            );
        }
    }
}

/// SH-SURFACE ST-1: bare enum variants at whole-module byte-equality (the wasm lane) — the
/// precedence-critical `bare_local_shadows_variant` fixture proves X-ST1 (a local named `A` beats
/// the variant `A`). CV/mem/fuel parity rides `w4_all_corpora_byte_equality` + the CV lanes via
/// CV_CORPORA; this pins the wasm lane directly.
#[test]
fn st1_bare_variant_byte_equality() {
    for (label, src) in BODY_BARE_ENUM_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-SURFACE ST-1: a bare-constructed enum RUNS — construct `B(v)` bare, read its payload back,
/// return it via the neg-sentinel; run == expected == oracle_run.
#[test]
fn st1_bare_variant_execution() {
    let src = "module tool;\nenum E { A, B(i64) }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: i64 = 41; let e: E = B(x); let g: E = A; return 0 - x; }\n";
    let sigil = sigil_wasm_bytes(src, "st1_exec");
    let oracle = oracle_wasm_bytes(src);
    assert_wasm_eq(&sigil, &oracle, "st1_exec");
    let sv = w5_run_neg_sentinel(&sigil, "st1_exec");
    assert_eq!(sv, 41, "ST-1 exec: bare-constructed enum ran wrong");
    assert_eq!(
        sv,
        w5_run_neg_sentinel(&oracle, "st1_exec"),
        "ST-1 exec: selfhost vs oracle run"
    );
}

/// SH-SURFACE ST-2: dot-method calls at whole-module byte-equality (the wasm lane). The impl-method
/// DEFINITION (Type__method, self as param0) + the CALL (Call(fid, [receiver, ...args])) both land;
/// `m_method_plus_freefn` proves the full-vec FuncId basis (the method + the free fn interleave).
#[test]
fn st2_method_byte_equality() {
    for (label, src) in BODY_METHOD_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-SURFACE ST-2: a dot-method call RUNS — `p.get()` on a constructed record, returned via the
/// neg-sentinel; run == expected == oracle_run.
#[test]
fn st2_method_execution() {
    let src = "module tool;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let p: P = P { x: 41 }; let v: i64 = p.get(); return 0 - v; }\n";
    let sigil = sigil_wasm_bytes(src, "st2_exec");
    let oracle = oracle_wasm_bytes(src);
    assert_wasm_eq(&sigil, &oracle, "st2_exec");
    let sv = w5_run_neg_sentinel(&sigil, "st2_exec");
    assert_eq!(sv, 41, "ST-2 exec: dot-method ran wrong");
    assert_eq!(
        sv,
        w5_run_neg_sentinel(&oracle, "st2_exec"),
        "ST-2 exec: selfhost vs oracle run"
    );
}

/// SH-SURFACE ST-3: tuples at whole-module byte-equality (the wasm lane). Construct
/// (`$tupleN__..` positional SF) + `let (x,y)=t` destructure (per-element LF) + the tuple-RHS
/// temp+copy all land; `t_triple`/`t_mixed_width` pin the arity + alignment paths.
#[test]
fn st3_tuple_byte_equality() {
    for (label, src) in BODY_TUPLE_CORPUS {
        let sigil = sigil_wasm_bytes(src, label);
        let oracle = oracle_wasm_bytes(src);
        assert_wasm_eq(&sigil, &oracle, label);
    }
}

/// SH-SURFACE ST-3: a tuple constructed then destructured RUNS — `let t=(a,b); let (x,y)=t`
/// summed and returned via the neg-sentinel; run == expected == oracle_run.
#[test]
fn st3_tuple_execution() {
    let src = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let t: (i64, i64) = (25, 16); let (x, y) = t; return 0 - (x + y); }\n";
    let sigil = sigil_wasm_bytes(src, "st3_exec");
    let oracle = oracle_wasm_bytes(src);
    assert_wasm_eq(&sigil, &oracle, "st3_exec");
    let sv = w5_run_neg_sentinel(&sigil, "st3_exec");
    assert_eq!(sv, 41, "ST-3 exec: tuple destructure ran wrong");
    assert_eq!(
        sv,
        w5_run_neg_sentinel(&oracle, "st3_exec"),
        "ST-3 exec: selfhost vs oracle run"
    );
}

#[test]
fn retired_lane_cases_are_exact_or_poisoned() {
    let mut poisoned = Vec::new();
    let mut outer_exact = Vec::new();
    for (label, src) in RETIRED_LANE_CORPUS {
        let (mem_p, _) = memory::lower(lower_oracle(src));
        let (fuel_p, _) = fuel::insert(mem_p);
        let emitted = wasm::emit(&fuel_p);
        if emitted.outer.is_some() {
            let oracle = oracle_cv_projection(src, true);
            let shadow = sigil_cv_mem_projection(src);
            if shadow == oracle {
                outer_exact.push(*label);
            } else if shadow.iter().any(|line| line.contains('!')) {
                poisoned.push(*label);
            } else {
                panic!("retired AIR case `{label}` produced divergent outer-ring AIR");
            }
            continue;
        }

        let shadow = wasm_full_output(src);
        if shadow.starts_with("!!") {
            poisoned.push(*label);
        } else {
            let shadow = wasm_hex_decode(&shadow, label);
            assert_wasm_eq(&shadow, &emitted.inner, label);
        }
    }
    assert_eq!(
        poisoned, RETIRED_LANE_POISON_CASES,
        "retired AIR projection cases changed exact/poison disposition"
    );
    assert_eq!(
        outer_exact, RETIRED_LANE_OUTER_EXACT_CASES,
        "retired AIR projection cases changed outer-ring exact disposition"
    );
}

#[test]
fn air_semantic_evidence_manifest() {
    use std::collections::BTreeSet;

    let corpora: &[(&str, &[(&str, &str)])] = &[
        ("body", BODY_CORPUS),
        ("control_flow", BODY_CF_CORPUS),
        ("match", BODY_MATCH_CORPUS),
        ("for_in", BODY_FORIN_CORPUS),
        ("for_range", BODY_FORRANGE_CORPUS),
        ("field", BODY_FIELD_CORPUS),
        ("write", BODY_WRITE_CORPUS),
        ("call", BODY_CALL_CORPUS),
        ("construct", BODY_CONSTRUCT_CORPUS),
        ("array", BODY_ARRAY_CORPUS),
        ("string", BODY_STRING_CORPUS),
        ("enum", BODY_ENUM_CORPUS),
        ("index", BODY_INDEX_CORPUS),
        ("bare_enum", BODY_BARE_ENUM_CORPUS),
        ("tuple", BODY_TUPLE_CORPUS),
        ("method", BODY_METHOD_CORPUS),
        ("cv1_extra", CV1_EXTRA_CORPUS),
        ("cv2_extra", CV2_EXTRA_CORPUS),
        ("cv3_extra", CV3_EXTRA_CORPUS),
        ("cv4_extra", CV4_EXTRA_CORPUS),
        ("cv5_extra", CV5_EXTRA_CORPUS),
        ("fuel_extra", F1_EXTRA_CORPUS),
        ("wasm1_extra", W1_EXTRA_CORPUS),
        ("wasm2_extra", W2_EXTRA_CORPUS),
        ("wasm3_extra", W3_EXTRA_CORPUS),
        ("wasm4_extra", W4_EXTRA_CORPUS),
        ("retired_lane", RETIRED_LANE_CORPUS),
    ];

    let mut cases = BTreeSet::new();
    for (corpus, entries) in corpora {
        assert!(!entries.is_empty(), "semantic corpus `{corpus}` is empty");
        for (label, _) in *entries {
            assert!(
                cases.insert(format!("{corpus}::{label}")),
                "duplicate semantic AIR case `{corpus}::{label}`"
            );
        }
    }
    for (label, _, _) in W5_TOOL_CORPUS {
        assert!(
            cases.insert(format!("wasm5_tool::{label}")),
            "duplicate semantic AIR case `wasm5_tool::{label}`"
        );
    }
    assert!(
        cases.len() >= air_case_manifest::CORPUS_CASE_FLOOR,
        "semantic AIR corpus fell to {} cases (floor {})",
        cases.len(),
        air_case_manifest::CORPUS_CASE_FLOOR
    );

    let source = include_str!("air_differential.rs");
    let mut required = BTreeSet::new();
    for name in air_case_manifest::REQUIRED_EVIDENCE_TESTS {
        assert!(
            required.insert(name),
            "duplicate required AIR check `{name}`"
        );
        assert!(
            source.contains(&format!("\nfn {name}(")),
            "required semantic AIR check `{name}` was removed"
        );
    }
}
