//! SOL0 Solidity → SIGIL frontend tests. Mirrors the TypeScript suite's shape:
//! golden translation (hand-authored), round-trip validity (emitted SIGIL
//! compiles), one conformance assertion per fail-closed constraint, the synergy
//! signal (overflow-safe-by-construction), determinism, and a totality/fuzz pass.

use std::path::PathBuf;

use proptest::prelude::*;

use sigil_compiler::compile_named_module;
use sigil_frontends::{EmittedSigil, Frontend, FrontendDiag, frontend_for};

fn sol() -> Box<dyn Frontend> {
    frontend_for("solidity").expect("solidity frontend registered")
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/frontends/solidity")
}

fn norm(s: &str) -> String {
    s.replace("\r\n", "\n")
}

fn translate_ok(src: &str, name: &str) -> EmittedSigil {
    sol()
        .translate(src, name)
        .unwrap_or_else(|d| panic!("translate `{name}` failed unexpectedly: {d:?}"))
}

fn translate_err(src: &str) -> Vec<FrontendDiag> {
    sol()
        .translate(src, "c.sol")
        .expect_err("expected a translation error")
}

fn sol_files(sub: &str) -> Vec<PathBuf> {
    let dir = fixtures_dir().join(sub);
    let mut v: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {dir:?}: {e}"))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("sol"))
        .collect();
    v.sort();
    v
}

// ── 1. Golden translation (hand-authored goldens) ────────────────────────────
#[test]
fn golden_translation() {
    for p in sol_files("compile") {
        let src = std::fs::read_to_string(&p).unwrap();
        let golden_path = p.with_extension("sigil");
        let golden = std::fs::read_to_string(&golden_path)
            .unwrap_or_else(|_| panic!("missing golden {golden_path:?}"));
        let emitted = translate_ok(&src, p.to_str().unwrap());
        assert_eq!(
            norm(&emitted.text),
            norm(&golden),
            "golden mismatch for {p:?}"
        );
    }
}

// ── 2. Round-trip: every emitted golden compiles clean through the real compiler.
#[test]
fn round_trip_compiles() {
    for p in sol_files("compile") {
        let src = std::fs::read_to_string(&p).unwrap();
        let emitted = translate_ok(&src, p.to_str().unwrap());
        compile_named_module(emitted.source_name.clone(), emitted.text.clone()).unwrap_or_else(
            |e| {
                let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
                panic!(
                    "emitted SIGIL for {p:?} must compile, got {codes:?}\n--- emitted ---\n{}",
                    emitted.text
                )
            },
        );
    }
}

// ── 3. Conformance: one reject fixture per fail-closed constraint (FE4xx). ────
#[test]
fn reject_fixtures_match_expected_codes() {
    for p in sol_files("reject") {
        let src = std::fs::read_to_string(&p).unwrap();
        let want = src
            .lines()
            .find_map(|l| l.trim().strip_prefix("// expect-fe:"))
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| panic!("reject fixture {p:?} missing `// expect-fe:` header"));
        let got = translate_err(&src)
            .first()
            .expect("at least one diagnostic")
            .code;
        assert_eq!(got, want, "wrong FE-code for {p:?}");
    }
}

// ── 4. The synergy signal: overflow-safe-by-construction. ────────────────────
// The emitted Vault routes the balance debit through a CHECKED u256 subtraction
// (which traps on underflow — the classic drain bug is impossible) behind a
// faithful `require`→`trap_if` guard. (A full runtime trap-proof — execute the
// wasm, assert the underflow path reverts — is a follow-on.)
#[test]
fn vault_is_overflow_safe_by_construction() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/vault.sol")).unwrap();
    let emitted = translate_ok(&src, "vault.sol");
    assert!(
        emitted.text.contains("trap_if("),
        "the require guard must lower to a trap_if"
    );
    assert!(
        emitted.text.contains("self.balance = self.balance - "),
        "the debit must be a checked u256 subtraction (overflow-safe by construction)"
    );
    // And it compiles — the checked-u256 semantics are real, not asserted prose.
    compile_named_module(emitted.source_name, emitted.text).expect("vault must compile");
}

// ── 5. Determinism: two translations are byte-identical. ─────────────────────
#[test]
fn deterministic_emission() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/vault.sol")).unwrap();
    let a = translate_ok(&src, "vault.sol").text;
    let b = translate_ok(&src, "vault.sol").text;
    assert_eq!(a, b);
}

// ── 6. Totality: never panics / hangs on arbitrary input (Ok or Err only). ───
proptest! {
    #[test]
    fn never_panics_on_arbitrary_input(s in ".{0,400}") {
        let _ = sol().translate(&s, "fuzz.sol");
    }
}

// ── 7. Depth cap: deep nesting rejects (FE402) without a stack overflow. ─────
#[test]
fn depth_cap_rejects_without_overflow() {
    let mut cond = String::from("a");
    for _ in 0..5000 {
        cond = format!("({cond} + 1)");
    }
    let src = format!(
        "pragma solidity ^0.8.0;\ncontract C {{ uint256 b; function f(uint256 a) public {{ b = {cond}; }} }}"
    );
    let diags = sol()
        .translate(&src, "deep.sol")
        .expect_err("deep nesting must reject");
    assert_eq!(
        diags.first().unwrap().code,
        sigil_frontends::codes::FE402_TOO_LARGE_SOL
    );
}

// ── 7b. Totality, the struct-reference axis: a deep struct→struct-field chain must ──
// reject (FE402) without a stack overflow. struct→struct references are a recursion axis
// the per-body MAX_NEST_DEPTH never measured; an unbounded chain overflowed the native
// stack in `detect_struct_cycle`'s DFS AND (via `zero_default`→the trusted re-parse self-
// check, ~depth 18) at emit. The `validate_struct_defs` depth cap rejects before either
// overflow. Reaching this assertion IS the proof of totality. (SOL-STRUCT adversarial
// review.)
#[test]
fn struct_reference_depth_rejects_without_overflow() {
    let mut src = String::from("pragma solidity ^0.8.0;\ncontract C {\n");
    // S0 → S1 → … → S3999 → S4000 (a scalar leaf). The `S0 head;` state field would also
    // force `zero_default` to recurse the whole chain at emit (the second overflow site).
    for i in 0..4000 {
        src.push_str(&format!("    struct S{i} {{ S{} a; }}\n", i + 1));
    }
    src.push_str("    struct S4000 { uint256 a; }\n    S0 head;\n}\n");
    let diags = sol()
        .translate(&src, "deepstruct.sol")
        .expect_err("a deep struct-reference chain must reject");
    assert_eq!(
        diags.first().unwrap().code,
        sigil_frontends::codes::FE402_TOO_LARGE_SOL
    );
}

// ── 8. Totality, the second axis: STATEMENT and UNARY nesting must also reject ─
// (FE402) without a stack overflow. The expression depth guard alone left the
// statement path (nested `if`, `else if` chains, `unchecked` nesting) and unary
// self-recursion (`!`/`-` chains) unbounded — adversarial nesting crashed the
// process (STATUS_STACK_OVERFLOW). This test reaching its assertions IS the proof
// the parser stays total. (Found by the SOL0 adversarial review.)
#[test]
fn statement_and_unary_nesting_reject_without_overflow() {
    let pre = "pragma solidity ^0.8.0;\n";
    let nested_if = format!(
        "{pre}contract C {{ uint256 b; function f(uint256 a) public {{ {}b=a;{} }} }}",
        "if (a > 0) {".repeat(4000),
        "}".repeat(4000)
    );
    let else_if = format!(
        "{pre}contract C {{ uint256 b; function f(uint256 a) public {{ if(a>0){{b=1;}} {} }} }}",
        "else if (a > 0) { b = 1; } ".repeat(4000)
    );
    let unary_not = format!(
        "{pre}contract C {{ function f() public pure returns (bool) {{ return {}true; }} }}",
        "!".repeat(50000)
    );
    let unary_neg = format!(
        "{pre}contract C {{ function f() public pure returns (uint256) {{ return {}1; }} }}",
        "-".repeat(50000)
    );
    let nested_unchecked = format!(
        "{pre}contract C {{ function f() public {{ {}{} }} }}",
        "unchecked {".repeat(4000),
        "}".repeat(4000)
    );
    // FLAT operator/postfix chains: these parse at constant RECURSION depth (a loop,
    // not re-entry) but build an N-deep AST that overflows the downstream walkers /
    // trusted re-parse / recursive Drop — the depth counter must be threaded through
    // the precedence/postfix loops too, not just the re-entrant descents.
    let binary_add = format!(
        "{pre}contract C {{ uint256 s; function f(uint256 a) public {{ s = a{}; }} }}",
        " + a".repeat(5000)
    );
    let binary_eq = format!(
        "{pre}contract C {{ function f(uint256 a) public pure returns (bool) {{ return a{}; }} }}",
        " == a".repeat(5000)
    );
    let and_chain = format!(
        "{pre}contract C {{ function f(bool a) public pure returns (bool) {{ return a{}; }} }}",
        " && a".repeat(5000)
    );
    // Member chain in EXPRESSION position (a statement-leading `x.y…` is an
    // assignment target and rejects at the first `.`; the postfix loop is only
    // reached inside an expression like a `return`).
    let member_chain = format!(
        "{pre}contract C {{ function f(uint256 a) public pure returns (uint256) {{ return a{}; }} }}",
        ".y".repeat(5000)
    );
    // SOL1 LM10: a deep index chain `a[a[…a…]]` (the new `[]` postfix rule) and a deep
    // nested mapping TYPE `mapping(a => mapping(a => … u …))` must both reject (FE402)
    // without overflowing the parser, the downstream walkers, or the trusted re-parse.
    let index_chain = format!(
        "{pre}contract C {{ function f(uint256 a) public pure returns (uint256) {{ return {}a{}; }} }}",
        "a[".repeat(5000),
        "]".repeat(5000)
    );
    let mapping_chain = format!(
        "{pre}contract C {{ {}uint256{} x; }}",
        "mapping(address => ".repeat(5000),
        ")".repeat(5000)
    );
    for (label, src) in [
        ("nested_if", nested_if),
        ("else_if", else_if),
        ("unary_not", unary_not),
        ("unary_neg", unary_neg),
        ("nested_unchecked", nested_unchecked),
        ("binary_add", binary_add),
        ("binary_eq", binary_eq),
        ("and_chain", and_chain),
        ("member_chain", member_chain),
        ("index_chain", index_chain),
        ("mapping_chain", mapping_chain),
    ] {
        match sol().translate(&src, "deep.sol") {
            Ok(_) => panic!("{label}: deep nesting must reject, not translate"),
            Err(diags) => assert_eq!(
                diags.first().unwrap().code,
                sigil_frontends::codes::FE402_TOO_LARGE_SOL,
                "{label}: expected FE402"
            ),
        }
    }
}

// ── 9. Pragma gate (NC-S3): accept the in-range >=0.8.0 forms (incl. the common
// space-after-operator style), reject pre-0.8, fabricated majors, malformed
// versions, and bare-substring `solidityN` directives.
#[test]
fn pragma_variants_are_gated() {
    let body = "contract C { uint256 x; function g() public view returns (uint256) { return x; } }";
    let ok = |p: &str| {
        sol()
            .translate(&format!("pragma solidity {p};\n{body}"), "c.sol")
            .is_ok()
    };
    let bad = |p: &str| {
        sol()
            .translate(&format!("pragma solidity {p};\n{body}"), "c.sol")
            .is_err()
    };
    // Accept: caret, >=, exact, and a multi-constraint range — with or without a
    // space after the operator (`>= 0.8.0` is idiomatic Solidity).
    assert!(ok("^0.8.0"), "^0.8.0");
    assert!(ok(">=0.8.0"), ">=0.8.0");
    assert!(ok(">= 0.8.0"), ">= 0.8.0 (space after operator)");
    assert!(ok("0.8.19"), "bare 0.8.19");
    assert!(ok(">=0.8.2 <0.9.0"), "range");
    // Reject: pre-0.8 floor, fabricated majors, trailing junk, extra components.
    for p in [
        "^0.7.0", ">=0.7.0", "<0.9.0", "^2.0.0", "1.0.0", "0.8.x", "0.8.0.1",
    ] {
        assert!(bad(p), "{p} must be rejected");
    }
    // A bare-substring directive (no word boundary) is not the solidity pragma →
    // treated as missing → reject.
    assert!(
        sol()
            .translate(&format!("pragma solidity8.0;\n{body}"), "c.sol")
            .is_err(),
        "solidity8.0 substring must not satisfy the pragma gate"
    );
}

// ── 10. `require(cond, "reason")` — the most common Solidity form — translates,
// dropping the reason (NC AG-S4), and the guard still lowers to a trap.
#[test]
fn require_reason_is_dropped() {
    let src = "pragma solidity ^0.8.0;\ncontract C { uint256 b; \
               function f(uint256 a) public { require(a >= b, \"insufficient balance\"); b = a; } }";
    let emitted = translate_ok(src, "c.sol");
    assert!(
        emitted.text.contains("trap_if(!((a >= self.b)))"),
        "the reason-bearing require must still lower to a guard:\n{}",
        emitted.text
    );
    assert!(
        !emitted.text.contains("insufficient"),
        "the reason string must be dropped, not emitted"
    );
    compile_named_module(emitted.source_name, emitted.text).expect("must compile");
}

// ── 11. CEI scope alignment: a local that SHADOWS a state field is not a storage
// write, so writing+guarding it is in-subset (and compiles); a genuine state
// write before a guard still rejects (FE412). (Found by the SOL0 adversarial review.)
#[test]
fn local_shadowing_state_field_is_not_a_storage_write() {
    let ok_src = "pragma solidity ^0.8.0;\ncontract C { uint256 bal; \
        function f(uint256 x) public returns (uint256) { uint256 bal = x; bal = bal + 1; require(bal > 0); return bal; } }";
    let emitted = translate_ok(ok_src, "c.sol");
    compile_named_module(emitted.source_name, emitted.text).expect("local-shadow must compile");

    let bad_src = "pragma solidity ^0.8.0;\ncontract C { uint256 bal; \
        function f(uint256 x) public { bal = x; require(bal > 0); } }";
    match sol().translate(bad_src, "c.sol") {
        Ok(_) => panic!("a real state-write-then-require must reject"),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE412_NON_CEI
        ),
    }
}

// ── 12. CEI scope correctness: a branch-local shadow must NOT leak past the `if`.
// A local declared inside a branch, then a post-if write to the SAME name (which is
// the state field again, by Solidity block scoping) followed by a trap, must reject
// FE412 — proving check/emit scope `locals` per branch rather than relying on a
// leaked shadow + the trusted compiler's undefined-name path. (SOL0 re-review.)
#[test]
fn branch_local_shadow_does_not_leak_past_if() {
    let src = "pragma solidity ^0.8.0;\ncontract C { uint256 x; \
        function f(uint256 a) public { if (a > 0) { uint256 x = a + 1; } x = a; require(a > 5); } }";
    match sol().translate(src, "c.sol") {
        Ok(e) => panic!(
            "post-if state write + trap must reject FE412, not translate:\n{}",
            e.text
        ),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE412_NON_CEI,
            "the branch-local must not leak, so the post-if `x = a` is a state write"
        ),
    }
}

// ── 13. SOL1b: `&&` short-circuit is STRUCTURALLY preserved (NC-L4 / LM7). ─────
// The RHS of `&&` must be emitted INSIDE the guarded `if`, never evaluated eagerly —
// a trapping RHS in the dead branch must not run. SIGIL's `if` is lazy by language
// semantics, so proving the frontend emits the guarded shape (RHS after the guard
// opens, and absent from the temp's initializing `let`) is the meaningful proof.
#[test]
fn logical_and_short_circuits_structurally() {
    // `a` is bool; the RHS `100 / d` would trap when `d == 0`, but must be unreachable
    // when `a` is false.
    let src = "pragma solidity ^0.8.0;\ncontract C { \
        function f(bool a, uint256 d) public pure returns (bool) { return a && (100 / d > 5); } }";
    let emitted = translate_ok(src, "c.sol").text;
    let guard = emitted
        .find("if __fe_0 {")
        .expect("`&&` must lower to a guarded `if __fe_0 {`");
    let rhs = emitted
        .find("100 / d")
        .expect("the RHS division must be present");
    assert!(
        rhs > guard,
        "the `&&` RHS must be hoisted INSIDE the guard (short-circuit), not eager:\n{emitted}"
    );
    // The temp's initializing `let` binds only the LHS (`a`), never the RHS.
    let let_line = emitted
        .lines()
        .find(|l| l.contains("let mut __fe_0: bool ="))
        .expect("the &&-temp let");
    assert!(
        !let_line.contains("100"),
        "the &&-temp must be initialized from the LHS only, not the RHS: `{let_line}`"
    );
    // And it round-trips: with `a` false the dead `100 / d` is genuinely never reached.
    compile_named_module(translate_ok(src, "c.sol").source_name, emitted)
        .expect("short-circuit contract must compile");
}

// ── 14. SOL1c (E1): a modifier's guard is INLINED around the body, never dropped. ─────
// The existential failure for a security translator is a modifier that compiles but whose
// guard silently vanishes (an `onlyOwner` no-op). The emitted `setX` must contain BOTH the
// inlined guard and the original body. (The byte-exact golden pins this too; this is the
// explicit security assertion + a direct regression guard for E1.)
#[test]
fn sol1c_modifier_guard_is_inlined_not_dropped() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/only_owner.sol")).unwrap();
    let emitted = translate_ok(&src, "only_owner.sol").text;
    assert!(
        emitted.contains("trap_if(!((__fe_sender == self.owner)))"),
        "the onlyOwner guard must be inlined, not dropped:\n{emitted}"
    );
    assert!(
        emitted.contains("self.x = v;"),
        "the function body must be preserved by inlining:\n{emitted}"
    );
}

// ── 15. SOL1c totality (E3): a deeply-nested modifier wrapping a deep body — each WITHIN
// the parser's per-body depth cap, but whose MERGED (spliced) depth exceeds it — must
// reject FE402 in the inline pass, BEFORE emit's trusted re-parse self-check (which would
// otherwise overflow the native stack ~depth 18). Reaching the assertion IS the proof the
// splice stays total. (The headline hardening find of the harden-spec ritual.)
#[test]
fn sol1c_deep_modifier_times_deep_body_rejects_without_overflow() {
    let mods = format!("{}_;{}", "if (g) {".repeat(5), "}".repeat(5));
    let deep_expr = ["a"; 10].join(" + ");
    let src = format!(
        "pragma solidity ^0.8.0;\ncontract C {{ bool g; uint256 x; \
         modifier deep() {{ {mods} }} \
         function f(uint256 a) public deep {{ x = {deep_expr}; }} }}"
    );
    match sol().translate(&src, "deep.sol") {
        Ok(e) => panic!(
            "deep modifier×body must reject FE402, not translate:\n{}",
            e.text
        ),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE402_TOO_LARGE_SOL,
            "the merged inlined body must re-bound to FE402"
        ),
    }
}

// ── 16. SOL1c: a modifier on a function WITH a return type — the modifier name is consumed
// in the marker loop BEFORE `returns`, the guard inlines, the return type is preserved, and
// it round-trips. (Guards the parse_function marker-loop ↔ `returns` interaction.)
#[test]
fn sol1c_modifier_on_returning_function() {
    let src = "pragma solidity ^0.8.0;\ncontract C { address owner; uint256 x; \
        modifier onlyOwner() { require(msg.sender == owner); _; } \
        function getX() public onlyOwner returns (uint256) { return x; } }";
    let emitted = translate_ok(src, "c.sol");
    assert!(
        emitted
            .text
            .contains("trap_if(!((__fe_sender == self.owner)))"),
        "the guard must inline on a returning function:\n{}",
        emitted.text
    );
    assert!(
        emitted.text.contains("-> u256"),
        "the return type must be preserved:\n{}",
        emitted.text
    );
    compile_named_module(emitted.source_name, emitted.text).expect("must compile");
}

// ── 17. SOL1c: an empty-parens modifier application `onlyOwner()` is a legal parameterless
// form (equivalent to `onlyOwner`) — it must inline like the bare form (only an `(args)`
// list is the unsupported parameterized application → FE448).
#[test]
fn sol1c_empty_parens_modifier_application() {
    let src = "pragma solidity ^0.8.0;\ncontract C { address owner; uint256 x; \
        modifier onlyOwner() { require(msg.sender == owner); _; } \
        function setX(uint256 v) public onlyOwner() { x = v; } }";
    let emitted = translate_ok(src, "c.sol");
    assert!(
        emitted
            .text
            .contains("trap_if(!((__fe_sender == self.owner)))"),
        "`onlyOwner()` must inline like `onlyOwner`:\n{}",
        emitted.text
    );
    compile_named_module(emitted.source_name, emitted.text).expect("must compile");
}

// ── 18. SOL1c totality (review-found): MANY applied modifiers that EACH nest `_` would
// make the right-fold build an AST whose depth = the application count — and the recursive
// post-inline walkers (the FE402 depth re-check itself, the placeholder scan, the tree's
// `Drop`) would overflow the native stack (~1900 deep). The per-function application cap
// rejects FE402 at the 17th application, before any deep tree is built. Reaching the
// assertion IS the proof the pass stays total (bounding modifier COUNT bounds merged DEPTH).
#[test]
fn sol1c_many_nesting_modifiers_reject_without_overflow() {
    let apps = "m ".repeat(2000);
    let src = format!(
        "pragma solidity ^0.8.0;\ncontract C {{ uint256 x; \
         modifier m() {{ if (x > 0) {{ _; }} }} \
         function f() public {apps}{{ x = 1; }} }}"
    );
    match sol().translate(&src, "deep.sol") {
        Ok(_) => panic!("many nesting modifiers must reject FE402, not translate"),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE402_TOO_LARGE_SOL,
            "the application cap must fire before the deep merged tree is built"
        ),
    }
}

// ── 19. SOL-CAP (E-4): the `// sigil:cap-access-control` directive is PURELY ADDITIVE.
// The SAME source without the directive translates to the SOL1c forgeable-trap form (owner
// field kept, no cap types); WITH the directive it becomes the unforgeable `&C_Owner` gate
// (owner field dropped, trap gone). Opt-in default-safety + the headline
// "compiles-but-stronger" proof in one test.
#[test]
fn sol_cap_directive_is_purely_additive() {
    let with_dir =
        std::fs::read_to_string(fixtures_dir().join("compile/cap_only_owner.sol")).unwrap();
    let without_dir: String = with_dir
        .lines()
        .filter(|l| l.trim() != "// sigil:cap-access-control")
        .collect::<Vec<_>>()
        .join("\n");

    // WITHOUT the directive → the SOL1c forgeable-trap form.
    let sol1c = translate_ok(&without_dir, "x.sol").text;
    assert!(
        sol1c.contains("trap_if(!((__fe_sender == self.owner)))"),
        "no directive must emit the SOL1c identity trap:\n{sol1c}"
    );
    assert!(
        !sol1c.contains("cap type"),
        "no directive must emit no cap types"
    );
    assert!(
        sol1c.contains("owner: u256"),
        "no directive keeps the owner field"
    );

    // WITH the directive → the unforgeable cap gate.
    let cap = translate_ok(&with_dir, "x.sol").text;
    assert!(
        cap.contains("__fe_owner: &C_Owner"),
        "the directive must emit the `&C_Owner` gate param:\n{cap}"
    );
    assert!(
        cap.contains("mint C_Owner for"),
        "the directive must mint the root owner cap in new()"
    );
    assert!(
        !cap.contains("__fe_sender == self.owner"),
        "the directive must DROP the forgeable identity trap"
    );
    assert!(
        !cap.contains("owner: u256"),
        "the directive drops the (now-unused) owner field"
    );
}

// ── 20. SOL-CAP: a clean `onlyOwner` contract under cap-mode translates deterministically
// and re-verifies through the trusted compiler (the reject fixtures cover the FE454-457
// fail-closed paths; this pins the positive path + determinism).
#[test]
fn sol_cap_clean_owner_translates_deterministically() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/cap_only_owner.sol")).unwrap();
    let a = translate_ok(&src, "cap_only_owner.sol").text;
    let b = translate_ok(&src, "cap_only_owner.sol").text;
    assert_eq!(a, b, "cap translation must be deterministic");
    compile_named_module(translate_ok(&src, "cap_only_owner.sol").source_name, a)
        .expect("cap-translated contract must compile");
}

// ── 21. SOL-ERC20 (EX-1): the headline security property — `transferFrom` folds into
// the SINGLE atomic cross-map `transfer_from`, NEVER a separate allowance decrement +
// balance move (which SIGIL cannot make atomic; a trap between them would desync funds
// and allowance). The byte-exact golden pins the shape; this is the explicit regression.
#[test]
fn sol_erc20_transferfrom_is_atomic_not_split() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/erc20_full.sol")).unwrap();
    let emitted = translate_ok(&src, "erc20_full.sol").text;
    // The atomic cross-map fold is present.
    assert!(
        emitted.contains("self.allowance.transfer_from(self.balances,"),
        "transferFrom must fold into the atomic cross-map `transfer_from`:\n{emitted}"
    );
    // Isolate transferFrom (the last method) and prove it has NO separate allowance
    // write or balance move — the non-atomic, fund-desyncing shape.
    let tf = emitted
        .split("pub fn transferFrom")
        .nth(1)
        .expect("transferFrom method present");
    assert!(
        !tf.contains("self.allowance.insert("),
        "transferFrom must NOT decrement allowance separately (atomicity):\n{tf}"
    );
    assert!(
        !tf.contains("self.balances.transfer("),
        "transferFrom must NOT move balances separately (atomicity):\n{tf}"
    );
    // approve still uses a direct two-key insert — the atomic fold is SPECIFIC to
    // transferFrom, not a blanket rewrite.
    assert!(
        emitted.contains("self.allowance.insert("),
        "approve must still emit a direct two-key allowance insert"
    );
}

// ── SOL-uintN: two load-bearing width-trap invariants the adversarial review stressed. ──

// `uint256 s = a + b` with a,b `uint128` must trap at the OPERAND width 2^128 BEFORE the
// result widens to uint256 — never 2^256. The trap bound comes from the operands, not the
// assignment target (the headline invariant: widening must not launder the trap away).
#[test]
fn uintn_widening_traps_at_operand_width() {
    let src = "pragma solidity ^0.8.0;\ncontract C { function f(uint128 a, uint128 b) public pure returns (uint256) { uint256 s = a + b; return s; } }";
    let emitted = sol().translate(src, "w.sol").expect("must translate").text;
    assert!(
        emitted.contains("__fe_add_checked(a, b, 340282366920938463463374607431768211456)"),
        "uint128 add must trap at 2^128 even when its result widens to uint256:\n{emitted}"
    );
}

// A `uintN`-sum transfer amount must be width-trapped BEFORE it feeds the trusted u256
// `transfer` primitive (which traps only at 2^256). Guards the transfer-fold interaction.
#[test]
fn uintn_transfer_amount_is_width_trapped() {
    let src = "pragma solidity ^0.8.0;\ncontract C { mapping(address => uint256) bal; function move(address to, uint128 a, uint128 b) public { bal[msg.sender] -= a + b; bal[to] += a + b; } }";
    let emitted = sol().translate(src, "t.sol").expect("must translate").text;
    assert!(
        emitted.contains(".transfer("),
        "the debit/credit must fold into transfer:\n{emitted}"
    );
    assert!(
        emitted.contains("__fe_add_checked(a, b, 340282366920938463463374607431768211456)"),
        "the uint128 transfer amount must be width-trapped at 2^128:\n{emitted}"
    );
}

// ── SOL-CTOR × SOL-uintN: the width-trap pass must walk the CONSTRUCTOR body too. ──
// `lower_uintn_arith` iterates `contract.functions`; the constructor is a separate AST field,
// so without an explicit ctor walk a `uint128` `+`/`*` in a constructor would emit a BARE
// (un-trapped) op — a silent overflow (the EX-1 failure recurring). (SOL-CTOR review finding.)
#[test]
fn ctor_uintn_arith_is_width_trapped() {
    let src = "pragma solidity ^0.8.0;\ncontract C { uint128 x; constructor(uint128 a, uint128 b) { x = a + b; } }";
    let emitted = sol().translate(src, "cw.sol").expect("must translate").text;
    assert!(
        emitted
            .contains("__fe_c.x = __fe_add_checked(a, b, 340282366920938463463374607431768211456)"),
        "a uint128 add in a constructor must be width-trapped at 2^128, not a bare op:\n{emitted}"
    );
}

// ── SOL-ENUM (EX-1, the load-bearing invariant): `EnumName.Member` lowers to the member's
// EXACT 0-based source-order index — a wrong/off-by-one index is a silent wrong value. AND
// the enum decl is ERASED to the `u256` carrier (EX-6): no `record State` is emitted, so a
// nominal type confusion or a stray decl cannot survive. The byte-golden pins the whole file;
// this is the explicit security regression on the index values + erasure.
#[test]
fn sol_enum_members_lower_to_exact_index_and_decl_is_erased() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/enum_status.sol")).unwrap();
    let emitted = translate_ok(&src, "enum_status.sol").text;
    // EX-1: Pending=0 (zero-default), Active=1, Closed=2 — exact source order.
    assert!(
        emitted.contains("status: 0"),
        "enum zero-default = the 0th member (Pending) = tag 0:\n{emitted}"
    );
    assert!(
        emitted.contains("self.status = 1;"),
        "State.Active is the 1st member → index 1:\n{emitted}"
    );
    assert!(
        emitted.contains("self.status = 2;"),
        "State.Closed is the 2nd member → index 2:\n{emitted}"
    );
    // EX-6: the enum decl is erased — the carrier is u256, never a `record State`.
    assert!(
        !emitted.contains("record State"),
        "the enum decl must be erased (no `record State`):\n{emitted}"
    );
    assert!(
        emitted.contains("status: u256"),
        "the enum-typed field lowers to the u256 tag carrier:\n{emitted}"
    );
    // And it round-trips through the trusted compiler.
    compile_named_module(translate_ok(&src, "enum_status.sol").source_name, emitted)
        .expect("enum contract must compile");
}

// ── SOL-ENUM (EX-2, nominal identity): two DISTINCT enums are not interchangeable — comparing
// a value of one with a value of the other is a nominal type confusion and must reject FE445,
// even though both lower to the same `u256` carrier. (The carrier-blind trusted compiler
// cannot catch this; the frontend is the sole gate.)
#[test]
fn sol_enum_cross_enum_comparison_rejects() {
    let src = "pragma solidity ^0.8.0;\ncontract C { enum A { X, Y } enum B { P, Q } A a; B b; \
        function f() public view returns (bool) { return a == b; } }";
    match sol().translate(src, "c.sol") {
        Ok(e) => panic!(
            "a cross-enum `==` must reject (nominal confusion), not translate:\n{}",
            e.text
        ),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE445_TYPE_MISMATCH_SOL,
            "comparing two distinct enums must be FE445"
        ),
    }
}

// ── SOL-DIVERGE: revert() / literal-false require(false)/assert(false) → the divergent trap(). ──

// EX-3 (the headline): a VALUE-returning function whose main path ends in revert() lowers the revert to
// the DIVERGENT trap() (the bottom type `Never`), not the old conditional-Unit trap_if(true) — so the
// return checker sees the path terminate and it compiles (the T044 class the old lowering broke). The
// byte-golden pins the shape; this is the explicit trap()-not-trap_if(true) + no-T044 regression.
#[test]
fn sol_diverge_revert_tail_is_divergent_trap_not_trap_if() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/revert_tail.sol")).unwrap();
    let emitted = translate_ok(&src, "revert_tail.sol").text;
    assert!(
        emitted.contains("trap();"),
        "a tail revert() must lower to the divergent trap():\n{emitted}"
    );
    assert!(
        !emitted.contains("trap_if(true)"),
        "the divergent trap() must replace the old conditional-Unit trap_if(true):\n{emitted}"
    );
    compile_named_module(translate_ok(&src, "revert_tail.sol").source_name, emitted)
        .expect("a value-returning fn ending in revert() must compile (no T044)");
}

// EX-1 (the existential): a NON-constant require/assert condition must STAY the conditional
// trap_if(!(c)) and must NEVER become the unconditional trap() — that would abort the function on
// every call (a broken contract), not just when the guard fails.
#[test]
fn sol_diverge_conditional_require_stays_trap_if() {
    let src = "pragma solidity ^0.8.0;\ncontract C { \
        function f(uint256 x) public pure returns (uint256) { require(x > 0); return x; } }";
    let emitted = translate_ok(src, "c.sol").text;
    assert!(
        emitted.contains("trap_if(!((x > 0)))"),
        "a conditional require must stay trap_if(!(c)):\n{emitted}"
    );
    assert!(
        !emitted.contains("trap();"),
        "a conditional require must NOT become the divergent trap():\n{emitted}"
    );
}

// EX-1 (other direction): a literal-false require/assert IS an unconditional abort → trap(), and as a
// value-returning fn's sole body it compiles (the T044 fix reaches require(false)/assert(false) too).
#[test]
fn sol_diverge_literal_false_require_is_divergent_trap() {
    let src = "pragma solidity ^0.8.0;\ncontract C { \
        function f() public pure returns (uint256) { require(false, \"x\"); } }";
    let emitted = translate_ok(src, "c.sol").text;
    assert!(
        emitted.contains("trap();") && !emitted.contains("trap_if"),
        "require(false) is an unconditional abort → the divergent trap():\n{emitted}"
    );
    compile_named_module(translate_ok(src, "c.sol").source_name, emitted)
        .expect("require(false) as a value-returning fn's body must compile (no T044)");
}

// EX-2 (no truncation): the trusted compiler accepts dead code after a diverging trap(), so a statement
// following revert() — which Solidity itself never executes either — is emitted as-is (not truncated)
// and still round-trips. Faithful: the dead statement never runs because trap() diverges.
#[test]
fn sol_diverge_dead_code_after_revert_still_compiles() {
    let src = "pragma solidity ^0.8.0;\ncontract C { uint256 x; \
        function f(bool go) public { if (!go) { revert(\"stop\"); x = 1; } x = 2; } }";
    let emitted = translate_ok(src, "c.sol").text;
    assert!(
        emitted.contains("trap();"),
        "revert() must lower to trap():\n{emitted}"
    );
    compile_named_module(translate_ok(src, "c.sol").source_name, emitted)
        .expect("dead code after a diverging trap() must still compile (no truncation needed)");
}

// The CEI guard is UNCHANGED by the divergence migration: a storage write followed by revert() is still
// FE412 (SIGIL's trap cannot roll back the write like Solidity's atomic revert). Making revert() diverge
// must not weaken this — the gate treats revert() as trap-capable regardless of how it lowers.
#[test]
fn sol_diverge_write_then_revert_is_still_cei_rejected() {
    let src = "pragma solidity ^0.8.0;\ncontract C { uint256 x; \
        function bad(uint256 v) public { x = v; revert(); } }";
    match sol().translate(src, "c.sol") {
        Ok(e) => panic!(
            "a storage write then revert() must reject FE412:\n{}",
            e.text
        ),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE412_NON_CEI,
            "write-then-revert must stay FE412 after the divergence migration"
        ),
    }
}

// ── SOL-CALLS: internal-call inlining (the OZ spine + the adversarial-review security invariants). ──

// The headline: a public `transfer` calling `_transfer(_msgSender(), to, amount)` inlines _msgSender()
// (→ the __fe_sender param) and splices _transfer's body, whose debit/credit then FOLDS into the ATOMIC
// `.transfer(...)` — the inlined body composes with the existing recognizer (EX-6). The byte-golden pins
// the shape; this is the explicit atomicity regression (a non-atomic debit/credit would desync funds).
#[test]
fn sol_calls_oz_spine_folds_to_atomic_transfer() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/erc20_calls.sol")).unwrap();
    let emitted = translate_ok(&src, "erc20_calls.sol").text;
    let tx = emitted
        .split("pub fn transfer")
        .nth(1)
        .expect("transfer method present");
    assert!(
        tx.contains("self.balances.transfer("),
        "the inlined _transfer debit/credit must fold into the atomic .transfer():\n{emitted}"
    );
    assert!(
        !tx.contains("self.balances.insert("),
        "transfer must NOT emit a separate map write (atomicity):\n{tx}"
    );
    compile_named_module(translate_ok(&src, "erc20_calls.sol").source_name, emitted)
        .expect("the inlined OZ spine must round-trip");
}

// FE488 (the CRITICAL capture): a callee's state-field reference captured by a same-named caller param
// is REJECTED — and the control (rename the caller param) proves the fix is precise: the guard then
// correctly reads `self.owner`, not the caller's argument. A silent accept here is an auth bypass.
#[test]
fn sol_calls_state_capture_rejects_and_control_reads_state() {
    let bad = "pragma solidity ^0.8.0;\ncontract C { address owner; uint256 secret; \
        function ownerAddr() internal view returns (address) { return owner; } \
        function admin(address owner) public { require(msg.sender == ownerAddr()); secret = 1; } }";
    match sol().translate(bad, "c.sol") {
        Ok(e) => panic!(
            "a state-field capture must reject FE488, not translate:\n{}",
            e.text
        ),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE488_STATE_CAPTURE_SOL
        ),
    }
    // Control: the caller param renamed → no shadow → the guard reads the STATE field.
    let good = bad.replace("address owner) public", "address ownerArg) public");
    let emitted = translate_ok(&good, "c.sol").text;
    assert!(
        emitted.contains("trap_if(!((__fe_sender == self.owner)))"),
        "with no shadow, the inlined guard must read the state field self.owner:\n{emitted}"
    );
}

// The FE488 capture class in the MODIFIER-inline pass (the same bug, audited in inline_modifiers after
// the SOL-CALLS review): a host PARAM shadowing the state field an applied `onlyOwner` reads would make
// the inlined guard check the host's argument, not self.owner (an auth bypass). Reject FE488; the
// renamed-param control proves the guard then correctly reads the state field.
#[test]
fn sol1c_modifier_state_capture_rejects_and_control_reads_state() {
    let bad = "pragma solidity ^0.8.0;\ncontract C { address owner; uint256 val; \
        modifier onlyOwner() { require(msg.sender == owner); _; } \
        function set(uint256 v, address owner) public onlyOwner { val = v; } }";
    match sol().translate(bad, "c.sol") {
        Ok(e) => panic!(
            "a modifier state-field capture must reject FE488, not translate:\n{}",
            e.text
        ),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE488_STATE_CAPTURE_SOL
        ),
    }
    // Control: rename the shadowing param → the inlined onlyOwner guard reads the STATE field.
    let good = bad.replace("address owner) public", "address ownerArg) public");
    let emitted = translate_ok(&good, "c.sol").text;
    assert!(
        emitted.contains("trap_if(!((__fe_sender == self.owner)))"),
        "with no shadow, the inlined modifier guard must read self.owner:\n{emitted}"
    );
    // Precision: a host param shadowing an UNRELATED state field the modifier does NOT read is allowed.
    let ok = "pragma solidity ^0.8.0;\ncontract C { address owner; uint256 val; \
        modifier onlyOwner() { require(msg.sender == owner); _; } \
        function set(uint256 val) public onlyOwner { } }";
    translate_ok(ok, "c.sol");
}

// ── SOL-UNCHECKED: `unchecked{}` → checked arithmetic + the OZ local-indirection transfer fold. ──

// The headline: the VERBATIM OpenZeppelin 4.x `_transfer` (a `fromBalance` local read + an `unchecked`
// debit `balances[from] = fromBalance - amount`) translates. Part A splices the `unchecked` wrapper out
// (SIGIL arith is always checked — trap-instead-of-wrap, fail-closed); Part B recognizes the
// local-indirection debit (fromBalance aliases balances[from]) and folds debit+credit into the ATOMIC
// `.transfer(...)`. A non-atomic (unfolded) debit/credit would FE412 or desync funds — so the byte
// golden + this atomicity assertion + the round-trip are the regression.
#[test]
fn sol_unchecked_oz_transfer_folds_to_atomic() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/erc20_unchecked_transfer.sol"))
        .unwrap();
    let emitted = translate_ok(&src, "erc20_unchecked_transfer.sol").text;
    // The inlined transfer folds to the atomic call inside the public `transfer`. (The standalone
    // internal `_transfer` is now dropped by PR5/L4's dead-internal sweep — inlined then call-site-
    // free — so exactly ONE `.transfer(` survives; the atomicity property is unchanged.)
    assert_eq!(
        emitted.matches("self.balances.transfer(").count(),
        1,
        "the inlined transfer must fold to the atomic .transfer() (the internal _transfer is swept):\n{emitted}"
    );
    assert!(
        !emitted.contains("self.balances.insert("),
        "the unchecked OZ debit must fold — never a separate map write (atomicity):\n{emitted}"
    );
    compile_named_module(
        translate_ok(&src, "erc20_unchecked_transfer.sol").source_name,
        emitted,
    )
    .expect("the verbatim OZ 4.x _transfer must round-trip through the trusted compiler");
}

// SOL-XFILE PR6/AC-2: the OZ 5.x transferFrom spine folds to the atomic `erc20_transfer_from` with the
// EXACT operand order (bal, from, spender=__fe_sender, to, amount) — the M-B "operand-mapping is the
// recognizer's only soundness duty" lesson — and the `_transfer` zero-guards survive as pure trap-checks
// BEFORE the single atomic op. Aliasing/infinite-allowance correctness lives in the exec-proven primitive.
#[test]
fn sol_oz5_transferfrom_folds_to_erc20_transfer_from() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/erc20_transferfrom_token.sol"))
        .unwrap();
    let emitted = translate_ok(&src, "erc20_transferfrom_token.sol").text;
    assert!(
        emitted.contains(
            "self._allowances.erc20_transfer_from(self._balances, from, __fe_sender, to, value)"
        ),
        "transferFrom must fold to the atomic erc20_transfer_from with operands (bal, from, spender, to, amount):\n{emitted}"
    );
    // The _transfer from/to zero-guards survive as pure trap-checks before the single atomic op (never
    // dropped). Slice the transferFrom method (the `__fe_inl` index is monotonic across functions, so
    // it is prefix-agnostic): the only surviving guards there are the two `if (… == 0) { trap(); }` —
    // the _spendAllowance/_approve guards were consumed into the trusted primitive.
    let tf = emitted.split("pub fn transferFrom").nth(1).unwrap_or("");
    let tf_body = tf.split("\n    pub fn ").next().unwrap_or(tf);
    assert!(
        tf_body.matches("== 0) {").count() >= 2 && tf_body.contains("trap();"),
        "the _transfer from/to zero-guards must survive before the fold:\n{tf_body}"
    );
    // Exactly ONE atomic op (the two committed map writes — allowance + balance — are folded).
    assert_eq!(
        emitted.matches("erc20_transfer_from(").count(),
        1,
        "exactly one folded transferFrom:\n{emitted}"
    );
    compile_named_module(
        translate_ok(&src, "erc20_transferfrom_token.sol").source_name,
        emitted,
    )
    .expect("the OZ 5.x transferFrom token must round-trip through the trusted compiler");
}

// EX-B1 (the Part-B soundness crux): the local-indirection fold fires ONLY when `fromBalance` provably
// still equals `balances[from]` at the debit. Reassigning the local between the bind and the debit
// invalidates the alias, so the debit does NOT fold — it stays a lone map write and the pair hits the CEI
// gate (FE412). If the alias were NOT invalidated, the fold would WRONGLY fire and accept a translation
// that debits the current slot while the source recomputed from a stale local — a silent value bug.
#[test]
fn sol_unchecked_stale_alias_between_bind_and_debit_blocks_fold() {
    let bad = "pragma solidity ^0.8.0;\ncontract Token { mapping(address => uint256) balances; \
        function bad(address from, address to, uint256 amount) public { \
        uint256 fromBalance = balances[from]; require(fromBalance >= amount); \
        fromBalance = amount; \
        balances[from] = fromBalance - amount; balances[to] += amount; } }";
    match sol().translate(bad, "c.sol") {
        Ok(e) => panic!(
            "a stale alias (local reassigned before the debit) must NOT fold — expected FE412:\n{}",
            e.text
        ),
        Err(diags) => assert_eq!(
            diags.first().unwrap().code,
            sigil_frontends::codes::FE412_NON_CEI
        ),
    }
    // Control: with the reassignment removed (only the `require` between bind and debit) the alias is
    // live and the OZ local-indirection debit folds to the atomic transfer → accepts.
    let good = bad.replace("fromBalance = amount; ", "");
    let emitted = translate_ok(&good, "c.sol").text;
    assert!(
        emitted.contains("self.balances.transfer("),
        "with a live alias the OZ local-indirection debit must fold to the atomic transfer:\n{emitted}"
    );
}

// AC-2 (the declared divergence): a lone `unchecked` arithmetic assignment is lowered as CHECKED — where
// Solidity WRAPS on overflow, SIGIL TRAPS. We do NOT silently wrap; the emitted subtraction is the
// checked SIGIL `-` (traps on underflow), identical to non-unchecked arithmetic.
#[test]
fn sol_unchecked_lone_arith_is_checked_not_wrapped() {
    let src = "pragma solidity ^0.8.0;\ncontract C { uint256 total; \
        function wrap(uint256 a, uint256 b) public { unchecked { total = a - b; } } }";
    let emitted = translate_ok(src, "c.sol").text;
    assert!(
        emitted.contains("self.total = (a - b);"),
        "unchecked arithmetic must lower as CHECKED (trap-on-overflow), not wrap:\n{emitted}"
    );
    compile_named_module(translate_ok(src, "c.sol").source_name, emitted)
        .expect("a checked unchecked-lowering must round-trip");
}

// SOL-UNCHECKED × SOL-CAP (adversarial-review regression). `unwrap_unchecked` runs BEFORE
// `recognize_cap_guards`, so an `unchecked` wrapper is TRANSPARENT to cap recognition: an
// `unchecked`-wrapped `onlyOwner` gate emits byte-identical SIGIL to the unwrapped gate (the
// unforgeable `&C_Owner` borrow), NOT a silently-downgraded forgeable `__fe_sender` trap. Before the
// ordering fix, the wrapper hid the gate require from the recognizer → a near-miss downgrade (H3).
#[test]
fn sol_unchecked_cap_gate_is_transparent_to_wrapper() {
    let wrapped = "// sigil:cap-access-control\npragma solidity ^0.8.0;\ncontract C { \
        mapping(address => uint256) balances; address owner; \
        modifier onlyOwner() { unchecked { require(msg.sender == owner); } _; } \
        function credit(address a, uint256 amt) public onlyOwner { balances[a] = balances[a] + amt; } }";
    let plain = wrapped.replace(
        "unchecked { require(msg.sender == owner); }",
        "require(msg.sender == owner);",
    );
    let w = translate_ok(wrapped, "c.sol").text;
    let p = translate_ok(&plain, "c.sol").text;
    assert_eq!(
        w, p,
        "an unchecked-wrapped gate must emit byte-identical cap SIGIL to the unwrapped gate:\n--- wrapped ---\n{w}\n--- plain ---\n{p}"
    );
    assert!(
        w.contains("&C_Owner"),
        "the gate must be recognized as the unforgeable cap, not downgraded to a forgeable trap:\n{w}"
    );
}

// SOL-UNCHECKED (FE490 alpha-rename): a top-level local in an `unchecked` block is alpha-renamed to
// `__fe_unchk<N>_` on flatten, so erasing the block boundary can NEITHER leak the binding into the
// enclosing scope NOR capture a same-named reference. Here the local `x` shadows the state field
// `x`; the `x = 5` AFTER the block MUST resolve to the STATE field (`self.x`), proving the flattened
// local did not capture it. The former FE490 reject over-approximated this case.
#[test]
fn sol_unchecked_top_level_local_is_renamed_no_leak() {
    let src = "pragma solidity ^0.8.0;\ncontract C { uint256 x; \
        function f(uint256 a) public { unchecked { uint256 x = a; x = x + 1; } x = 5; } }";
    let emitted = translate_ok(src, "c.sol").text;
    assert!(
        emitted.contains("let mut __fe_unchk0_x") && emitted.contains("self.x = 5;"),
        "the unchecked local must be renamed __fe_unchk*, and `x = 5` after the block must write \
         self.x (no capture):\n{emitted}"
    );
    // Identifier validation now recurses into `unchecked` bodies (it runs BEFORE the rename), so a
    // user local that spoofs the reserved `__fe_` prefix inside `unchecked` is still rejected FE420 —
    // the rename can never launder a reserved-prefix user identifier.
    let evil = "pragma solidity ^0.8.0;\ncontract C { uint256 t; \
        function f(uint256 a) public { unchecked { uint256 __fe_evil = a; t = __fe_evil; } } }";
    assert_eq!(
        translate_err(evil).first().unwrap().code,
        sigil_frontends::codes::FE420_BAD_IDENTIFIER_SOL
    );
}

// ── SOL-SAFEMATH: `using SafeMath` + fold `.add/.sub/.mul/.div/.mod` to checked ops. ──

// The headline: a verbatim pre-4.4 OZ SafeMath `_transfer` (the `.sub(amt,"msg")`/`.add(amt)` method
// form) folds — at PARSE — to checked `-`/`+`, the revert-message string is DROPPED, and the resulting
// debit/credit composes with `recognize_transfers` into the ATOMIC `self.balances.transfer(...)`. A
// non-atomic (unfolded) pair would FE412 or desync funds — so the fold + atomicity + round-trip are the
// regression.
#[test]
fn sol_safemath_transfer_folds_to_atomic() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/erc20_safemath_transfer.sol"))
        .unwrap();
    let emitted = translate_ok(&src, "erc20_safemath_transfer.sol").text;
    assert!(
        emitted.contains("self.balances.transfer("),
        "the SafeMath debit/credit must fold to the atomic .transfer():\n{emitted}"
    );
    assert!(
        !emitted.contains(".add(") && !emitted.contains(".sub(") && !emitted.contains("ERC20:"),
        "no SafeMath method call or revert-message string may survive the fold:\n{emitted}"
    );
    compile_named_module(
        translate_ok(&src, "erc20_safemath_transfer.sol").source_name,
        emitted,
    )
    .expect("the pre-4.4 OZ SafeMath _transfer must round-trip through the trusted compiler");
}

// EX-3/EX-4 (the two security-critical invariants of a SYNTACTIC parse-time fold): (a) the fold runs
// BEFORE the SOL-CAP scans, so a SafeMath-wrapped `msg.sender` is NOT hidden from the FE454 data-use
// gate; (b) the fold does no typing, so a wrong-receiver `address.add(x)` is caught by the checker
// (FE443), never silently mis-lowered. A control confirms the clean cap contract still folds + accepts.
#[test]
fn sol_safemath_fold_is_cap_visible_and_type_rechecked() {
    // EX-3: a SafeMath-wrapped msg.sender in a cap-mode guarded body still hits FE454 (not hidden).
    let cap_hide = "// sigil:cap-access-control\npragma solidity ^0.8.0;\ncontract C { \
        using SafeMath for uint256; mapping(address => uint256) balances; address owner; \
        modifier onlyOwner() { require(msg.sender == owner); _; } \
        function credit(uint256 x) public onlyOwner { balances[msg.sender] = balances[msg.sender].add(x); } }";
    assert_eq!(
        translate_err(cap_hide).first().unwrap().code,
        sigil_frontends::codes::FE454_ADDRESS_USED_AS_DATA_SOL
    );
    // EX-4: a wrong-receiver SafeMath fold (`address.add`) is rejected by check's arith rules (FE443).
    let wrong_recv = "pragma solidity ^0.8.0;\ncontract C { using SafeMath for uint256; address a; \
        uint256 v; function f(uint256 x) public { v = a.add(x); } }";
    assert_eq!(
        translate_err(wrong_recv).first().unwrap().code,
        sigil_frontends::codes::FE443_ADDRESS_OP_SOL
    );
    // Control: the SAME contract with a uint256 receiver folds to checked `+` and accepts.
    let ok = wrong_recv.replace("address a;", "uint256 a;");
    assert!(translate_ok(&ok, "c.sol").text.contains("(self.a + x)"));
}

// SOL-MULTIWRITE: the OZ `_burn` shape (a straight-line balance debit + totalSupply decrement) was a
// hard FE412 wall (no rollback). `total_cei` hoists the totalSupply arithmetic into a pre-write local
// and reorders the single map write FIRST, so no trap can fire after a commit — the emitted body
// puts the `.insert(` before the trap-free `self.totalSupply =` store, and it round-trips.
#[test]
fn sol_multiwrite_burn_hoists_arith_and_reorders_map_first() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/erc20_burn.sol")).unwrap();
    let emitted = translate_ok(&src, "erc20_burn.sol").text;
    // The totalSupply arithmetic is hoisted to a pre-write `__fe_w0` local (before any storage write).
    assert!(
        emitted.contains("let mut __fe_w0: u256 = (self.totalSupply - amount);"),
        "the trap-capable totalSupply arithmetic must be hoisted to a pre-write local:\n{emitted}"
    );
    let insert_at = emitted
        .find("self.balances.insert(")
        .expect("the balance debit must be a map insert");
    let store_at = emitted
        .find("self.totalSupply = __fe_w0;")
        .expect("the totalSupply store must read the hoisted local (trap-free)");
    // The single map write must precede the trap-free scalar store (map-first ordering).
    assert!(
        insert_at < store_at,
        "the map write must be reordered before the scalar store:\n{emitted}"
    );
    compile_named_module(translate_ok(&src, "erc20_burn.sol").source_name, emitted)
        .expect("the hoisted OZ _burn must round-trip through the trusted compiler");
}

// EX-5 / the no-op invariant: `total_cei` fires ONLY on a body that currently VIOLATES CEI. A
// multi-write body that ALREADY passes (the single map write first, then a trap-free scalar store)
// must be left byte-identical — no `__fe_w` hoist, order preserved — so no accepted body changes. (The
// full 56-golden byte-identity is enforced by `golden_translation`; this pins the reasoning directly.)
#[test]
fn sol_multiwrite_is_noop_on_already_cei_body() {
    let src = "pragma solidity ^0.8.0;\ncontract C { \
        mapping(address => uint256) balances; uint256 totalSupply; \
        function set(address k, uint256 x, uint256 t) public { balances[k] = x; totalSupply = t; } }";
    let emitted = translate_ok(src, "c.sol").text;
    assert!(
        !emitted.contains("__fe_w"),
        "an already-CEI multi-write body must NOT be rewritten by total_cei:\n{emitted}"
    );
    let insert_at = emitted
        .find("self.balances.insert(")
        .expect("map write present");
    let store_at = emitted
        .find("self.totalSupply = t;")
        .expect("scalar store present");
    assert!(
        insert_at < store_at,
        "source order must be preserved (no reorder):\n{emitted}"
    );
    compile_named_module(translate_ok(src, "c.sol").source_name, emitted)
        .expect("the already-CEI body must round-trip");
}

// SOL-MULTIWRITE adversarial-review CRITICAL regression: a TRAP-FREE scalar store that reads the map
// and sits BEFORE the map write in source must observe the PRE-write map value. total_cei hoists EVERY
// scalar store's RHS into the pre-write prefix, so the read lands BEFORE the reordered-to-front map
// write. Before the fix the trap-free store was moved AS-IS to after the map write and read the
// POST-write value — a silent mistranslation (snapshot = 105 instead of 100 for a +5 credit).
#[test]
fn sol_multiwrite_snapshot_reads_pre_write_value() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/multiwrite_snapshot.sol")).unwrap();
    let emitted = translate_ok(&src, "multiwrite_snapshot.sol").text;
    // The snapshot read is hoisted into `__fe_w0` BEFORE the map write; the store-back reads the local.
    let hoist_at = emitted
        .find("let mut __fe_w0: u256 = self.balances.get_or(account, 0);")
        .expect("the snapshot read must be hoisted to a pre-write local");
    let insert_at = emitted
        .find("self.balances.insert(")
        .expect("the credit must be a map insert");
    let store_at = emitted
        .find("self.snapshot = __fe_w0;")
        .expect("the snapshot store must read the pre-write hoisted local, not the map");
    assert!(
        hoist_at < insert_at && insert_at < store_at,
        "the snapshot read must be hoisted BEFORE the map write (else it reads the post-write value):\n{emitted}"
    );
    compile_named_module(
        translate_ok(&src, "multiwrite_snapshot.sol").source_name,
        emitted,
    )
    .expect("the snapshot regression fixture must round-trip");
}

// SOL-MULTIMAP M-A: a ≥2-DISTINCT-map body (lock/unlock) folds into an atomic reserve-all-then-write
// batch — every value hoisted (read pre-write), then ALL `reserve1`s (read-only), then ALL `insert`s
// (trap-free). The reserves MUST precede the writes (else a later insert could trap after a commit).
#[test]
fn sol_multimap_reserves_precede_writes() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/multimap_lock.sol")).unwrap();
    let emitted = translate_ok(&src, "multimap_lock.sol").text;
    let hoist_a = emitted
        .find("let mut __fe_rb0: u256 = (self.balances.get_or(u, 0) - a);")
        .expect("the balances value must be hoisted pre-write");
    let reserve_a = emitted
        .find("self.balances.reserve1(u);")
        .expect("balances must be reserved");
    let reserve_b = emitted
        .find("self.locked.reserve1(u);")
        .expect("locked must be reserved");
    let insert_a = emitted
        .find("self.balances.insert(u, __fe_rb0);")
        .expect("balances trap-free insert");
    // Both hoists precede both reserves, both reserves precede every insert (reserve-all-then-write).
    assert!(
        hoist_a < reserve_a && reserve_a.max(reserve_b) < insert_a,
        "reserves must precede writes (reserve-all-then-write):\n{emitted}"
    );
    compile_named_module(translate_ok(&src, "multimap_lock.sol").source_name, emitted)
        .expect("the distinct-maps reserved batch must round-trip");
}

// SOL-MULTIMAP M-A: the transfer_from multi-map orchestration — a folded `.transfer()` plus a deferred
// write to a DISTINCT map. The deferred map is RESERVED (read-only) BEFORE the atomic transfer (so if
// the transfer traps, nothing on the deferred map committed), and its trap-free insert comes AFTER.
#[test]
fn sol_multimap_transfer_reserves_deferred_before_transfer() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/transfer_plus_reward.sol")).unwrap();
    let emitted = translate_ok(&src, "transfer_plus_reward.sol").text;
    let reserve = emitted
        .find("self.rewardDebt.reserve1(to);")
        .expect("the deferred rewardDebt map must be reserved");
    let transfer = emitted
        .find("self.balances.transfer(from, to, amt);")
        .expect("the balances transfer must be the atomic op");
    let insert = emitted
        .find("self.rewardDebt.insert(to, __fe_rb0);")
        .expect("the deferred insert must be trap-free (reads the hoisted local)");
    assert!(
        reserve < transfer && transfer < insert,
        "reserve deferred map → transfer → deferred insert (the transfer_from orchestration):\n{emitted}"
    );
    compile_named_module(
        translate_ok(&src, "transfer_plus_reward.sol").source_name,
        emitted,
    )
    .expect("the transfer + reward reserved batch must round-trip");
}

// SOL-MULTIMAP M-B: the fee-on-transfer split (a debit + 2 credits on ONE map) folds into a SINGLE atomic
// `transfer_split(from, amount, to, net, feeTo, fee)` — the aliasing across {from,to,feeTo} handled inside
// verified stdlib. No `insert`/loose write survives (the 3 same-map writes are ONE op), and it round-trips.
#[test]
fn sol_multimap_fee_on_transfer_folds_to_transfer_split() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/fee_on_transfer.sol")).unwrap();
    let emitted = translate_ok(&src, "fee_on_transfer.sol").text;
    assert!(
        emitted.contains("self.balances.transfer_split(__fe_sender, amount, to, net, feeTo, fee);"),
        "the debit + 2 credits must fold to the atomic transfer_split with the source operands:\n{emitted}"
    );
    // The 3 same-map writes are ONE op — no residual `.insert(`/`.transfer(` loose write.
    assert!(
        !emitted.contains(".insert(") && !emitted.contains(".transfer("),
        "no loose same-map write may survive the split fold:\n{emitted}"
    );
    compile_named_module(
        translate_ok(&src, "fee_on_transfer.sol").source_name,
        emitted,
    )
    .expect("the fee-on-transfer split must round-trip through the trusted compiler");
}

// SOL-UPDATE: the OZ 5.x unified `_update` — the 2-`if` zero-address-dispatch pair folds to the
// atomic trusted `erc20_update(totalSupply, from, to, value)` followed by the TRAP-FREE totalSupply
// store-back (`self._totalSupply = __fe_ts;` — a bare-Var `=` store, CEI-safe after the committed
// map op). No loose map write survives inside the folded methods, and it round-trips.
#[test]
fn sol_update_folds_to_erc20_update() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/erc20_update_token.sol")).unwrap();
    let emitted = translate_ok(&src, "erc20_update_token.sol").text;
    assert!(
        emitted.contains(".erc20_update(self._totalSupply,"),
        "the `_update` if-pair must fold to the atomic erc20_update on the totalSupply field:\n{emitted}"
    );
    assert!(
        emitted.contains("self._totalSupply = __fe_ts;"),
        "the returned new totalSupply must be stored back trap-free:\n{emitted}"
    );
    assert!(
        !emitted.contains(".insert("),
        "no loose map write may survive the `_update` fold:\n{emitted}"
    );
    compile_named_module(
        translate_ok(&src, "erc20_update_token.sol").source_name,
        emitted,
    )
    .expect("the OZ 5.x `_update` token must round-trip through the trusted compiler");
}

// SOL-UPDATE EX-5 / MC-6: `normalize_address_zero` REWRITES `address(0)` → `0`; it never deletes a
// statement. The leading zero-address guards must SURVIVE as `if (x == 0) { trap(); }` — a transfer
// to the zero address still REVERTS (dropping the guard would silently turn it into a burn via the
// `to == 0` dispatch inside `erc20_update`).
#[test]
fn sol_update_zero_guards_survive_normalization() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/erc20_update_token.sol")).unwrap();
    let emitted = translate_ok(&src, "erc20_update_token.sol").text;
    let transfer_fn = emitted
        .split("pub fn transfer(")
        .nth(1)
        .expect("transfer fn present")
        .split("pub fn")
        .next()
        .unwrap();
    assert!(
        transfer_fn.contains("== 0) {") && transfer_fn.contains("trap();"),
        "the zero-address guards must survive normalization as `if (x == 0) {{ trap(); }}`:\n{emitted}"
    );
}

// SOL-SYNTAX: custom `error` declarations (file-level + contract-member) are DISCARDED — the emitted
// SIGIL carries no trace of the error names, and `revert CustomError(...)` lowers to `trap()`.
#[test]
fn sol_syntax_custom_errors_discarded() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/custom_error_token.sol")).unwrap();
    let emitted = translate_ok(&src, "custom_error_token.sol").text;
    assert!(
        emitted.contains("trap();"),
        "a `revert CustomError(...)` must lower to `trap()`:\n{emitted}"
    );
    assert!(
        !emitted.contains("Unauthorized") && !emitted.contains("TooSmall"),
        "the emitted SIGIL must carry no trace of the discarded error names:\n{emitted}"
    );
}

// SOL-SYNTAX EX-3: a NAMED mapping (Solidity ≥0.8.18) emits byte-IDENTICAL SIGIL to its UNNAMED twin
// — the param names are pure documentation with zero semantic effect (no AST field).
#[test]
fn sol_syntax_named_mapping_equals_unnamed() {
    let named = "pragma solidity ^0.8.18;\ncontract M {\n  mapping(address owner => uint256 bal) m;\n  function g(address a) public { uint256 x = m[a]; m[a] = x; }\n}\n";
    let unnamed = "pragma solidity ^0.8.18;\ncontract M {\n  mapping(address => uint256) m;\n  function g(address a) public { uint256 x = m[a]; m[a] = x; }\n}\n";
    let a = translate_ok(named, "m.sol").text;
    let b = translate_ok(unnamed, "m.sol").text;
    assert_eq!(
        a, b,
        "a named mapping must emit byte-identical SIGIL to the unnamed form"
    );
}

// SOL-ACCESS PR1: `bytes32` is the u256 carrier (full 256-bit opaque id — the `address`
// precedent) and `constant`/`immutable` are consumed as pure surface modifiers whose
// compile-time-literal initializer SURVIVES to the record seed (never zero-defaulted —
// a role constant that silently became 0 would gate on DEFAULT_ADMIN_ROLE, MI-6/MC-3
// territory). The type name itself must be fully erased from the emitted SIGIL.
#[test]
fn sol_access_bytes32_carrier_and_constant_literal_survive() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/bytes32_roles.sol")).unwrap();
    let emitted = translate_ok(&src, "bytes32_roles.sol").text;
    // Skip the `module bytes32_roles;` header (the fixture NAME carries the substring);
    // every TYPE position below it must be erased to the u256 carrier.
    let body = emitted.split_once('\n').expect("module header line").1;
    assert!(
        !body.contains("bytes32"),
        "the `bytes32` type name must be fully erased to the u256 carrier:\n{emitted}"
    );
    assert!(
        emitted.contains(
            "MINTER_ROLE: 0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6"
        ),
        "the constant's 32-byte hex literal must seed the record field (not zero-default):\n{emitted}"
    );
    assert!(
        emitted.contains("roleMemberCount: BoundedMap_u256_u256_64"),
        "a `mapping(bytes32 => uint256)` must lower to the u256 bounded map:\n{emitted}"
    );
}

// SOL-ACCESS PR1: the `constant` modifier is PURE SURFACE — a `bytes32 constant X = lit`
// emits byte-identical SIGIL to the same declaration without the modifier. Ditto
// `immutable` with a declaration-site literal initializer. (AC-2: an `immutable` set
// from a CONSTRUCTOR ARGUMENT is a separate deploy-time-init wall, not covered here.)
#[test]
fn sol_access_constant_modifier_is_pure_surface() {
    let with_mod = "pragma solidity ^0.8.0;\ncontract K {\n  bytes32 public constant R = 0x01;\n  uint256 public immutable LIMIT = 7;\n  function f() public view returns (uint256) { return LIMIT; }\n}\n";
    let without = "pragma solidity ^0.8.0;\ncontract K {\n  bytes32 public R = 0x01;\n  uint256 public LIMIT = 7;\n  function f() public view returns (uint256) { return LIMIT; }\n}\n";
    let a = translate_ok(with_mod, "k.sol").text;
    let b = translate_ok(without, "k.sol").text;
    assert_eq!(
        a, b,
        "`constant`/`immutable` must be consumed as pure surface (byte-identical emit)"
    );
    assert!(
        a.contains("LIMIT: 7"),
        "the modifier must not eat the initializer — the literal seeds the field:\n{a}"
    );
}

// SOL-ACCESS PR2 / EX-1: the folded role constants must equal the INDEPENDENTLY
// PUBLISHED on-chain values — never a from-memory or single-implementation number.
// References (fetched 2026-07-12, two independent channels):
//   keccak256("MINTER_ROLE") = 0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6
//     — a live `emit RoleGranted(role: 0x9f2df0…)` execution trace in
//       code-423n4/2024-02-ai-arena-findings#1507 (a deployed-contract observation).
//   keccak256("") = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
//     — the canonical empty-input hash (an EOA's extcodehash; ethers.js docs).
// A mismatch here means the fold is hashing the wrong bytes or with the wrong
// function (SHA3-256 ≠ Keccak-256) — the MC-3 silent-wrong-role catastrophe.
#[test]
fn sol_access_keccak_fold_matches_published_vectors() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/keccak_role.sol")).unwrap();
    let emitted = translate_ok(&src, "keccak_role.sol").text;
    assert!(
        emitted.contains(
            "MINTER_ROLE: 0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6"
        ),
        "keccak256(\"MINTER_ROLE\") must fold to the published on-chain value:\n{emitted}"
    );
    // The expression-position fold: `members[keccak256("MINTER_ROLE")][account]` reads
    // through the SAME constant (roles agree between the decl and the gate).
    assert!(
        emitted
            .contains("get_or(0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6,"),
        "the expression-position fold must produce the same role id:\n{emitted}"
    );
    let empty =
        "pragma solidity ^0.8.0;\ncontract E { bytes32 public constant Z = keccak256(\"\"); }\n";
    let e = translate_ok(empty, "e.sol").text;
    assert!(
        e.contains("Z: 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
        "keccak256(\"\") must fold to the canonical empty-input hash:\n{e}"
    );
}

// SOL-ACCESS PR2 / EX-1: two-crate cross-check — every emitted constant must agree with
// an INDEPENDENT second Keccak-256 implementation (`tiny_keccak`) over role-shaped and
// arbitrary inputs. Guards against a wrong-variant regression (sha3::Sha3_256 vs
// sha3::Keccak256) that a fixed-vector test alone might miss on exotic inputs.
#[test]
fn sol_access_keccak_two_crate_cross_check() {
    use tiny_keccak::{Hasher, Keccak};
    for s in [
        "MINTER_ROLE",
        "BURNER_ROLE",
        "PAUSER_ROLE",
        "DEFAULT_ADMIN_ROLE",
        "",
        "a",
        "The quick brown fox jumps over the lazy dog",
        "0123456789_ABCDEFGHIJKLMNOPQRSTUVWXYZ!#$%&'()*+,-./:;<=>?@[]^_`{|}~ ",
    ] {
        let src = format!(
            "pragma solidity ^0.8.0;\ncontract K {{ bytes32 public constant X = keccak256(\"{s}\"); }}\n"
        );
        let emitted = translate_ok(&src, "k.sol").text;
        // Anchor on `X: 0x` — the record TYPE line also contains `X: ` (as `X: u256`),
        // so a bare `X: ` split lands on the type, not the seeded constant.
        let got = emitted
            .split("X: 0x")
            .nth(1)
            .and_then(|t| t.get(..64))
            .unwrap_or_else(|| panic!("no folded constant in:\n{emitted}"));
        let mut k = Keccak::v256();
        k.update(s.as_bytes());
        let mut out = [0u8; 32];
        k.finalize(&mut out);
        let want: String = out.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(got, want, "fold vs tiny_keccak disagree for {s:?}");
    }
}

// SOL-ACCESS PR3 / EX-4: bool-valued maps store the CANONICAL u256 0/1 — a literal
// `= true` write lowers to `insert(k, 1)`, `= false` to `insert(k, 0)`, and every read
// wraps as `(get_or(…, 0) == 1)` (a SIGIL bool; the 0 default ≡ Solidity's mapping
// default `false`). No lax truthiness can exist in storage: the ONLY writers are the
// rewritten literals (MC-6).
#[test]
fn sol_access_bool_map_canonical_zero_one() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/bool_map_blocklist.sol")).unwrap();
    let emitted = translate_ok(&src, "bool_map_blocklist.sol").text;
    assert!(
        emitted.contains("self.blocked.insert(account, 1);")
            && emitted.contains("self.blocked.insert(account, 0);"),
        "literal bool writes must lower to the canonical 1/0 inserts:\n{emitted}"
    );
    assert!(
        emitted.contains("return (self.blocked.get_or(account, 0) == 1);"),
        "a bool-map read must wrap as the canonical `== 1` comparison:\n{emitted}"
    );
    assert!(
        emitted.contains("trap_if(!(!((self.blocked.get_or(__fe_sender, 0) == 1))));"),
        "the `require(!blocked[msg.sender])` gate must read through the same wrap:\n{emitted}"
    );
}

// SOL-ACCESS PR3 × PR2: the AccessControl membership shape END-TO-END — a 2-key
// bool-valued map keyed by a FOLDED keccak role id, grant/revoke as 1/0, and the
// `onlyRole`-style `require(hasRole[ROLE][msg.sender])` gate reading through `== 1`.
// This is precisely the storage PR4's struct flatten will synthesize from OZ's
// `RoleData.hasRole`, proven working before the flatten exists.
#[test]
fn sol_access_bool_map_role_gate_composes_with_keccak() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/bool_map_roles.sol")).unwrap();
    let emitted = translate_ok(&src, "bool_map_roles.sol").text;
    let role = "0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6";
    assert!(
        emitted.contains(&format!("self.hasRole.insert({role}, account, 1);"))
            && emitted.contains(&format!("self.hasRole.insert({role}, account, 0);")),
        "grant/revoke must write 1/0 under the folded role id:\n{emitted}"
    );
    assert!(
        emitted.contains(&format!(
            "trap_if(!((self.hasRole.get_or({role}, __fe_sender, 0) == 1)));"
        )),
        "the onlyRole-style gate must read the folded role id through `== 1`:\n{emitted}"
    );
}

// SOL-ACCESS PR3 honest scope: a bool-map write COMPOSED with a later trap-capable
// write stays FE412 — the total-CEI/multimap transforms bail on bool-map writes (their
// hoists type values as u256), so the body keeps its natural CEI verdict. Fail-closed,
// zero AC impact (grant/revoke is a single write per function).
#[test]
fn sol_access_bool_map_write_then_arith_stays_fe412() {
    let src = "pragma solidity ^0.8.0;\ncontract C {\n  mapping(address => bool) flags;\n  uint256 count;\n  function f(address a) public { flags[a] = true; count = count + 1; }\n}\n";
    let got = translate_err(src).first().expect("a diagnostic").code;
    assert_eq!(got, "FE412", "the composed bool-write body must stay FE412");
}

// SOL-ACCESS PR4 / MC-4 + MI-3: the struct-map explode gives each field its OWN
// synthesized map (two DISTINCT declarations — conflation is impossible by
// construction), drops the struct + the map-to-struct var, and threads keys in
// SOURCE order (outer role key first, inner account key second).
#[test]
fn sol_access_struct_map_explodes_per_field_in_key_order() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/struct_map_roles.sol")).unwrap();
    let emitted = translate_ok(&src, "struct_map_roles.sol").text;
    assert!(
        emitted.contains("__fe_sm_6__roles_hasRole: BoundedMap2_u256_u256_u256_64")
            && emitted.contains("__fe_sm_6__roles_adminRole: BoundedMap_u256_u256_64"),
        "each field must explode into its OWN map of the right arity:\n{emitted}"
    );
    assert!(
        !emitted.contains("RoleData") && !emitted.contains("_roles:"),
        "the struct decl and the map-to-struct var must be dropped:\n{emitted}"
    );
    assert!(
        emitted.contains("self.__fe_sm_6__roles_hasRole.insert(role, account, 1);"),
        "grantRole must thread (outer role, inner account) in source order:\n{emitted}"
    );
    let role = "0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6";
    assert!(
        emitted.contains(&format!(
            "trap_if(!((self.__fe_sm_6__roles_hasRole.get_or({role}, __fe_sender, 0) == 1)));"
        )),
        "the onlyRole-style gate must compose keccak (PR2) × bool 0/1 (PR3) × the flatten (PR4):\n{emitted}"
    );
    assert!(
        emitted.contains("self.__fe_sm_6__roles_adminRole.insert(role, admin);"),
        "a scalar field write must lower to the 1-key insert:\n{emitted}"
    );
}

// SOL-ACCESS PR4: the parse-time path rewrite fires ONLY when the member is NOT
// immediately called — `bal[a].add(x)` is the SafeMath method idiom and must still
// fold to the checked operator, never become a phantom `__fe_sm_bal_add` map.
#[test]
fn sol_access_struct_map_rewrite_spares_safemath_calls() {
    let src = "pragma solidity ^0.8.0;\nlibrary SafeMath {}\ncontract K {\n  using SafeMath for uint256;\n  mapping(address => uint256) bal;\n  function f(address a, uint256 x) public view returns (uint256) { return bal[a].add(x); }\n}\n";
    let emitted = translate_ok(src, "k.sol").text;
    assert!(
        !emitted.contains("__fe_sm_"),
        "a CALLED member on an index must not be path-rewritten:\n{emitted}"
    );
    assert!(
        emitted.contains("(self.bal.get_or(a, 0) + x)"),
        "the SafeMath fold must still produce the checked `+`:\n{emitted}"
    );
}

// SOL-ACCESS PR5-W1: a parameterized modifier binds each param to its application arg
// EVAL-ONCE (a `let __fe_m<N>_<param> = <arg>` prelude), then reads the binding for every
// param use — a call-valued arg runs exactly once even when the param is used twice.
#[test]
fn sol_access_param_modifier_binds_arg_eval_once() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/param_modifier.sol")).unwrap();
    let emitted = translate_ok(&src, "param_modifier.sol").text;
    // The arg (the getter `limit()`) is bound ONCE to a fresh local...
    assert_eq!(
        emitted.matches("__fe_m0_fee: u256 = self.feeCap").count(),
        1,
        "the call-valued arg must be bound exactly once:\n{emitted}"
    );
    // ...and BOTH guard clauses read that binding (never re-evaluate the arg).
    assert_eq!(
        emitted.matches("__fe_m0_fee >").count() + emitted.matches("__fe_m0_fee <").count(),
        2,
        "both param uses must read the single binding:\n{emitted}"
    );
    assert!(
        !emitted.contains("self.feeCap)") || emitted.matches("self.feeCap").count() == 1,
        "the getter must be inlined once, not per use:\n{emitted}"
    );
}

// SOL-ACCESS PR5-W1: the OZ `onlyRole(role)` gate composes with PR2 (keccak) × PR3 (bool
// 0/1) × PR4 (struct flatten) — a call-arg `getRoleAdmin(role)` inlines once into the
// binding, a keccak-literal arg folds, and the guard reads the flattened 2-key bool map.
#[test]
fn sol_access_onlyrole_gate_composes_the_stack() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/onlyrole_gate.sol")).unwrap();
    let emitted = translate_ok(&src, "onlyrole_gate.sol").text;
    let role = "0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6";
    // grantRole's onlyRole(getRoleAdmin(role)) — the getter binds once, the guard reads it.
    assert!(
        emitted.contains("__fe_m0_role: u256 = self.__fe_sm_6__roles_adminRole.get_or")
            && emitted.contains(
                "trap_if(!((self.__fe_sm_6__roles_hasRole.get_or(__fe_m0_role, __fe_sender, 0) == 1)))"
            ),
        "onlyRole(getRoleAdmin(role)) must bind the admin-role once and gate on it:\n{emitted}"
    );
    // mintFor's onlyRole(keccak256("MINTER_ROLE")) — the keccak arg folds into the binding.
    assert!(
        emitted.contains(&format!("__fe_m1_role: u256 = {role}")),
        "a keccak-literal modifier arg must fold into the binding:\n{emitted}"
    );
}

// SOL-ACCESS PR5-W3: `_msgSender()` (the OZ Context shim) is discard-safe inside an
// `emit` — the whole emit drops (no SIGIL sink) and the shim is a pure read. The
// carve-out is sound ONLY because a declared `_msgSender` must be the pure `return
// msg.sender;` shim; an impure one (a side effect a discarded emit would drop) → FE481.
#[test]
fn sol_access_msgsender_in_emit_is_discard_safe() {
    let src = std::fs::read_to_string(fixtures_dir().join("compile/emit_msgsender.sol")).unwrap();
    let emitted = translate_ok(&src, "emit_msgsender.sol").text;
    assert!(
        emitted.contains("self.total = (self.total + v);") && !emitted.contains("Log"),
        "the emit (with its _msgSender() arg) must drop, leaving the state write:\n{emitted}"
    );
    // The fail-closed guard: an impure `_msgSender` rejects rather than silently dropping.
    let impure =
        std::fs::read_to_string(fixtures_dir().join("reject/emit_impure_msgsender.sol")).unwrap();
    assert_eq!(
        translate_err(&impure).first().expect("a diagnostic").code,
        "FE481",
        "a side-effecting `_msgSender` must reject fail-closed"
    );
}

// SOL-ACCESS PR5-W4: a bool-returning internal fn (OZ `_grantRole`) called as a STATEMENT
// inlines with its TAIL-position pure returns dropped (the value is discarded). A non-tail
// early return stays FE484 (fail-closed — flat inlining can't model mid-body control flow).
#[test]
fn sol_access_statement_call_drops_tail_pure_returns() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/grantrole_statement.sol")).unwrap();
    let emitted = translate_ok(&src, "grantrole_statement.sol").text;
    // The `return true`/`return false` are gone; the guarded insert remains.
    assert!(
        !emitted.contains("return true") && !emitted.contains("return false"),
        "tail returns must be stripped when the value is discarded:\n{emitted}"
    );
    assert!(
        emitted.contains("self._has.insert(__fe_inl1_role, __fe_inl1_a, 1);"),
        "the guarded body must survive the strip:\n{emitted}"
    );
    // Fail-closed: a non-tail early return keeps FE484.
    let mid = std::fs::read_to_string(fixtures_dir().join("reject/call_midreturn_statement.sol"))
        .unwrap();
    assert_eq!(
        translate_err(&mid).first().expect("a diagnostic").code,
        "FE484",
        "a non-tail early return must stay FE484"
    );
}

// SOL-ACCESS PR5 HEADLINE: a self-contained AccessControl-gated mint token exercises the
// whole ladder (PR1-4 + W1-W4) and its AUTHORITY is faithful — `mint` traps unless the
// caller holds MINTER_ROLE (the folded keccak id, read through the struct-flattened 2-key
// bool map); `grantRole` traps unless the caller holds the role's admin. supportsInterface
// (ERC165 introspection) is dropped. The real unmodified OZ AccessControlERC20MintBase
// also translates AND compiles via --project-root (proven at 49KB/66 AIR; not a CI fixture
// as the OZ corpus is out-of-repo).
#[test]
fn sol_access_headline_authcontrol_token_gates_are_faithful() {
    let src =
        std::fs::read_to_string(fixtures_dir().join("compile/access_control_token.sol")).unwrap();
    let emitted = translate_ok(&src, "access_control_token.sol").text;
    let minter = "0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6";
    // mint's gate: trap unless the caller holds MINTER_ROLE (folded keccak, flattened map).
    assert!(
        emitted.contains("__fe_inl6_role: u256 = self.MINTER_ROLE")
            && emitted.contains(
                "if !((self.__fe_sm_6__roles_hasRole.get_or(__fe_inl6_role, __fe_inl6_account, 0) == 1)) {"
            ),
        "mint must trap unless the caller holds MINTER_ROLE:\n{emitted}"
    );
    assert!(
        emitted.contains(&format!("MINTER_ROLE: {minter}")),
        "MINTER_ROLE must be the folded keccak constant:\n{emitted}"
    );
    // grantRole's onlyRole(getRoleAdmin(role)) gate reads the admin role once and traps.
    assert!(
        emitted.contains("__fe_m0_role: u256 = self.__fe_sm_6__roles_adminRole.get_or"),
        "grantRole must gate on the role's admin (onlyRole + getRoleAdmin, eval-once):\n{emitted}"
    );
    // ERC165 supportsInterface is dropped; the RoleData struct is exploded away.
    assert!(
        !emitted.contains("supportsInterface") && !emitted.contains("RoleData"),
        "supportsInterface (ERC165) and the RoleData struct must be gone:\n{emitted}"
    );
}
// ── Synthesized-name reservation: `self` (the emitted method receiver) and `new`
// (the emitted constructor) are emitter-OWNED names. A user identifier colliding
// with either must be rejected up front (FE420), not passed through to emit as a
// duplicate binding — a `self` param emits `fn f(self: C, self: u256)` (N005
// duplicate param) and `function new()` emits a second `new` in the impl (N002
// duplicate definition), both of which are INVISIBLE to the FE500 parse self-check
// (they are name-resolution errors, not parse errors). This mirrors the identifier
// gate the TypeScript frontend already applies via `expect_emittable_ident`.
#[test]
fn synthesized_names_self_and_new_are_reserved() {
    use sigil_frontends::codes::FE420_BAD_IDENTIFIER_SOL;
    let cases = [
        // parameter named `self` → duplicate receiver.
        "pragma solidity ^0.8.0;\ncontract C { function f(uint256 self) public pure returns (uint256) { return self; } }",
        // parameter named `new`.
        "pragma solidity ^0.8.0;\ncontract C { function f(uint256 new) public pure returns (uint256) { return new; } }",
        // function named `new` → duplicate constructor.
        "pragma solidity ^0.8.0;\ncontract C { function new() public { } }",
        // state variable named `self`.
        "pragma solidity ^0.8.0;\ncontract C { uint256 self; }",
    ];
    for src in cases {
        assert_eq!(
            translate_err(src)[0].code,
            FE420_BAD_IDENTIFIER_SOL,
            "expected FE420 for a synthesized-name collision in:\n{src}"
        );
    }
}
