//! SOL-ERC20 adversarial regressions: the subtle "compiles-but-WRONG" risks for the
//! `transferFrom` atomic fold (the existential failure for a security translator — a
//! translation that compiles but means something weaker/different than the source).
//! Each probe constructs a transferFrom-SHAPED body that must NOT fold into the atomic
//! `transfer_from` with wrong operands; the fold fires ONLY on the exact canonical
//! pattern, and every near-miss is rejected (FE412/FE440/FE442/FE443) — never a
//! best-effort fold. Mirrors the post-impl empirical review (the SOL-CAP playbook).

use sigil_compiler::compile_named_module;
use sigil_frontends::frontend_for;

fn tr(src: &str) -> Result<String, Vec<String>> {
    frontend_for("solidity")
        .unwrap()
        .translate(src, "adv.sol")
        .map(|e| e.text)
        .map_err(|d| d.iter().map(|x| x.code.to_string()).collect())
}

const PRE: &str = "pragma solidity ^0.8.0;\n";
const MAPS: &str = "    mapping(address => uint256) balances;\n    mapping(address => mapping(address => uint256)) allowance;\n";

fn contract(body: &str) -> String {
    format!("{PRE}contract Token {{\n{MAPS}{body}\n}}\n")
}

/// L2: a transferFrom whose allowance debit `from` ≠ the balance move's `from` must NOT fold into the
/// atomic `transfer_from` with conflated operands (that WOULD be a wrong-operand mistranslation). The
/// security property is preserved: the atomic fold still requires exact operand match, so this shape is
/// NOT folded. Since SOL-MULTIMAP M-A, the un-folded shape TRANSLATES FAITHFULLY as a distinct-maps
/// reserved batch — the allowance decrement and the `other → to` balance move stay SEPARATE and keep the
/// SOURCE operands (it moves `other`'s funds, spending `from`'s allowance, exactly as the source says — a
/// buggy contract translated faithfully, never a translator-introduced conflation).
#[test]
fn transferfrom_mismatched_from_translates_faithfully_no_atomic_fold() {
    let src = contract(
        "    function transferFrom(address from, address other, address to, uint256 amount) public {\n\
         \x20       require(allowance[from][msg.sender] >= amount);\n\
         \x20       allowance[from][msg.sender] -= amount;\n\
         \x20       balances[other] -= amount;\n\
         \x20       balances[to] += amount;\n\
         \x20   }",
    );
    let text = tr(&src).expect("mismatched-from transferFrom translates faithfully via M-A");
    // NO wrong-operand atomic fold: the atomic transfer_from is NEVER emitted for a mismatched shape.
    assert!(
        !text.contains("transfer_from("),
        "a mismatched transferFrom must NOT fold into the atomic transfer_from:\n{text}"
    );
    // Faithful: the balance move is `other → to` (the source operands), NOT `from`/`other` conflated.
    assert!(
        text.contains("self.balances.transfer(other, to, amount)"),
        "the balance move must keep the source operands (other → to):\n{text}"
    );
    compile_named_module("adv.sol".to_string(), text).expect("must round-trip");
}

/// L2: the allowance debit amount ≠ the balance move amount — spending a different allowance than is
/// moved. Same as above: NOT folded into the atomic transfer_from (which requires matching amounts); M-A
/// translates it faithfully as separate ops — the allowance decrements by `other`, the balance moves
/// `amount`, exactly as the source says.
#[test]
fn transferfrom_mismatched_amount_translates_faithfully_no_atomic_fold() {
    let src = contract(
        "    function transferFrom(address from, address to, uint256 amount, uint256 other) public {\n\
         \x20       require(allowance[from][msg.sender] >= other);\n\
         \x20       allowance[from][msg.sender] -= other;\n\
         \x20       balances[from] -= amount;\n\
         \x20       balances[to] += amount;\n\
         \x20   }",
    );
    let text = tr(&src).expect("mismatched-amount transferFrom translates faithfully via M-A");
    assert!(
        !text.contains("transfer_from("),
        "a mismatched-amount transferFrom must NOT fold into the atomic transfer_from:\n{text}"
    );
    // Faithful: the balance move is `amount`, the allowance decrement is by `other` (distinct — as source).
    assert!(
        text.contains("self.balances.transfer(from, to, amount)")
            && text.contains("get_or(from, __fe_sender, 0) - other"),
        "the balance move (amount) and allowance decrement (other) must stay distinct:\n{text}"
    );
    compile_named_module("adv.sol".to_string(), text).expect("must round-trip");
}

/// L3: a HAND-WRITTEN "infinite approval" approximation (a `if allowance > amount { allowance -= a }`
/// guard over a raw `balances[from]-=a; balances[to]+=a`) still rejects FE412. SOL-XFILE PR6/AC-2
/// models the CANONICAL OZ 5.x transferFrom shape only — `recognize_spend_transfer` requires the exact
/// inlined spine (`let CA = alw[o][s]; if (CA < type(uint256).max) { alw[o][s] = CA - v }` then the
/// folded balance `Erc20Update`). This shape differs (a `>` guard, a compound `-=` debit, no `CA` read,
/// a `MapTransfer` not `Erc20Update`), so it does NOT match the tight recognizer, and its branch
/// allowance write plus the post-if balance move stay two committed writes → FE412 (fail-closed).
#[test]
fn transferfrom_infinite_approval_skip_rejects() {
    let src = contract(
        "    function transferFrom(address from, address to, uint256 amount) public {\n\
         \x20       if (allowance[from][msg.sender] > amount) { allowance[from][msg.sender] -= amount; }\n\
         \x20       balances[from] -= amount;\n\
         \x20       balances[to] += amount;\n\
         \x20   }",
    );
    match tr(&src) {
        Ok(text) => panic!("infinite-approval skip must reject, not fold:\n{text}"),
        Err(codes) => assert_eq!(codes.first().map(String::as_str), Some("FE412")),
    }
}

/// L3: a fee-on-transfer (an EXTRA balance write to a third party) leaves a write after
/// the atomic fold → FE412. The fold must not silently drop the fee.
#[test]
fn transferfrom_fee_on_transfer_rejects() {
    let src = contract(
        "    function transferFrom(address from, address to, address feeTo, uint256 amount) public {\n\
         \x20       require(allowance[from][msg.sender] >= amount);\n\
         \x20       allowance[from][msg.sender] -= amount;\n\
         \x20       balances[from] -= amount;\n\
         \x20       balances[to] += amount;\n\
         \x20       balances[feeTo] += amount;\n\
         \x20   }",
    );
    match tr(&src) {
        Ok(text) => panic!("fee-on-transfer must reject (extra write after the fold):\n{text}"),
        Err(codes) => assert_eq!(codes.first().map(String::as_str), Some("FE412")),
    }
}

/// L1 (positive, fold-correctness): the EXPANDED allowance debit form
/// `allowance[f][s] = allowance[f][s] - amount` must fold IDENTICALLY to the compound
/// `-=` form — same atomic `transfer_from`, correct operand order (from, spender=sender,
/// to, amount). Proves `as_allowance_debit`'s expanded arm + operand threading.
#[test]
fn transferfrom_expanded_debit_folds_correctly() {
    let src = contract(
        "    function transferFrom(address from, address to, uint256 amount) public {\n\
         \x20       require(allowance[from][msg.sender] >= amount);\n\
         \x20       allowance[from][msg.sender] = allowance[from][msg.sender] - amount;\n\
         \x20       balances[from] -= amount;\n\
         \x20       balances[to] += amount;\n\
         \x20   }",
    );
    let text = tr(&src).expect("expanded-form transferFrom must translate");
    assert!(
        text.contains("self.allowance.transfer_from(self.balances, from, __fe_sender, to, amount)"),
        "expanded debit must fold to the atomic transfer_from with correct operands:\n{text}"
    );
    compile_named_module("adv.sigil".to_string(), text).expect("must compile");
}

/// L5 (determinism + EX-8 byte-identity): the full ERC20 is deterministic, and an
/// existing SINGLE-level fixture is unchanged by the two-key work (no regression).
#[test]
fn erc20_deterministic_and_single_level_unchanged() {
    let full = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/frontends/solidity/compile/erc20_full.sol"),
    )
    .unwrap();
    let a = tr(&full).unwrap();
    let b = tr(&full).unwrap();
    assert_eq!(a, b, "erc20_full translation must be deterministic");

    // The single-level transfer ERC20 still emits the single-level `transfer`, NOT the
    // two-key path — the two-key work is purely additive (EX-8).
    let single = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/frontends/solidity/compile/erc20_transfer.sol"),
    )
    .unwrap();
    let text = tr(&single).unwrap();
    assert!(
        text.contains("self.balances.transfer(__fe_sender, to, amount)")
            && !text.contains("BoundedMap2")
            && !text.contains("transfer_from"),
        "single-level transfer must be unchanged (no two-key leakage):\n{text}"
    );
}
