//! SOL-INH M1 — the C3-linearization + merge DIFFERENTIAL & SECURITY regressions.
//!
//! Pins, as permanent regressions, the three faithfulness properties a flatten (or a downstream
//! pass) change must never silently break:
//! - **EX-1 (C3 order):** the emitted state-field order == reverse(MRO), most-base-first, checked
//!   against KNOWN solc MROs for 5 hierarchies (linear / multi-base / Context-diamond / OZ-token /
//!   deep-wide). Hand-computed once from solc's C3 — NOT a live solc call.
//! - **EX-2 (override = derived-wins):** a base-declared-first method overridden by the derived
//!   emits the DERIVED body, never the base's (a file-order merge would invert it).
//! - **EX-3 (no dropped guard):** an inherited `modifier`'s guard survives into the merged body.
//!
//! Plus the fail-closed rejects (FE472 shadow / FE469 cycle / FE471 non-linearizable).

use sigil_frontends::frontend_for;

const P: &str = "pragma solidity ^0.8.0;\n";

fn emit(src: &str) -> String {
    frontend_for("solidity")
        .unwrap()
        .translate(src, "m.sol")
        .unwrap_or_else(|d| panic!("translate failed: {} {}", d[0].code, d[0].message))
        .text
}

fn reject(src: &str) -> String {
    match frontend_for("solidity").unwrap().translate(src, "m.sol") {
        Ok(e) => panic!("expected a reject, got OK:\n{}", e.text),
        Err(d) => d[0].code.to_string(),
    }
}

/// The merged record's field names in declared order (from the FIRST `record … { … }` line).
fn field_order(emit: &str) -> Vec<String> {
    let line = emit
        .lines()
        .find(|l| l.trim_start().starts_with("record "))
        .expect("a record declaration");
    let inner = line.split('{').nth(1).unwrap().split('}').next().unwrap();
    inner
        .split(',')
        .filter_map(|f| f.trim().split(':').next().map(|s| s.trim().to_string()))
        .filter(|s| !s.is_empty())
        .collect()
}

#[test]
fn c3_differential_field_order() {
    // Each contract carries a uniquely-named state field, so the emitted record field order reveals
    // the merge's most-base-first layout = reverse of solc's (most-derived-first) C3 MRO.
    let cases: &[(&str, &[&str])] = &[
        // linear: C is B is A → MRO [C,B,A] → fields [fa,fb,fc]
        (
            "contract A { uint256 fa; } contract B is A { uint256 fb; } contract C is B { uint256 fc; }",
            &["fa", "fb", "fc"],
        ),
        // multi: C is A, B → B is more-derived (listed last) → MRO [C,B,A] → [fa,fb,fc]
        (
            "contract A { uint256 fa; } contract B { uint256 fb; } contract C is A, B { uint256 fc; }",
            &["fa", "fb", "fc"],
        ),
        // OZ Context diamond: D is A,B; A,B is Ctx → MRO [D,B,A,Ctx] → [fctx,fa,fb,fd], Ctx ONCE
        (
            "contract Ctx { uint256 fctx; } contract A is Ctx { uint256 fa; } contract B is Ctx { uint256 fb; } contract D is A, B { uint256 fd; }",
            &["fctx", "fa", "fb", "fd"],
        ),
        // OZ token: Token is ERC20,Ownable; both is Ctx → MRO [Token,Ownable,ERC20,Ctx]
        (
            "contract Ctx { uint256 fctx; } contract ERC20 is Ctx { uint256 ferc; } contract Ownable is Ctx { uint256 fown; } contract Token is ERC20, Ownable { uint256 ftok; }",
            &["fctx", "ferc", "fown", "ftok"],
        ),
        // deep-wide: E is C,D; C is A,B; D is B → MRO [E,D,C,B,A] → [fa,fb,fc,fd,fe], shared B ONCE
        (
            "contract A { uint256 fa; } contract B { uint256 fb; } contract C is A, B { uint256 fc; } contract D is B { uint256 fd; } contract E is C, D { uint256 fe; }",
            &["fa", "fb", "fc", "fd", "fe"],
        ),
    ];
    for (src, want) in cases {
        let e = emit(&format!("{P}{src}"));
        assert_eq!(
            field_order(&e),
            *want,
            "C3 field-order mismatch for:\n{src}\n--- emit ---\n{e}"
        );
    }
}

#[test]
fn inherited_guard_survives() {
    // EX-3: B inherits A's `onlyOwner`; its `require(msg.sender == owner)` must reach setValue's body
    // as the exact lowered trap. A silently-dropped guard would be an access-control bypass.
    let e = emit(&format!(
        "{P}contract A {{ address owner; modifier onlyOwner() {{ require(msg.sender == owner); _; }} }}\ncontract B is A {{ uint256 value; function setValue(uint256 v) public onlyOwner {{ value = v; }} }}"
    ));
    assert!(
        e.contains("trap_if(!((__fe_sender == self.owner)))"),
        "inherited onlyOwner guard dropped from the merged setValue:\n{e}"
    );
}

#[test]
fn override_derived_wins() {
    // EX-2 / MC-2: Base is declared FIRST in the file (the OZ norm) and Derived overrides val(). The
    // DERIVED body (return 2) must win — a file-order merge would wrongly keep Base's (return 1).
    let e = emit(&format!(
        "{P}contract Base {{ uint256 x; function val() public view returns (uint256) {{ return 1; }} }}\ncontract Derived is Base {{ function val() public view returns (uint256) {{ return 2; }} }}"
    ));
    assert!(e.contains("return 2"), "derived override lost:\n{e}");
    assert!(
        !e.contains("return 1"),
        "base body wrongly won (override inverted):\n{e}"
    );
}

#[test]
fn type_alias_override_is_not_an_overload() {
    // `f(uint)` over `f(uint256)` is a faithful override (uint ≡ uint256), not an inherited overload
    // — it must translate (derived wins), not reject FE420.
    let e = emit(&format!(
        "{P}contract Base {{ uint256 x; function setX(uint a) public {{ x = a; }} }}\ncontract Derived is Base {{ function setX(uint256 a) public {{ x = a; }} }}"
    ));
    assert!(
        e.contains("setX"),
        "alias override failed to translate:\n{e}"
    );
}

#[test]
fn abstract_inheritor_does_not_mask_the_concrete() {
    // A concrete deployable (`Token`) extended by an ABSTRACT contract must still be selected as the
    // main — the abstract inheritor is undeployable and must not be misread as a cycle.
    let e = emit(&format!(
        "{P}contract Token {{ uint256 supply; function setSupply(uint256 s) public {{ supply = s; }} }}\nabstract contract Ext is Token {{ function more() public view returns (uint256); }}"
    ));
    assert!(
        e.contains("record Token"),
        "concrete Token masked by its abstract inheritor:\n{e}"
    );
}

#[test]
fn fail_closed_rejects() {
    // shadow
    assert_eq!(
        reject(&format!(
            "{P}contract A {{ uint256 x; }} contract B is A {{ uint256 x; }}"
        )),
        "FE472"
    );
    // cycle
    assert_eq!(
        reject(&format!(
            "{P}contract A is B {{ uint256 x; }} contract B is A {{ uint256 y; }}"
        )),
        "FE469"
    );
    // non-linearizable (A wants X-before-Y, B wants Y-before-X)
    assert_eq!(
        reject(&format!(
            "{P}contract X {{ uint256 fx; }} contract Y {{ uint256 fy; }} contract A is X, Y {{ uint256 fa; }} contract B is Y, X {{ uint256 fb; }} contract D is A, B {{ uint256 fd; }}"
        )),
        "FE471"
    );
}
