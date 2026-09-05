// expect-fe: FE441
// SOL-ACCESS PR4 REGRESSION (adversarial-review CONFIRMED, HIGH): the synthesized
// per-field map name MUST be injective over (var, field). Two struct-maps whose
// (var, field) pairs mangle to the SAME string under a naive `__fe_sm_{var}_{field}`
// scheme — here struct-map `a_b`.`c` and the access `a[k].b_c` (a has NO field b_c) both
// naively -> `__fe_sm_a_b_c` — let the `a[k].b_c` access SILENTLY alias `a_b`'s storage
// slot (a cross-variable slot share, the PR's named existential). The length-prefixed
// injective encoding (`__fe_sm_<len>_<var>_<field>`) makes the collision structurally
// impossible: `a[k].b_c` -> __fe_sm_1_a_b_c is NOT among the synthesized names -> the
// residual sweep rejects it PRECISELY (never a silent shared slot).
pragma solidity ^0.8.0;
contract C {
    struct Sc { uint256 c; }
    mapping(uint256 => Sc) a_b;
    struct Sz { uint256 z; }
    mapping(uint256 => Sz) a;

    function writeReal(uint256 k, uint256 v) public { a_b[k].c = v; }
    function readTypo(uint256 k) public view returns (uint256) { return a[k].b_c; }
}
