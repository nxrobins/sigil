// expect-fe: FE420
// adversarial-review wart: a struct named after a SIGIL BUILTIN type (`u256`) would emit
// `record u256`, colliding with the primitive in the trust anchor (a downstream T-code).
// `u256` is not a Solidity token, so it slips past the scalar interception — reject cleanly.
pragma solidity ^0.8.0;
contract C {
    struct u256 { uint256 x; }
}
