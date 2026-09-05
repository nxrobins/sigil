// expect-fe: FE420
// A contract named `BoundedMap2_u256_u256_u256_64` collides with the stdlib TWO-key map
// type the frontend emits for a nested `mapping`: the emitted `record BoundedMap2_…`
// suppresses stdlib injection, so `…::new()` binds to the user record's `new` — and under
// cap-mode that `new` is arity-changed, panicking the trusted re-verifier. Rejected
// fail-closed BEFORE emission (adversarial-review finding; the two-key twin of FE420).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract BoundedMap2_u256_u256_u256_64 {
    address owner;
    mapping(address => mapping(address => uint256)) allowance;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function setA(address s, uint256 v) public onlyOwner {
        allowance[s][s] = v;
    }
}
