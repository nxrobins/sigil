// expect-fe: FE420
// A contract named `BoundedMap_u256_u256_64` collides with the stdlib map type the frontend
// emits for `mapping` fields: the field initializer `BoundedMap_u256_u256_64::new()` would
// resolve to the user record's `new`, and under cap-mode that `new` is arity-changed —
// ICE-ing the trusted re-verifier. Rejected fail-closed (review finding; general SOL1 fix).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract BoundedMap_u256_u256_64 {
    address owner;
    mapping(address => uint256) m;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function setM(address a, uint256 v) public onlyOwner {
        m[a] = v;
    }
}
