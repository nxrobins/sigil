// expect-fe: FE430
// NC-L3c/LM5 (adversarial-review fix): a state-field `address` initializer must get
// the same 160-bit range gate as a body-position assignment. A >160-bit literal here
// (42 hex digits = 168 bits) is a value Solidity itself forbids for an address; before
// the fix it bypassed the gate and round-tripped clean (an out-of-range address in the
// u256 carrier). The frontend is the SOLE gate for this — the compiler sees only u256.
pragma solidity ^0.8.0;
contract C {
    address owner = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
    function getOwner() public view returns (address) { return owner; }
}
