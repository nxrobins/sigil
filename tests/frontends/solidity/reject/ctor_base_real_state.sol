// expect-fe: FE468
// SOL-XFILE PR4/L3: a base constructor that initializes REAL state (`owner`, a live field — not a
// dropped string) is NOT metadata-only and cannot be dropped: silently skipping it would leave the
// owner uninitialized (the Ownable class). Even the all-literal call cannot rescue it → FE468.
pragma solidity ^0.8.0;
abstract contract Owned {
    address owner;
    constructor(address o) { owner = o; }
    function who() public view returns (address) { return owner; }
}
contract C is Owned {
    constructor() Owned(0x0000000000000000000000000000000000000001) {}
}
