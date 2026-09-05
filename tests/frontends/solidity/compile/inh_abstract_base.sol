// SOL-XFILE PR2/L2: an ABSTRACT base contributes its PARSED members to the flattened concrete
// (unlike an interface, whose body is skipped) — the canonical OZ shape (`abstract contract ERC20`
// implements the real logic a derived token inherits). Here `B is A` flattens to A's `total` + `get`
// PLUS B's own `bump`; the abstract A is never itself a deployable sink.
pragma solidity ^0.8.0;

abstract contract A {
    uint256 total;
    function get() public view returns (uint256) { return total; }
}

contract B is A {
    function bump(uint256 v) public { total = total + v; }
}
