// expect-fe: FE490
// SOL-SAFEMATH EX-1: under an active `using SafeMath for uint256`, a SafeMath method call with the
// wrong arity (`.add` takes ONE operand — `.add(a, b)` is the library form, not the method form) is
// fail-closed rejected, never folded with a silently-dropped argument.
pragma solidity ^0.8.0;
contract C {
    using SafeMath for uint256;
    uint256 v;
    function f(uint256 a, uint256 b) public { v = a.add(a, b); }
}
