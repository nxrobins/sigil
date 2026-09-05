// expect-fe: FE490
// SOL-SAFEMATH EX-2: the `.sub`/`.div`/`.mod` 2nd argument may ONLY be a string revert-message (which
// is dropped). A non-string 2nd arg (`a.sub(x, y)`) is NOT the SafeMath message form — fail-closed
// rejected, so the fold can never mis-index a computed value into (or out of) the arithmetic.
pragma solidity ^0.8.0;
contract C {
    using SafeMath for uint256;
    uint256 v;
    function f(uint256 a, uint256 b) public { v = a.sub(a, b); }
}
