// expect-fe: FE401
// SOL-SAFEMATH EX-5: a `.add`/`.sub`/… method call is folded ONLY under an active
// `using SafeMath for uint256`. Without the directive it is an ordinary (unsupported) method call —
// FE401 — matching Solidity, where `.add` on a bare uint256 without the `using` is a type error.
pragma solidity ^0.8.0;
contract C {
    uint256 v;
    function f(uint256 a, uint256 b) public { v = a.add(b); }
}
