// expect-fe: FE443
// SOL-SAFEMATH EX-4: the parse-time fold is purely syntactic (no type info); it folds `owner.add(x)`
// to `owner + x` REGARDLESS of the receiver type. Soundness comes from the DOWNSTREAM checker, which
// re-validates operand types and rejects arithmetic on an `address` (FE443). So a wrong-receiver
// SafeMath call is never silently mis-lowered — it fails closed at check.
pragma solidity ^0.8.0;
contract C {
    using SafeMath for uint256;
    address owner;
    uint256 v;
    function f(uint256 x) public { v = owner.add(x); }
}
