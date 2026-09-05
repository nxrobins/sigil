// expect-fe: FE481
// SOL-ACCESS PR5-W3: the `_msgSender()`-is-discard-safe carve-out is sound ONLY if
// `_msgSender` is the pure `return msg.sender;` shim. A `_msgSender` with a SIDE EFFECT
// (here a state write) could be dropped silently with a discarded emit — rejected loud.
pragma solidity ^0.8.0;
contract C {
    event Log(address who);
    uint256 calls;
    function _msgSender() internal returns (address) { calls = calls + 1; return msg.sender; }
    function f() public { emit Log(_msgSender()); }
}
