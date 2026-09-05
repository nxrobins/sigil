// expect-fe: FE481
// SOL-ACCESS PR5-W3 REGRESSION (adversarial-review finding): the `_msgSender()`-discard-safe
// carve-out requires `_msgSender` to be the PURE shim — no params, NO MODIFIERS, body
// exactly `return msg.sender;`. A gating modifier (`onlyController { require(...); _; }`) is
// inlined LATER than reject_impure_msgsender runs, so its `require` (a revert Solidity raises
// when `_msgSender()` is evaluated inside a discarded emit) would be silently dropped with the
// emit — WEAKENING authority (a non-controller call that Solidity reverts would succeed). The
// modifier'd shim is rejected fail-closed.
pragma solidity ^0.8.20;
contract C {
    address controller;
    uint256 total;
    event Access(address who);
    modifier onlyController() { require(msg.sender == controller); _; }
    function _msgSender() internal view onlyController returns (address) { return msg.sender; }
    function doThing() public { total = total + 1; emit Access(_msgSender()); }
}
