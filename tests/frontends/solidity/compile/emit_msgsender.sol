// SOL-ACCESS PR5-W3: `_msgSender()` (the OZ Context shim for `msg.sender`) is discard-safe
// inside an `emit` — the event is dropped (no SIGIL sink), and `_msgSender()` is a pure
// global read, so dropping it with the emit loses nothing. Sound ONLY because a declared
// `_msgSender` MUST be the pure `return msg.sender;` shim (reject_impure_msgsender).
pragma solidity ^0.8.0;
contract C {
    event Log(address who, uint256 v);
    uint256 total;

    function _msgSender() internal view returns (address) { return msg.sender; }

    function bump(uint256 v) public {
        total = total + v;
        emit Log(_msgSender(), v);
    }
}
