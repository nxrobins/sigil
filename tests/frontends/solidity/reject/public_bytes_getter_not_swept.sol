// expect-fe: FE410
// SOL-XFILE PR5/L4: the dead-internal sweep is INTERNAL/PRIVATE-only (EX-5) — a PUBLIC function is
// part of the external ABI and is NEVER swept, even when uncalled and out of subset. This public
// `data()` returns `bytes` (unrepresentable) → NOT swept → its return type reaches check → FE410
// (fail-closed). Pins that the sweep cannot silently drop a public method.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function data() public view returns (bytes memory) {
        return msg.data;
    }

    function get() public view returns (uint256) {
        return x;
    }
}
