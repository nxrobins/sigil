// expect-fe: FE410
// SOL-ACCESS EX-3: ONLY full-width `bytes32` is modeled (256-bit, right = full, no
// ambiguity). Every `bytesN` (N<32) is LEFT-aligned in Solidity — a right-aligned u256
// carrier would mis-order/mis-compare it (e.g. a `bytes4` function selector) — so it has
// no faithful bounded analog and stays FE410 (no left-alignment model in v1).
pragma solidity ^0.8.0;
contract C { bytes4 selector; }
