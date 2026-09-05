// expect-fe: FE410
// SOL1b rewrites ONLY `msg.sender`; every other EVM global member (`msg.value`,
// `tx.origin`, `block.timestamp`, …) is left intact and still rejected (FE410) —
// no silent substitution.
pragma solidity ^0.8.0;
contract C { uint256 x; function pay() public { x = msg.value; } }
