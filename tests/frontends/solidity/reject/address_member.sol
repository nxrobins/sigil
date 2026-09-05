// expect-fe: FE443
// SOL1b: `msg.sender` is now a valid `address` expression (the synthesized
// `__fe_sender` param), so assigning it to a `uint256` local is an address↔uint256
// mix → FE443 (NOT FE410). The synthesized sender is subject to the SAME
// address-distinctness rules as any address (NC-L3b) — it cannot silently become a
// uint256. (Other `msg.*`/`tx.*`/`block.*` members remain FE410; see msg_value_unsupported.)
pragma solidity ^0.8.0;
contract C { uint256 b; function f() public { uint256 z = msg.sender; b = z; } }
