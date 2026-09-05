// SOL-ACCESS PR1 — `bytes32` as a full-width 256-bit opaque role/hash id (the `u256`
// carrier, exactly the `address → u256` precedent), the `constant` state-var modifier
// (modeled as a record field seeded with its compile-time literal), and a
// `mapping(bytes32 => uint256)` keyed by a role. This is the storage shape AccessControl
// needs, minus the keccak fold (PR2) and the role struct (PR4). No arrays.
pragma solidity ^0.8.0;
contract RoleRegistry {
    bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;
    bytes32 public constant MINTER_ROLE =
        0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6;

    mapping(bytes32 => uint256) roleMemberCount;
    bytes32 lastRole;

    function bump(bytes32 role) public {
        roleMemberCount[role] = roleMemberCount[role] + 1;
        lastRole = role;
    }

    function count(bytes32 role) public view returns (uint256) {
        return roleMemberCount[role];
    }

    function minterRole() public view returns (bytes32) {
        return MINTER_ROLE;
    }
}
