// SOL-ACCESS PR2 - compile-time `keccak256("literal")` -> the precomputed Keccak-256
// hash as a u256 constant (the AccessControl role-id idiom). The fold happens at PARSE
// (the **/SafeMath precedent), so the emitted SIGIL carries the REAL on-chain role id
// (independently verified: MINTER_ROLE = 0x9f2df0fe...c8956a6) and the role gates work
// against the same values a deployed Solidity contract uses. Roles key the existing
// two-key bounded map; no new storage machinery.
pragma solidity ^0.8.0;
contract RoleStore {
    bytes32 public constant MINTER_ROLE = keccak256("MINTER_ROLE");
    bytes32 public constant BURNER_ROLE = keccak256("BURNER_ROLE");

    mapping(bytes32 => mapping(address => uint256)) members;

    function grantRole(bytes32 role, address account) public {
        members[role][account] = 1;
    }

    function hasRole(bytes32 role, address account) public view returns (uint256) {
        return members[role][account];
    }

    function isMinter(address account) public view returns (uint256) {
        return members[keccak256("MINTER_ROLE")][account];
    }
}
