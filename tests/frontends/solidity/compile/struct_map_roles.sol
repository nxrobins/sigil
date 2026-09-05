// SOL-ACCESS PR4 - the struct-of-mappings flatten: the VERBATIM OZ AccessControl
// storage shape. `mapping(bytes32 => RoleData)` explodes into one synthesized map per
// field (__fe_sm__roles_hasRole: 2-key bytes32*address->bool canonical 0/1;
// __fe_sm__roles_adminRole: 1-key bytes32->u256); every `_roles[role].field...`
// access was rewritten AT PARSE to the same names (one shared mangle - decl and
// access cannot disagree), keys threaded in source order (MI-3). The struct decl and
// the map-to-struct var are dropped. Composes with PR2 (folded keccak role ids) and
// PR3 (bool canonical 0/1) - the full AccessControl storage story.
pragma solidity ^0.8.20;
contract RoleStore {
    struct RoleData {
        mapping(address => bool) hasRole;
        bytes32 adminRole;
    }

    mapping(bytes32 => RoleData) private _roles;
    uint256 minted;

    function hasRole(bytes32 role, address account) public view returns (bool) {
        return _roles[role].hasRole[account];
    }

    function getRoleAdmin(bytes32 role) public view returns (bytes32) {
        return _roles[role].adminRole;
    }

    function grantRole(bytes32 role, address account) public {
        _roles[role].hasRole[account] = true;
    }

    function revokeRole(bytes32 role, address account) public {
        _roles[role].hasRole[account] = false;
    }

    function setRoleAdmin(bytes32 role, bytes32 admin) public {
        _roles[role].adminRole = admin;
    }

    function mint(uint256 amount) public {
        require(_roles[keccak256("MINTER_ROLE")].hasRole[msg.sender]);
        minted = minted + amount;
    }
}
