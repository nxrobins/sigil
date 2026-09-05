// SOL-ACCESS PR3 - the 2-key bool-valued map IS the AccessControl role-membership
// storage shape (what PR4's struct flatten will produce from RoleData.hasRole):
// mapping(role => mapping(account => bool)) over the existing BoundedMap2, values
// canonical 0/1. The onlyRole-style gate `require(hasRole[role][msg.sender])` reads
// through the same wrap. Composes with PR2: the role id is a folded keccak constant.
pragma solidity ^0.8.0;
contract Roles {
    bytes32 public constant MINTER_ROLE = keccak256("MINTER_ROLE");
    mapping(bytes32 => mapping(address => bool)) hasRole;
    uint256 minted;

    function grantMinter(address account) public {
        hasRole[keccak256("MINTER_ROLE")][account] = true;
    }

    function revokeMinter(address account) public {
        hasRole[keccak256("MINTER_ROLE")][account] = false;
    }

    function isMinter(address account) public view returns (bool) {
        return hasRole[keccak256("MINTER_ROLE")][account];
    }

    function mint(uint256 amount) public {
        require(hasRole[keccak256("MINTER_ROLE")][msg.sender]);
        minted = minted + amount;
    }
}
