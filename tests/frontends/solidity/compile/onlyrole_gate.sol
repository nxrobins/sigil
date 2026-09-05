// SOL-ACCESS PR5-W1: the OZ AccessControl `onlyRole(role)` gate END-TO-END. The
// parameterized modifier binds its `role` arg eval-once (a call arg `getRoleAdmin(role)`
// inlines once; a `keccak256("MINTER_ROLE")` arg folds), and the guard
// `require(_roles[role].hasRole[msg.sender])` reads the struct-flattened 2-key bool map
// (PR4) with the canonical 0/1 wrap (PR3) — the whole AC authority story composing.
pragma solidity ^0.8.20;
contract Gated {
    struct RoleData { mapping(address => bool) hasRole; bytes32 adminRole; }
    mapping(bytes32 => RoleData) _roles;
    uint256 minted;

    modifier onlyRole(bytes32 role) {
        require(_roles[role].hasRole[msg.sender]);
        _;
    }

    function getRoleAdmin(bytes32 role) public view returns (bytes32) {
        return _roles[role].adminRole;
    }

    function grantRole(bytes32 role, address account) public onlyRole(getRoleAdmin(role)) {
        _roles[role].hasRole[account] = true;
    }

    function mintFor(uint256 amount) public onlyRole(keccak256("MINTER_ROLE")) {
        minted = minted + amount;
    }
}
