// expect-fe: FE441
// SOL-ACCESS: a whole-`M[k]` read of an exploded struct-map (a struct copy - illegal
// Solidity for a mapping-bearing struct anyway) - only `M[k].<field>` paths exist
// after the explode; the surviving bare `_roles` reference is rejected PRECISELY
// (never a baffling "undeclared variable" for a var the user declared).
pragma solidity ^0.8.0;
contract C {
    struct RoleData { mapping(address => bool) hasRole; bytes32 adminRole; }
    mapping(bytes32 => RoleData) _roles;
    bytes32 last;
    function f(bytes32 role) public { last = _roles[role].adminRole; }
    function g(bytes32 role) public view returns (bytes32) { return _roles[role]; }
}
