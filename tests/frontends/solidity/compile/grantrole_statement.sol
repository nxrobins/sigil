// SOL-ACCESS PR5-W4: a value-returning internal fn (`_grantRole` returns bool) called as
// a STATEMENT (return value discarded). Its `if (…) { …; return true; } else { return
// false; }` has TAIL-position PURE returns — when the value is discarded, those returns
// are just "the body ends here" and drop, leaving `if (…) { insert }`. Works in a method
// AND the (CEI-exempt) constructor — the OZ AccessControl `_grantRole` shape.
pragma solidity ^0.8.20;
contract R {
    mapping(bytes32 => mapping(address => bool)) _has;

    function hasRole(bytes32 role, address a) public view returns (bool) { return _has[role][a]; }

    function _grantRole(bytes32 role, address a) internal returns (bool) {
        if (!hasRole(role, a)) {
            _has[role][a] = true;
            return true;
        } else {
            return false;
        }
    }

    function grantRole(bytes32 role, address a) public { _grantRole(role, a); }
    constructor(address admin) { _grantRole(0x00, admin); }
}
