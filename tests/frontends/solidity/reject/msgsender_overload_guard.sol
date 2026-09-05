// expect-fe: FE481
// SOL-ACCESS PR5-W3 REGRESSION (CRITICAL, adversarial-review finding): the
// `_msgSender()`-discard-safe carve-out requires EVERY `_msgSender` to be the pure shim.
// OVERLOADING it (a 0-arg guard-bearing one + a sibling arity) used to defeat the check —
// `disambiguate_overloads` renamed the guard-bearing `_msgSender` to `__fe_ov0__msgSender`
// BEFORE reject_impure_msgsender's literal-name check ran, so its `require(msg.sender==owner)`
// vanished with the discarded emit, leaving grantRole COMPLETELY UNGATED (any caller grants
// any role). The check now runs BEFORE disambiguate_overloads and catches every overload:
// the guard-bearing 0-arg one fails the body check → FE481.
pragma solidity ^0.8.20;
contract C {
    address owner;
    mapping(bytes32 => mapping(address => bool)) _roles;
    event RoleGranted(bytes32 role, address account, address sender);
    function _msgSender() internal returns (address) { require(msg.sender == owner); return msg.sender; }
    function _msgSender(uint256 x) internal returns (address) { return msg.sender; }
    function grantRole(bytes32 role, address account) public {
        emit RoleGranted(role, account, _msgSender());
        _roles[role][account] = true;
    }
    function hasRole(bytes32 role, address a) public view returns (bool) { return _roles[role][a]; }
}
