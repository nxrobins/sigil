// expect-fe: FE401
// SOL-XFILE PR5/L4: `normalize_literals` folds ONLY `type(uint256).max` / `type(uint).max` to the
// u256-max literal. `type(uint128).max` is a NARROW-width max whose value-carrier semantics are not
// modeled, so it is left intact → the `type(...)` call reaches check as an unsupported call → FE401
// (fail-closed). Pins the normalize's exact-width tightness.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) allowance;

    function setInfinite(address s) public {
        allowance[s] = type(uint128).max;
    }
}
