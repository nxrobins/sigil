// SOL-XFILE PR5/L4: `type(uint256).max` (the OZ `_spendAllowance` infinite-allowance sentinel)
// normalizes to the u256-max literal 2^256−1 in `normalize_literals`. `type(uint).max` is the same
// value. Both an assignment RHS and a comparison operand fold; any other `type(...)` stays FE401.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) allowance;

    function setInfinite(address s) public {
        allowance[s] = type(uint256).max;
    }

    function isInfinite(address s) public view returns (bool) {
        return allowance[s] == type(uint).max;
    }
}
