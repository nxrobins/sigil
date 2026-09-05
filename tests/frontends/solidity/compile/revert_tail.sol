// SOL-DIVERGE (headline, EX-3): a VALUE-returning function whose main path ends in `revert()`. The
// revert lowers to the divergent `trap()` (bottom type `Never`, #442-444), so the return checker sees
// the path terminate — no T044 missing-return. Under the old `trap_if(true)` (a conditional Unit trap)
// this emitted `… trap_if(true); }` with no trailing return and FAILED to compile through the trusted
// compiler. Round-trips now.
pragma solidity ^0.8.0;
contract Store {
    uint256 value;
    bool present;

    function get() public view returns (uint256) {
        if (present) {
            return value;
        }
        revert("not present");
    }
}
