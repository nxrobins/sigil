// expect-fe: FE420
// SOL1b adversarial-review fix (L4-01, EXISTENTIAL sound-hole): a user local named
// `__fe_0` must be rejected. Before the fix, locals were never identifier-checked, so
// a user `__fe_0` collided with the &&/|| desugar temp — the later binding won, and a
// `require(__fe_0)`/`return __fe_0` silently observed the &&/|| result (guard bypass).
pragma solidity ^0.8.0;
contract C {
    function f(uint256 a, uint256 b) public pure returns (bool) {
        bool __fe_0 = (a == 7);
        bool ok = (a > 0) && (b > 0);
        return __fe_0;
    }
}
