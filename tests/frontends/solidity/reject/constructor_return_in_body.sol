// expect-fe: FE464
// EX-4: a constructor has no return value; an explicit `return` (even bare) would also
// short-circuit the synthesized tail `return __fe_c`. Early-exit is a documented anti-goal.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    constructor(uint256 a) {
        x = a;
        return;
    }
}
