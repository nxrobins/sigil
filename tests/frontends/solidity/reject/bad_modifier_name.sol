// expect-fe: FE420
// A modifier name colliding with the reserved `__fe_` synth prefix is rejected pre-desugar
// (it would otherwise be confusable with a synthesized name after inlining).
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    modifier __fe_evil() {
        _;
    }

    function setX(uint256 v) public {
        x = v;
    }
}
