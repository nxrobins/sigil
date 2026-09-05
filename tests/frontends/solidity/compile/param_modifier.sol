// SOL-ACCESS PR5-W1: a parameterized modifier (was FE448) inlines by binding each param
// to its application argument EVAL-ONCE via a `let __fe_m<N>_<param> = <arg>;` prelude,
// then alpha-renaming the modifier body's param refs to that binding. The existential:
// a call-valued arg (`limit()`) must be evaluated exactly ONCE even though `fee` is used
// twice in the guard body — the single binding is read both times, the getter runs once.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    uint256 feeCap;

    modifier costs(uint256 fee) {
        require(fee > 0);
        require(fee < 1000);
        _;
    }

    function limit() public view returns (uint256) { return feeCap; }

    function setX(uint256 v) public costs(limit()) { x = v; }
}
