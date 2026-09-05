// expect-fe: FE481
// A discarded `emit` must not drop a side effect: an emit argument that is a CALL (which could
// mutate state) is rejected rather than silently dropped.
pragma solidity ^0.8.0;
contract C {
    function f() public {
        emit E(g());
    }
}
