// expect-fe: FE485
// SOL-CALLS: mutual recursion between internal functions. Inlining requires an acyclic call graph
// (each callee is pushed onto a stack; a callee already on the stack → FE485). The OZ spine is acyclic.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function a() internal {
        b();
    }

    function b() internal {
        a();
    }

    function go() public {
        a();
    }
}
