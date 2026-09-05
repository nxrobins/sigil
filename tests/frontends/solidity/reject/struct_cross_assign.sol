// expect-fe: FE445
// EX-2: structs are NOMINAL — a value of struct `A` is not assignable where `B` is
// expected, even with identical fields. No structural coercion.
pragma solidity ^0.8.0;
contract C {
    struct A { uint256 v; }
    struct B { uint256 v; }
    function f(A memory a) public pure returns (B memory) {
        return a;
    }
}
