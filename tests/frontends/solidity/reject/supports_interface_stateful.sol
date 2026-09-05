// expect-fe: FE410
// SOL-ACCESS W2: the supportsInterface introspection drop is gated on `view`/`pure`. A
// NON-view function of that name (which could mutate state / grant authority) does NOT
// match the drop — it stays rejected on its body (the bytes4 param → FE410), never
// silently removed. (Here the body is out of subset; the point is it is NOT dropped.)
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    function supportsInterface(bytes4 id) public returns (bool) { x = 1; return true; }
}
