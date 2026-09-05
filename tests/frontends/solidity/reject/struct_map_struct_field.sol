// expect-fe: FE441
// SOL-ACCESS EX-5: a struct-map whose struct has a STRUCT-typed field has no bounded
// per-field explode (the nested struct would need its own recursive flatten). The
// synthesized `mapping(K => Inner)` fail-closes at check - never a corrupted flatten.
pragma solidity ^0.8.0;
contract C {
    struct Inner { uint256 x; }
    struct Outer { Inner inner; uint256 y; }
    mapping(uint256 => Outer) m;
    function f(uint256 k) public view returns (uint256) { return m[k].y; }
}
