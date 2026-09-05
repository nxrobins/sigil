// expect-fe: FE441
// SOL-ACCESS EX-5: a 2-level mapping FIELD would synthesize a 3-key map (no bounded
// analog, FE440 territory) - the explode BAILS and the surviving `m[k].deep` access
// gets the precise struct-map reject (fail-closed).
pragma solidity ^0.8.0;
contract C {
    struct D { mapping(address => mapping(address => uint256)) deep; }
    mapping(uint256 => D) m;
    function f(uint256 k, address a, address b) public view returns (uint256) { return m[k].deep[a][b]; }
}
