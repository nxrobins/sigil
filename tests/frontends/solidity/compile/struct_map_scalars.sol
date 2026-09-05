// SOL-ACCESS PR4 - an all-scalar struct under a mapping explodes into one 1-key map
// per field (formerly the reject/struct_valued_mapping.sol deferral). Field isolation:
// x and y live in DISTINCT synthesized maps; `points[a].x` rewrites to the 1-key
// access `__fe_sm_points_x[a]`.
pragma solidity ^0.8.0;
contract C {
    struct Point { uint256 x; uint256 y; }
    mapping(address => Point) points;

    function setX(address a, uint256 v) public { points[a].x = v; }
    function setY(address a, uint256 v) public { points[a].y = v; }
    function getX(address a) public view returns (uint256) { return points[a].x; }
    function sum(address a) public view returns (uint256) { return points[a].x + points[a].y; }
}
