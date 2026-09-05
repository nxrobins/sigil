// A contract exercising structs: a `struct` decl, a struct-typed state field (with a
// recursive zero-default in new()), whole-struct assignment + construction, field
// read/write, a struct param, and a struct return.
pragma solidity ^0.8.0;
contract Geometry {
    struct Point { uint256 x; uint256 y; }
    Point origin;
    uint256 moves;

    function setOrigin(uint256 a, uint256 b) public {
        origin = Point(a, b);
    }

    function shiftX(uint256 d) public {
        origin.x = origin.x + d;
    }

    function getX() public view returns (uint256) {
        return origin.x;
    }

    function makePoint(uint256 a, uint256 b) public pure returns (Point memory) {
        return Point(a, b);
    }

    function manhattan(Point memory p) public pure returns (uint256) {
        return p.x + p.y;
    }
}
