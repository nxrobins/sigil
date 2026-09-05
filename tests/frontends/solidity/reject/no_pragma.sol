// expect-fe: FE411
// NC-S3: checked-by-default arithmetic requires a >= 0.8.0 pragma.
contract C { uint256 b; function f(uint256 a) public { b = a; } }
