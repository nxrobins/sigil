// expect-fe: FE477
// `using X for Y;` (a free-function / library attachment) is a deferred feature — every form EXCEPT
// `using SafeMath for uint256` (which SOL-SAFEMATH recognizes + discards) stays a fail-closed FE477.
pragma solidity ^0.8.0;
using Address for address;
contract C { uint256 x; }
