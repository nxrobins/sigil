// expect-fe: FE476
// SOL-XFILE PR2/L2: a LIBRARY used as an inheritance base stays rejected — libraries are
// `using`-attached / called, never a faithful inheritance base in the subset. (Abstract and
// interface bases ARE now admitted; only `library` remains FE476 in the `is` position.)
pragma solidity ^0.8.0;
library L { function helper() internal pure returns (uint256) { return 1; } }
contract B is L { uint256 y; }
