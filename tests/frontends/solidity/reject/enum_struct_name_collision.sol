// expect-fe: FE420
// A name shared by an enum and a struct has two resolve_ty meanings.
pragma solidity ^0.8.0;
contract C { enum Foo { A, B } struct Foo { uint256 x; } uint256 y; }
