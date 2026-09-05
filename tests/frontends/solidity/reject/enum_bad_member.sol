// expect-fe: FE466
// Name.Member where Member is not a member of the enum — the silent-wrong-value guard.
pragma solidity ^0.8.0;
contract C { enum Color { Red, Green } Color c; function f() public { c = Color.Purple; } }
