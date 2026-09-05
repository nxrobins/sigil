// expect-fe: FE441
// SOL-ACCESS: a bool KEY stays rejected (a 2-slot "map" is not the bounded-ledger
// shape; no real contract keys storage by bool). Only the VALUE position admits bool.
pragma solidity ^0.8.0;
contract C { mapping(bool => uint256) m; }
