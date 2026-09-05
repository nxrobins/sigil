// expect-fe: FE410
// A `string` is droppable only as a metadata STATE field; a `string` param/return/local is rejected
// (SIGIL has no string type).
pragma solidity ^0.8.0;
contract C { function setName(string memory n) public {} }
