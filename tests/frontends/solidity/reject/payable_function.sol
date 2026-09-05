// expect-fe: FE452
// `payable` (like `virtual`/`override`) lexes as a bare ident in the function-attribute
// position; it is recognized as a fixed unsupported-attribute set and rejected precisely,
// not reported as a confusing "undefined modifier".
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function deposit(uint256 v) public payable {
        x = v;
    }
}
