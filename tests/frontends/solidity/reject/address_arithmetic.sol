// expect-fe: FE443
// NC-L3a/LM3: address is a CLOSED type — arithmetic on it is rejected (only ==/!=).
pragma solidity ^0.8.0;
contract C { function f(address a) public pure returns (address) { return a + 1; } }
