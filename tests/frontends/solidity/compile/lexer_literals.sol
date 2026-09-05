// Exercises the SOL-LEX literal forms that now translate (lexer-only, value-preserving): a
// single-quote `require` reason (dropped, like a double-quoted one), an underscore digit
// separator (`1_000` → 1000), and scientific notation (`2e9` → the plain integer 2000000000).
pragma solidity ^0.8.0;
contract Token {
    uint256 supply;

    function setSupply(uint256 a) public {
        require(a >= 1_000, 'amount too small');
        supply = 2e9;
    }

    function maxSupply() public pure returns (uint256) {
        return 1_000_000;
    }
}
