// expect-fe: FE420
// SOL-ACCESS: `keccak256` is a reserved builtin. A USER function of that name (solc
// historically only WARNS on builtin shadowing) would have its literal calls silently
// FOLDED instead of dispatched - a mistranslation. The declaration itself is rejected.
pragma solidity ^0.8.0;
contract C {
    function keccak256(uint256 x) public pure returns (uint256) { return x; }
}
