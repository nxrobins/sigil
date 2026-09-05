// SOL-TOKEN: constant `**` folds (faithful to Solidity 0.8's checked exponentiation). `2 ** 3 ** 2`
// is right-associative (= 2 ** 9 = 512); `10 ** 18` is the decimals idiom.
pragma solidity ^0.8.0;
contract C {
    function a() public pure returns (uint256) { return 10 ** 18; }
    function b() public pure returns (uint256) { return 2 ** 3 ** 2; }
    function c() public pure returns (uint256) { return 1000 * 10 ** 6; }
}
