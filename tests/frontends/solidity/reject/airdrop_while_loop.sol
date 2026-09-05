// expect-fe: FE401
// The greenfield parse surface admits ONLY the one rigid airdrop `for` header. A `while` loop is
// not in the `Stmt` grammar → `parse_stmt`'s default arm → FE401. No general loop survives.
pragma solidity ^0.8.20;
contract C {
    function f(uint256 n) external {
        uint256 i = 0;
        while (i < n) {
            i = i + 1;
        }
    }
}
