// expect-fe: FE401
// SOL-ACCESS MC-3: the lexer stores a string literal's RAW text (escapes unprocessed),
// so folding a literal containing `\` would hash the escape TEXT where solc hashes the
// escaped BYTE - a wrong-bytes constant that compiles. The raw-text gate refuses it:
// not folded, fail-closed.
pragma solidity ^0.8.0;
contract C {
    bytes32 h;
    function f() public {
        h = keccak256("MINTER\nROLE");
    }
}
