// SOL-INH M0: a redundant `import` line is SKIPPED (its symbols are inline in a self-contained
// flattened file), and `virtual`/`override` inheritance specifiers are accepted-and-ignored
// (the function name is the override key — no flatten semantics). The contract translates as a
// plain flat contract.
pragma solidity ^0.8.0;
import "./IFoo.sol";
contract Foo {
    uint256 x;

    function setX(uint256 a) public virtual {
        x = a;
    }

    function getX() public view virtual override returns (uint256) {
        return x;
    }
}
