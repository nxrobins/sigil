// SOL1c headline: the ubiquitous access-control modifier. `onlyOwner` inlines its
// `require(msg.sender == owner)` guard around the function body (the `_` placeholder),
// in the desugar pass. The guard's `msg.sender` flows through the SAME lowering as a
// body `msg.sender` → the synthesized `__fe_sender` caller-authority param.
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }
}
