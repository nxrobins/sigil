// SOL-INH M1: B inherits A's `onlyOwner` modifier + `owner` field; the inherited guard MUST survive
// flattening into setValue's emitted body (EX-3 — the dropped-guard existential). After merge, the
// pipeline inlines onlyOwner and lowers `msg.sender` → the `__fe_sender` param, so the trap appears.
pragma solidity ^0.8.0;

contract A {
    address owner;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }
}

contract B is A {
    uint256 value;

    function setValue(uint256 v) public onlyOwner {
        value = v;
    }
}
