// expect-fe: FE420
// A user function named `new` collides with the synthesized `new()` constructor — two
// impl-methods named `new` are an N002 duplicate at name-resolution (invisible to the FE500
// parse self-check). Rejected. (General SOL0 fix surfaced by the SOL-CAP review; no cap-mode
// directive needed — it applies to all Solidity translation.)
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function new(uint256 v) public {
        x = v;
    }
}
