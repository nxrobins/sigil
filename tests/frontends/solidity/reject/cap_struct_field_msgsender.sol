// expect-fe: FE454
// cap-mode (proactive — the IndexAssign2 review finding, recurring via the new FieldAssign
// variant): a guarded `onlyOwner` method whose ONLY `msg.sender` use is a STRUCT FIELD
// write. Cap-translation drops the gate and frees the untrusted `__fe_sender`, so the E-2
// data-use gate must see the field write and reject (FE454) — not silently weaken.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    struct S { address who; }
    S s;
    address owner;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function setWho() public onlyOwner {
        s.who = msg.sender;
    }
}
