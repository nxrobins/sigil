// sigil:cap-access-control
// SOL-HARDEN C2 (pin): under cap-mode, an `emit` argument that READS the owner field is DISCARDED at
// parse (SOL-EVENTS) BEFORE the E-2 data-use gate runs, so it is NOT a disqualifying data-use. This is
// sound — the discarded emit has no SIGIL sink, and FE481 guarantees the discarded arg is side-effect-
// free (a pure read). This fixture pins the (accepted, authority-faithful) behavior across the three
// owner-in-emit shapes, including the STRONGEST one E-2 would otherwise reject:
//   1. a plain owner read           `emit OwnerPoked(owner);`
//   2. an owner-as-MAP-KEY read     `emit BalRead(balances[owner]);`   (E-2 lists "a map key" as data)
//   3. an emit BETWEEN the gate `require` and `_` in the modifier (would be an FE455 near-miss if it
//      survived; post-discard the body is the exact gate shape and recognizes cleanly).
// The `&C_Owner` gate is intact and the owner field is dropped exactly as for a no-emit cap contract.
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 x;
    mapping(address => uint256) balances;

    event OwnerPoked(address who);
    event GateHit(address who);
    event BalRead(uint256 amount);

    modifier onlyOwner() {
        require(msg.sender == owner);
        emit GateHit(owner);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        emit OwnerPoked(owner);
        emit BalRead(balances[owner]);
        x = v;
    }
}
