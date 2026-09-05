// expect-fe: FE454
// Review finding 1 (the load-bearing fix): inside an `onlyOwner` body, `msg.sender` IS the
// authorized owner identity (the gate pins `msg.sender == owner`). Solidity's `withdraw` can
// only ever debit `bal[owner]` (the caller == owner). Cap-translation would drop the gate and
// free `msg.sender` into the unconstrained `__fe_sender` — an `&C_Owner` holder could pass ANY
// address and drain `bal[victim]` (funds theft). The opaque cap can't supply the owner's
// address, so a guarded body that reads `msg.sender` is rejected (was the unsound H7 golden).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract Bank {
    address owner;
    mapping(address => uint256) bal;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function withdraw(address to, uint256 amt) public onlyOwner {
        require(bal[msg.sender] >= amt);
        bal[msg.sender] -= amt;
        bal[to] += amt;
    }
}
