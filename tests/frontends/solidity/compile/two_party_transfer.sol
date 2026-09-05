// SOL1b: the explicit two-party transfer (no msg.sender) — `bal[from] = bal[from] -
// a; bal[to] = bal[to] + a;`. Was a SOL1a FE412 reject (a second trap-capable map
// write after a committed write); now the recognizer folds the debit/credit idiom
// into the TRUSTED atomic `transfer`, so it is admitted and fund-safe by construction.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) bal;
    function move(address from, address to, uint256 a) public {
        bal[from] = bal[from] - a;
        bal[to] = bal[to] + a;
    }
}
