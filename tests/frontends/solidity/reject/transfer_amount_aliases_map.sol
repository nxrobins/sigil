// expect-fe: FE412
// SOUNDNESS (recognizer aliasing guard): the transfer fold requires from/to/amount to
// be free of map reads. Here `amount` is `bal[a]` — the SAME map being mutated — so
// folding to `transfer(a, b, bal[a])` would read the PRE-debit value, but Solidity
// credits `b` with the POST-debit value (0). The pair is left unfolded → the second
// trap-capable map write is FE412 (fail-closed; bind the amount to a local to fold it).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) bal;
    function drain(address a, address b) public {
        bal[a] -= bal[a];
        bal[b] += bal[a];
    }
}
