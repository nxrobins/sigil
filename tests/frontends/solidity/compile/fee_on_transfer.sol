// SOL-MULTIMAP M-B: the fee-on-transfer / reflection idiom — a debit + TWO credits on the SAME
// `balances` map (`balances[from] -= amount; balances[to] += net; balances[feeTo] += fee;`). This was an
// FE412 reject (≥2 same-map writes; the keys can alias, e.g. `to == feeTo`, which the frontend cannot
// disprove). M-B folds it into an atomic `transfer_split`, whose aliasing across all 5 partitions of
// {from,to,feeTo} lives in verified stdlib (exec-proven), all checks before any write.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;

    function splitTransfer(address to, address feeTo, uint256 amount, uint256 fee) public {
        uint256 net = amount - fee;
        balances[msg.sender] -= amount;
        balances[to] += net;
        balances[feeTo] += fee;
    }
}
