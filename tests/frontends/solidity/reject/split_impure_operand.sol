// expect-fe: FE412
// SOL-MULTIMAP M-B EX-B3 (pure operands): a split whose operand READS a map (here the `to` credit's amount
// is `balances[x]`, an Index) is not `is_transfer_operand`-pure — its value is not stable across the atomic
// `transfer_split`, so `recognize_split` does NOT fold it → the 3 same-map writes hit the CEI gate → FE412.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;

    function f(address to, address feeTo, uint256 amount, uint256 fee, address x) public {
        balances[msg.sender] -= amount;
        balances[to] += balances[x];
        balances[feeTo] += fee;
    }
}
