// expect-fe: FE412
// EX-1/EX-2: a non-canonical transferFrom (the balance credit uses a DIFFERENT amount
// `fee`, so the debit/credit does not fold into an atomic MapTransfer) leaves two
// separate storage writes — rejected by the CEI gate, so no non-atomic transferFrom
// can compile (SIGIL cannot roll back the allowance debit if a later write traps).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowance;
    function transferFrom(address from, address to, uint256 amount, uint256 fee) public {
        require(allowance[from][msg.sender] >= amount);
        allowance[from][msg.sender] -= amount;
        balances[from] -= amount;
        balances[to] += fee;
    }
}
