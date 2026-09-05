// A full ERC20 token core: balances + allowance (a nested mapping), with
// balanceOf / allowance getters, approve, transfer, and transferFrom. The
// `transferFrom` (allowance debit + balance move) folds into the single atomic
// trusted `allowance.transfer_from(balances, ...)` (SOL-ERC20). Event-free.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowance;

    function balanceOf(address who) public view returns (uint256) {
        return balances[who];
    }

    function allowanceOf(address owner, address spender) public view returns (uint256) {
        return allowance[owner][spender];
    }

    function approve(address spender, uint256 amount) public {
        allowance[msg.sender][spender] = amount;
    }

    function transfer(address to, uint256 amount) public {
        require(balances[msg.sender] >= amount);
        balances[msg.sender] -= amount;
        balances[to] += amount;
    }

    function transferFrom(address from, address to, uint256 amount) public returns (bool) {
        require(allowance[from][msg.sender] >= amount);
        allowance[from][msg.sender] -= amount;
        balances[from] -= amount;
        balances[to] += amount;
        return true;
    }
}
