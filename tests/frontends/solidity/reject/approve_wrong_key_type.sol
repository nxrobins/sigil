// expect-fe: FE443
// EX-4: a two-key write type-checks BOTH key positions. The allowance's second key is
// `address`, but `spender` here is a `uint256` — an address/uint256 confusion (FE443),
// not silently accepted.
pragma solidity ^0.8.0;
contract C {
    mapping(address => mapping(address => uint256)) allowance;
    function approve(uint256 spender, uint256 amount) public {
        allowance[msg.sender][spender] = amount;
    }
}
