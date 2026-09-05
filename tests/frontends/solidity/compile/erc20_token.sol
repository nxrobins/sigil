// SOL-TOKEN: the project's FIRST fully-translatable real ERC20 with metadata. `string` name/symbol
// are dropped (pure metadata, no SIGIL effect); `10 ** 18` constant-folds; decimals is a plain u256
// field; the transfer folds to the atomic `.transfer(...)` with its balance guard. Round-trips.
pragma solidity ^0.8.0;

contract MyToken {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    uint256 public totalSupply;
    string public name = "MyToken";
    string public symbol = "MTK";
    uint8 public decimals = 18;

    constructor() {
        totalSupply = 1000000 * 10 ** 18;
        balanceOf[msg.sender] = totalSupply;
    }

    function transfer(address to, uint256 amount) public returns (bool) {
        require(balanceOf[msg.sender] >= amount);
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function approve(address spender, uint256 amount) public returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }
}
