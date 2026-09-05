// A constructor with arguments + deploy-time init logic: validates the supply, sets the
// owner to the deployer (`msg.sender` → the `__fe_sender` deploy param), the initial supply,
// and mints the supply to the deployer. Lowered to a `new(...)` that builds the record as a
// local `__fe_c`, runs the body on it (CEI-moot), and returns it.
pragma solidity ^0.8.0;
contract Token {
    address owner;
    uint256 totalSupply;
    mapping(address => uint256) balances;

    constructor(uint256 initialSupply) {
        require(initialSupply > 0);
        owner = msg.sender;
        totalSupply = initialSupply;
        balances[msg.sender] = initialSupply;
    }

    function balanceOf(address who) public view returns (uint256) {
        return balances[who];
    }
}
