// SOL-ACCESS PR3 - a bool-valued mapping (the blocklist / allowlist shape). Storage is
// the SAME u256 bounded map with the CANONICAL 0/1 representation (EX-4): literal
// writes lower to insert(k, 1|0), reads lower to (get_or(k, 0) == 1) - a SIGIL bool.
// get_or's 0 default = false, exactly Solidity's mapping default. No lax truthiness
// can exist in storage: the only writers are the rewritten literals (MC-6).
pragma solidity ^0.8.0;
contract Blocklist {
    mapping(address => bool) blocked;
    uint256 total;

    function ban(address account) public {
        blocked[account] = true;
    }

    function unban(address account) public {
        blocked[account] = false;
    }

    function isBlocked(address account) public view returns (bool) {
        return blocked[account];
    }

    function deposit(uint256 amount) public {
        require(!blocked[msg.sender]);
        total = total + amount;
    }
}
