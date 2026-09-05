// SOL-SAFEMATH (headline): the VERBATIM pre-4.4 OpenZeppelin `_transfer` shape, which uses SafeMath
// (`using SafeMath for uint256;` + `x.sub(y,"msg")`/`x.add(y)`) instead of 0.8 native checked math.
// The `using` directive is recognized + discarded; each SafeMath method call folds at PARSE time to
// the equivalent CHECKED SIGIL operator (`.sub`→`-`, `.add`→`+`; the revert-message string is dropped
// — SIGIL's trap carries no message). The resulting `balances[from] = balances[from] - amount;
// balances[to] = balances[to] + amount;` debit/credit then folds through `recognize_transfers` into the
// ATOMIC `self.balances.transfer(...)` — SafeMath composes with the existing recognizer, no new
// machinery. Round-trips through the trusted compiler.
pragma solidity ^0.8.0;
contract Token {
    using SafeMath for uint256;
    mapping(address => uint256) balances;

    function transfer(address to, uint256 amount) public {
        balances[msg.sender] = balances[msg.sender].sub(amount, "ERC20: transfer amount exceeds balance");
        balances[to] = balances[to].add(amount);
    }
}
