// SOL-CALLS (headline): the OpenZeppelin spine — a public `transfer` calls the internal
// `_transfer(_msgSender(), to, amount)`. Inlining substitutes `_msgSender()` (a pure single-return)
// → `msg.sender` → the `__fe_sender` param, and splices `_transfer`'s (alpha-renamed) body — whose
// debit/credit then flows through `recognize_transfers` and folds into the ATOMIC `.transfer(...)`
// (EX-6: the inlined body composes with the existing recognizer). Round-trips through the compiler.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;

    function _msgSender() internal view returns (address) {
        return msg.sender;
    }

    function _transfer(address from, address to, uint256 amount) internal {
        balances[from] -= amount;
        balances[to] += amount;
    }

    function transfer(address to, uint256 amount) public {
        _transfer(_msgSender(), to, amount);
    }
}
