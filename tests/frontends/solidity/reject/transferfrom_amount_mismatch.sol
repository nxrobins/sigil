// expect-fe: FE412
// SOL-XFILE PR6/AC-2: `recognize_spend_transfer` folds ONLY when the allowance-spend amount and the
// balance-move amount share a root (`same_root`). Here `_spendAllowance` spends `value` but the
// balance move transfers `value / 2` — a mismatch. The fold BAILS (never mistranslates to move the
// wrong amount); the conditional allowance write + the balance `Erc20Update` stay two committed map
// writes → the CEI gate rejects FE412 (fail-closed). Pins the amount-identity gate.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;
    uint256 private _totalSupply;

    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        address spender = msg.sender;
        uint256 half = value / 2;
        _spendAllowance(from, spender, value);
        _transfer(from, to, half);
        return true;
    }

    function _transfer(address from, address to, uint256 value) internal {
        if (from == address(0)) {
            revert("zero from");
        }
        if (to == address(0)) {
            revert("zero to");
        }
        _update(from, to, value);
    }

    function _update(address from, address to, uint256 value) internal {
        if (from == address(0)) {
            _totalSupply += value;
        } else {
            uint256 fromBalance = _balances[from];
            if (fromBalance < value) {
                revert("balance");
            }
            unchecked {
                _balances[from] = fromBalance - value;
            }
        }
        if (to == address(0)) {
            unchecked {
                _totalSupply -= value;
            }
        } else {
            unchecked {
                _balances[to] += value;
            }
        }
    }

    function _approve(address owner, address spender, uint256 value, bool emitEvent) internal {
        if (owner == address(0)) {
            revert("zero owner");
        }
        if (spender == address(0)) {
            revert("zero spender");
        }
        _allowances[owner][spender] = value;
    }

    function _spendAllowance(address owner, address spender, uint256 value) internal {
        uint256 currentAllowance = _allowances[owner][spender];
        if (currentAllowance < type(uint256).max) {
            if (currentAllowance < value) {
                revert("allowance");
            }
            unchecked {
                _approve(owner, spender, currentAllowance - value, false);
            }
        }
    }
}
