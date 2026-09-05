// expect-fe: FE412
// SOL-XFILE PR6/AC-2: `recognize_spend_transfer` folds ONLY when every statement between the
// `_spendAllowance` block and the balance `Erc20Update` is PURE filler (copy-`let`s + the `_transfer`
// zero-guards). Here transferFrom writes `lastSpender = spender` between the two — a storage write, not
// pure filler. The fold BAILS (a non-pure statement means the body is not the rigid transferFrom
// shape); the conditional allowance write + the `lastSpender` write + the balance move are multiple
// committed writes → the CEI gate rejects FE412 (fail-closed). Pins the filler-purity gate.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;
    uint256 private _totalSupply;
    address private lastSpender;

    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        address spender = msg.sender;
        _spendAllowance(from, spender, value);
        lastSpender = spender;
        _transfer(from, to, value);
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
