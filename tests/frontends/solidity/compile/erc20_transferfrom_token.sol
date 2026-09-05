// SOL-XFILE PR6/AC-2: a self-contained OZ 5.x `transferFrom` token. The public `transferFrom` inlines
// `_spendAllowance` (an infinite-allowance dispatch `if (currentAllowance < type(uint256).max)` guarding
// an `_allowances[owner][spender] = currentAllowance - value` decrement) + `_transfer` (zero-guards →
// `_update` → the folded balance `Erc20Update`). `recognize_spend_transfer` folds the whole spine to ONE
// atomic `self._allowances.erc20_transfer_from(self._balances, from, __fe_sender, to, value)` (the
// trusted primitive: zero-guarded, infinite-allowance-skipping, atomic across both maps) — so it passes
// CEI and round-trips. `approve`/`transfer`/`mint` complete a usable token.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;
    uint256 private _totalSupply;

    function allowance(address owner, address spender) public view returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 value) public returns (bool) {
        address owner = msg.sender;
        _approve(owner, spender, value, true);
        return true;
    }

    function transfer(address to, uint256 value) public returns (bool) {
        address owner = msg.sender;
        _transfer(owner, to, value);
        return true;
    }

    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        address spender = msg.sender;
        _spendAllowance(from, spender, value);
        _transfer(from, to, value);
        return true;
    }

    function mint(address account, uint256 value) public {
        _update(address(0), account, value);
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
        uint256 currentAllowance = allowance(owner, spender);
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
