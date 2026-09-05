// SOL-UPDATE: the OZ 5.x unified `_update(from, to, value)` — mint (`from == address(0)`),
// burn (`to == address(0)`), and transfer share ONE internal function whose debit and credit
// live in DIFFERENT `if` branches (formerly FE412: two committed writes across the branch
// join; and `address(0)` itself was FE401). The pipeline: `normalize_address_zero` rewrites
// the exact `address(0)` cast → `0` (the leading zero-guards SURVIVE as `if (x == 0) trap` —
// a transfer to the zero address still reverts); `inline_internal_calls` splices `_update`
// into each public method; `recognize_update` folds the 2-`if` dispatch pair into ONE atomic
// trusted `balances.erc20_update(totalSupply, from, to, value)` (dynamic mint/burn/transfer
// dispatch + `from == to` aliasing in verified stdlib, ALL traps before any write — the
// `eu_*` exec-proof), followed by a TRAP-FREE totalSupply store-back.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) _balances;
    uint256 _totalSupply;

    event Transfer(address from, address to, uint256 value);

    function _update(address from, address to, uint256 value) internal {
        if (from == address(0)) {
            _totalSupply += value;
        } else {
            uint256 fromBalance = _balances[from];
            if (fromBalance < value) {
                revert ERC20InsufficientBalance(from, fromBalance, value);
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
        emit Transfer(from, to, value);
    }

    function _transfer(address from, address to, uint256 value) internal {
        if (from == address(0)) {
            revert ERC20InvalidSender(address(0));
        }
        if (to == address(0)) {
            revert ERC20InvalidReceiver(address(0));
        }
        _update(from, to, value);
    }

    function transfer(address to, uint256 value) public returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    function mint(address account, uint256 value) public {
        if (account == address(0)) {
            revert ERC20InvalidReceiver(address(0));
        }
        _update(address(0), account, value);
    }

    function burn(uint256 value) public {
        _update(msg.sender, address(0), value);
    }
}
