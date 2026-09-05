// SOL-ACCESS PR5 HEADLINE: a self-contained AccessControl-gated mint token exercising the
// WHOLE stack — bytes32+constant (PR1), keccak256("MINTER_ROLE") fold (PR2), a bool-valued
// role map (PR3), the RoleData struct-of-mappings flatten (PR4), the parameterized
// onlyRole(getRoleAdmin(role)) modifier (W1), _msgSender() in a discarded emit (W3),
// _grantRole's bool tail-returns dropped at a statement call (W4), and supportsInterface's
// ERC165 introspection dropped (W2). The authority story is faithful: mint traps unless
// the caller holds MINTER_ROLE; grantRole traps unless the caller holds the role's admin.
// This is the OZ AccessControlERC20MintBase shape; the real unmodified OZ file (with its
// full closure) also translates AND compiles via --project-root (49KB wasm, 66 AIR fns).
pragma solidity ^0.8.20;

interface IAccessControl {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

contract AccessControlMintToken is IAccessControl {
    struct RoleData {
        mapping(address => bool) hasRole;
        bytes32 adminRole;
    }

    mapping(bytes32 => RoleData) private _roles;
    mapping(address => uint256) private _balances;
    uint256 private _totalSupply;

    bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;
    bytes32 public constant MINTER_ROLE = keccak256("MINTER_ROLE");

    event RoleGranted(bytes32 indexed role, address indexed account, address indexed sender);

    error CallerNotMinter(address caller);

    function _msgSender() internal view returns (address) { return msg.sender; }

    function supportsInterface(bytes4 interfaceId) public view returns (bool) {
        return interfaceId == 0x7965db0b;
    }

    function hasRole(bytes32 role, address account) public view returns (bool) {
        return _roles[role].hasRole[account];
    }

    function getRoleAdmin(bytes32 role) public view returns (bytes32) {
        return _roles[role].adminRole;
    }

    modifier onlyRole(bytes32 role) {
        require(_roles[role].hasRole[_msgSender()]);
        _;
    }

    function _grantRole(bytes32 role, address account) internal returns (bool) {
        if (!hasRole(role, account)) {
            _roles[role].hasRole[account] = true;
            emit RoleGranted(role, account, _msgSender());
            return true;
        } else {
            return false;
        }
    }

    function grantRole(bytes32 role, address account) public onlyRole(getRoleAdmin(role)) {
        _grantRole(role, account);
    }

    function mint(address to, uint256 amount) public {
        if (!hasRole(MINTER_ROLE, _msgSender())) {
            revert CallerNotMinter(_msgSender());
        }
        _balances[to] += amount;
    }

    constructor(address admin, address minter) {
        _grantRole(DEFAULT_ADMIN_ROLE, admin);
        _grantRole(MINTER_ROLE, minter);
    }
}
