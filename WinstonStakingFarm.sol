
// File: @openzeppelin/contracts/utils/Counters.sol


// OpenZeppelin Contracts v4.4.1 (utils/Counters.sol)

pragma solidity ^0.8.0;

/**
 * @title Counters
 * @author Matt Condon (@shrugs)
 * @dev Provides counters that can only be incremented, decremented or reset. This can be used e.g. to track the number
 * of elements in a mapping, issuing ERC721 ids, or counting request ids.
 *
 * Include with `using Counters for Counters.Counter;`
 */
library Counters {
    struct Counter {
        // This variable should never be directly accessed by users of the library: interactions must be restricted to
        // the library's function. As of Solidity v0.5.2, this cannot be enforced, though there is a proposal to add
        // this feature: see https://github.com/ethereum/solidity/issues/4637
        uint256 _value; // default: 0
    }

    function current(Counter storage counter) internal view returns (uint256) {
        return counter._value;
    }

    function increment(Counter storage counter) internal {
        unchecked {
            counter._value += 1;
        }
    }

    function decrement(Counter storage counter) internal {
        uint256 value = counter._value;
        require(value > 0, "Counter: decrement overflow");
        unchecked {
            counter._value = value - 1;
        }
    }

    function reset(Counter storage counter) internal {
        counter._value = 0;
    }
}

// File: @openzeppelin/contracts/utils/Context.sol


// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

// File: @openzeppelin/contracts/utils/Address.sol


// OpenZeppelin Contracts (last updated v4.5.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: @openzeppelin/contracts/token/ERC20/IERC20.sol


// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// File: @openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol


// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)

pragma solidity ^0.8.0;


/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

// File: @openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol


// OpenZeppelin Contracts v4.4.1 (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.0;



/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// File: Staking.sol


pragma solidity ^0.8.0;
pragma experimental ABIEncoderV2;





/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}


// SPDX-License-Identifier: MIT
/**
 * @title WinstonStakingFarm
 * @dev This contract handles the staking of ERC20 tokens. Custody of multiple tokens can be
 * given to this contract, which will release donated rewards based on staked holdings.
 */
contract WinstonStakingFarm is Context, ReentrancyGuard {
    using SafeERC20 for IERC20Metadata;
    using SafeERC20 for IERC20;
    using Counters for Counters.Counter;
    event TransferOwnership(address newowner, address oldowner);
    event TokensDeposited(address token, uint256 amount);
    event TokensWithdrawn(address token, uint256 amount);
    event TokensStaked(address user, address token, uint256 amount);
    event TokensCollected(address user, address token, uint256 amount);
    event AddressBlacklisted(address _address);
    event RemovedBlacklistedAddress(address _address);
    event Withdraw(uint256 farm, uint256 amount);
    event EmergencyWithdraw(uint256 amount);
    event EmergencyTokenWithdraw(address token, uint256 amount);
    struct UserAssets {
        address user; // Owner of the assets
        address token; // Asset 
        uint256 amount; // Amount of the asset
        uint256 vested; // Timestamp when Vested
        uint256 staked; // Timestamp when Staked
        uint256 collected; // Total Collected
        uint256 lastCollected; // Total Collected
    }

    struct AssetSettings {
        uint256 id;
        address stakeable;
        address rewardToken;
        address feeWallet;
        uint256 minVestingPeriod;
        uint256 maxStakeAmount;
        uint256 totalDeposited;
        uint256 balance;
        uint256 totalRewarded;
        uint256 fee;
        uint256 start;
        uint256 duration;
    }

    /* [User -> Token -> Amount] Rewards Collected */
    mapping (address => mapping (address => UserAssets)) private _assets;
    mapping (uint256 => AssetSettings) private _assetFarms;
    mapping (address => bool) private _blacklisted;
    
    address private _owner;
    /* Array of Holders */
    address[] private _holders;
    /* Array of Reward Tokens */
    address[] private _rewardTokens;
    /* [Token -> Bool] Token Blacklist */
    Counters.Counter private _assetId;

    constructor() {
        _owner = _msgSender();
        emit TransferOwnership(_msgSender(), address(0));
    }

   function setupAssetFarm(
       AssetSettings memory winstonFarm,
       bool _isUpdate
       ) public onlyOwner() {
           
       uint256 _id = winstonFarm.id; 
       address _stakeable = winstonFarm.stakeable; 
       address _rewardToken = winstonFarm.rewardToken; 
       address _feeWallet = winstonFarm.feeWallet; 
       uint256 _minVestingPeriod = winstonFarm.minVestingPeriod; 
       uint256 _maxStakeAmount = winstonFarm.maxStakeAmount; 
       uint256 _totalDeposited = winstonFarm.totalDeposited; 
       uint256 _balance = winstonFarm.balance; 
       uint256 _totalRewarded = winstonFarm.totalRewarded; 
       uint256 _fee = winstonFarm.fee; 
       uint256 _start = winstonFarm.start; 
       uint256 _duration = winstonFarm.duration; 
        require(_isUpdate && _id >= _assetId.current(), 'Invalid Asset Id');
        if (!_isUpdate) {
            require(rewardTokenExists(_rewardToken), 'Farm Exists Already');
            _rewardTokens.push(_rewardToken);
            uint256 id = _assetId.current();//asset id
            _assetId.increment();
            _assetFarms[id] = AssetSettings(
                id, 
                _stakeable, 
                _rewardToken, 
                _feeWallet, 
                _minVestingPeriod, 
                _maxStakeAmount, 
                _totalDeposited,
                _balance,
                _totalRewarded,
                _fee, 
                _start,  
                _duration
            );
        } else {
            _assetFarms[_id] = AssetSettings(
                _id, 
                _stakeable, 
                _rewardToken, 
                _feeWallet, 
                _minVestingPeriod, 
                _maxStakeAmount, 
                _totalDeposited,
                _balance,
                _totalRewarded,
                _fee, 
                _start,  
                _duration
            );
        }
   }

    function rewardTokenExists(address _rewardToken) public view returns (bool) {
        for (uint i = 0; i < _rewardTokens.length; i++) {
            if (_rewardTokens[i] == _rewardToken) {
                return true;
            }
        }
        return false;
    }

   function getAssetFarm(uint256 id) public view returns (AssetSettings memory) {
      return _assetFarms[id];
   }

    modifier onlyOwner() {
        require(owner() == _msgSender(), "WinstonStakingFarm: access restricted to owner");
        _;
    }
        
    /**
     * @dev Getter for the beneficiary address.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev transfer ownership of the contract.
     */
    function transferOwner(address newowner) public virtual onlyOwner() {
       _owner = newowner;
       emit TransferOwnership(newowner, _msgSender());
    }
    
    /**
     * @dev Getter for a token reward balance.
     */
    function rewardAssetBalance(address token) public view virtual returns (uint256 balance) {
        for(uint256 i = 0; i < _assetId.current(); i++) {
            if(_assetFarms[i].rewardToken == token)
                return _assetFarms[i].balance;
        }
    }

    /**
     * @dev Getter for a token reward.
     */
    function getRewardAssets(address token) public view virtual returns (AssetSettings memory rewardAsset) {
        for(uint256 i = 0; i < _assetId.current(); i++) {
            if(_assetFarms[i].rewardToken == token)
                return _assetFarms[i];
        }
    }

    /**
     * @dev Getter for a token reward.
     */
    function getStakeableAssets(address token) public view virtual returns (AssetSettings memory stakeableAsset) {
        for(uint256 i = 0; i < _assetId.current(); i++) {
            if(_assetFarms[i].stakeable == token)
                return _assetFarms[i];
        }
    }

    function calculateFee(address _token, uint256 _amount, uint256 _fee) public view virtual returns (uint256 payout, uint256 fee) {
        uint256 adjustedfee = (_amount * _fee) * 10 ** IERC20Metadata(address(_token)).decimals();
        require(_amount - adjustedfee > 0, 'Payout amount to low');
        return (_amount - adjustedfee, adjustedfee);
    }

    /**
     * @dev donate Rewards funds
     */
    function donate(address token, uint256 amount) payable public {
        require(!_blacklisted[token], 'Token is Blacklisted.');
        require(amount >= 0, 'Amount too low.');
        require(rewardTokenExists(token), 'Farm Not Created.');
        AssetSettings memory asset = getRewardAssets(token);
        (uint256 _amount, uint256 _fee) = calculateFee(token, amount, asset.fee);
        asset.balance += _amount;
        asset.totalDeposited += _amount;
        IERC20(token).safeTransferFrom(_msgSender(), address(this), _amount);
        IERC20(token).safeTransferFrom(_msgSender(), address(asset.feeWallet), _fee);
        emit TokensDeposited(token, amount);
    }

    /**
     * @dev Blacklist an address.
     */
    function blacklistAddress(address _address) public onlyOwner() {
       _blacklisted[_address] = true;
       emit AddressBlacklisted(_address);
   }

    /**
     * @dev Remove Blacklisted address.
     */
    function removeBlacklistedAddress(address _address) public onlyOwner() {
       _blacklisted[_address] = false;
        emit RemovedBlacklistedAddress(_address);
    }
    
    /**
     * @dev Check Blacklisted address.
     */
    function isBlacklisted(address _address) public virtual returns (bool) {
       return _blacklisted[_address];
    }

    /**
    * @dev Release the tokens that have already vested.
    */
    function collectRewards(address token) public  {
        require(isBlacklisted(_msgSender()), 'User is Blacklisted.');
        require(isBlacklisted(token), 'Token is Blacklisted.');
        AssetSettings memory asset = getRewardAssets(token);
        require(asset.stakeable == token, 'Farm MisMatch Error');
        require(block.timestamp >= asset.start, "Not Started");
        require(block.timestamp < asset.start + asset.duration, "Period Ended");
        require(asset.balance >= 0, "No reward balance to payout.");
        UserAssets memory userAsset = _assets[_msgSender()][token];
        require(userAsset.amount >= 0, "Zero Staked Balance");
        require(block.timestamp >= userAsset.staked + asset.minVestingPeriod, "Vesting Period not met.");
        require(block.timestamp >= userAsset.lastCollected + 86400000, 'Already Collected Today');
        uint256 payout = ((asset.balance / 365) * (block.timestamp - (userAsset.staked + asset.minVestingPeriod))) / asset.duration;
        (uint256 releasable, uint256 fee) = calculateFee(token, payout, asset.fee);
        asset.balance -= payout;
        asset.totalRewarded += payout;
        userAsset.collected += releasable;
        userAsset.lastCollected = block.timestamp;
        emit TokensCollected(_msgSender(), token, payout);
        SafeERC20.safeTransfer(IERC20(token), asset.feeWallet, fee);
        SafeERC20.safeTransfer(IERC20(token), _msgSender(), releasable);
        // require(block.timestamp >= asset.start + asset.minVestingPeriod, "Not Vested");
    }

    /**
     * @dev Calculates the amount that has already vested. Default implementation is a linear vesting curve.
     */
    function calculateRewards(address token) public virtual view returns (uint256) {
        AssetSettings memory asset = getRewardAssets(token);
        require(block.timestamp >= asset.start, "Not Started");
        require(block.timestamp < asset.start + asset.duration, "Period Ended");
        require(asset.balance >= 0, "No reward balance to payout.");
        UserAssets memory userAsset = _assets[_msgSender()][token];
        require(userAsset.amount >= 0, "Zero Staked Balance");
        require(block.timestamp >= userAsset.staked + asset.minVestingPeriod, "Vesting Period not met.");
        require(block.timestamp >= userAsset.lastCollected + 86400000, 'Already Collected Today');
        uint256 payout = ((asset.balance / 365) * (block.timestamp - (userAsset.staked + asset.minVestingPeriod))) / asset.duration;
        (uint256 releasable, ) = calculateFee(token, payout, asset.fee);
        return (releasable);
    }

    function stake(uint256 farm, uint256 amountToStake) public nonReentrant {
        require(isBlacklisted(_msgSender()), 'User is Blacklisted.');
        AssetSettings memory currentfarm = _assetFarms[farm];
        require(isBlacklisted(currentfarm.stakeable), 'Token is Blacklisted.');
        require(rewardTokenExists(currentfarm.rewardToken), 'Farm Does not Exist');
        _assets[_msgSender()][currentfarm.stakeable].amount += amountToStake;
        IERC20(currentfarm.stakeable).safeTransferFrom(_msgSender(), address(this), amountToStake);
    }

    function withdraw(uint256 farm, uint256 amount) public nonReentrant {
        require(isBlacklisted(_msgSender()), 'User is Blacklisted.');
        AssetSettings memory withdrawfarm = _assetFarms[farm];
        require(isBlacklisted(withdrawfarm.stakeable), 'Token is Blacklisted.');
        UserAssets memory userAsset = _assets[_msgSender()][withdrawfarm.stakeable];
        require(userAsset.amount >= amount, 'Insufficient balance');
        collectRewards(withdrawfarm.stakeable);
        userAsset.amount -= amount;
        IERC20(withdrawfarm.stakeable).safeTransferFrom(address(this), _msgSender(), userAsset.amount);

    }

    receive() external payable {}

    function adminEmergencyWithdraw(uint256 amount) public onlyOwner() nonReentrant {
        (bool success, ) = payable(address(this)).call{value: amount}("");
        require(success);
    }

    function adminEmergencyTokenWithdraw(address token, uint256 amount) public onlyOwner() nonReentrant {
        IERC20(token).safeTransferFrom(address(this), _msgSender(), amount);
        emit EmergencyTokenWithdraw(token, amount);
    }
}
