// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.9;

import "../@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import "../@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract LockToken {
    using SafeERC20 for IERC20;

    event Deposited(address owner, address token, uint256 amount, uint unlockTime);
    event Withdrawal(address owner, address token, uint amount, uint when);
    struct Staked {
        address payable token;
        uint256 balance;
        uint256 fee;
        uint unlockTime;
    }

    mapping(address => Staked) holders;
    uint256 _fee = 0;
    address _owner;

    constructor () {
        _owner = msg.sender;
    }

    function setFee(uint256 fee) external {
        require(_owner == msg.sender, 'Not authorized!');
        _fee = fee;
    }

    function getFee() public view returns (uint256 fee) {
        return _fee;
    }

    function deposit(address owner, address token, uint256 amount, uint unlockTime) external {
        require(
            block.timestamp < unlockTime,
            "Unlock time should be in the future"
        );
        require(amount >= _fee + 1, 'You have to supply a balance greater than the fee.');
        require(IERC20(payable(token)).balanceOf(msg.sender) >= amount, 'You have to have a balance greater than your deposit');
        require(IERC20(payable(token)).allowance(msg.sender, address(this)) >= amount, "You must give the contract an allowance");
        IERC20(payable(token)).safeTransferFrom(msg.sender, address(this), amount);
        holders[msg.sender].token = payable(token);
        holders[msg.sender].balance = amount;
        holders[msg.sender].fee = _fee;
        holders[msg.sender].unlockTime = unlockTime;
        emit Deposited(owner, token, amount, unlockTime);

    }

    function withdraw() public {
        require(block.timestamp >= holders[msg.sender].unlockTime, "You can't withdraw yet");
        require(holders[msg.sender].balance >= 0, "You have no balance");
        IERC20(holders[msg.sender].token).transferFrom(address(this), msg.sender, holders[msg.sender].balance - _fee);
        IERC20(holders[msg.sender].token).transferFrom(address(this), _owner, _fee);
        delete holders[msg.sender];
        emit Withdrawal(msg.sender, holders[msg.sender].token, address(this).balance - _fee, block.timestamp);
    }
}