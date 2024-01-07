using GasZRC20 as gasToken;

methods {
    function allowance(address, address) external returns (uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function _.transferFrom(address, address, uint256) external => DISPATCHER(true);
    function _.gasCoinZRC20ByChainId(uint256) external => CONSTANT;
    function _.gasPriceByChainId(uint256) external => CONSTANT;
}

ghost balanceSum() returns mathint {
    init_state axiom balanceSum() == 0;
}

hook Sstore _balances[KEY address a] uint256 balance (uint256 old_balance) STORAGE {
    havoc balanceSum assuming balanceSum@new() == balanceSum@old() + balance - old_balance;
}

invariant balanceSum_equals_totalSupply()
    balanceSum() == to_mathint(totalSupply());

rule storageAffected(method f) {
    env e;

    mathint totalSupplyBefore = totalSupply();

    calldataarg args;
    f(e, args);

    mathint totalSupplyAfter = totalSupply();

    assert totalSupplyAfter != totalSupplyBefore
        => f.selector == sig:burn(uint256).selector ||
           f.selector == sig:deposit(address, uint256).selector ||
           f.selector == sig:withdraw(bytes memory, uint256).selector;
}

rule transfer(address recipient, uint256 amount) {
    env e;

    mathint balSenderBefore = balanceOf(e.msg.sender);
    mathint balRecipientBefore = balanceOf(recipient);
    bool senderIsRecipient = e.msg.sender == recipient;

    transfer(e, recipient, amount);

    mathint balSenderAfter = balanceOf(e.msg.sender);
    mathint balRecipientAfter = balanceOf(recipient);

    assert !senderIsRecipient => balSenderAfter == balSenderBefore - amount, "sender balance not updated correctly";
    assert !senderIsRecipient => balRecipientAfter == balRecipientBefore + amount, "recipient balance not updated correctly";
    assert senderIsRecipient => balSenderBefore == balSenderAfter, "sender balance not unchanged";
}

rule transfer_revert(address recipient, uint256 amount) {
    env e;

    mathint balSenderBefore = balanceOf(e.msg.sender);
    mathint balRecipientBefore = balanceOf(recipient);

    transfer@withrevert(e, recipient, amount);

    bool revert1 = e.msg.value > 0;
    bool revert2 = e.msg.sender == 0;
    bool revert3 = recipient == 0;
    bool revert4 = balSenderBefore < to_mathint(amount);
    bool revert5 = e.msg.sender != recipient && balRecipientBefore + amount > max_uint256;

    assert lastReverted <=> revert1 || revert2 || revert3 || revert4 || revert5,
                            "revert conditions violated or incomplete";
}

rule transferFrom(address sender, address recipient, uint256 amount) {
    env e;

    mathint balSenderBefore = balanceOf(sender);
    mathint balRecipientBefore = balanceOf(recipient);
    mathint allowanceBefore = allowance(sender, e.msg.sender);
    bool senderIsRecipient = sender == recipient;

    transferFrom(e, sender, recipient, amount);

    mathint balSenderAfter = balanceOf(sender);
    mathint balRecipientAfter = balanceOf(recipient);
    mathint allowanceAfter = allowance(sender, e.msg.sender);

    assert !senderIsRecipient => balSenderAfter == balSenderBefore - amount, "sender balance not updated correctly";
    assert !senderIsRecipient => balRecipientAfter == balRecipientBefore + amount, "recipient balance not updated correctly";
    assert senderIsRecipient => balSenderBefore == balSenderAfter, "sender balance not unchanged";
    assert allowanceAfter == allowanceBefore - amount, "allowance not updated as expected";
}

rule transferFrom_revert(address sender, address recipient, uint256 amount) {
    env e;

    mathint balSenderBefore = balanceOf(sender);
    mathint balRecipientBefore = balanceOf(recipient);
    mathint allowanceBefore = allowance(sender, e.msg.sender);

    transferFrom@withrevert(e, sender, recipient, amount);

    bool revert1 = e.msg.value > 0;
    bool revert2 = sender == 0;
    bool revert3 = recipient == 0;
    bool revert4 = balSenderBefore < to_mathint(amount);
    bool revert5 = sender != recipient && balRecipientBefore + amount > max_uint256;
    bool revert6 = allowanceBefore < to_mathint(amount);
    bool revert7 = e.msg.sender == 0;

    assert lastReverted <=> revert1 || revert2 || revert3 || revert4 || revert5 || revert6 || revert7,
                            "revert conditions violated or incomplete";
}

rule approve(address spender, uint256 value) {
    env e;
    approve(e, spender, value);
    assert allowance(e.msg.sender, spender) == value, "approve did not set allowance as expected";
}

rule approve_revert(address spender, uint256 value) {
    env e;
    approve@withrevert(e, spender, value);
    bool revert1 = e.msg.value > 0;
    assert lastReverted <=> revert1, "revert conditions violated or incomplete";
}
