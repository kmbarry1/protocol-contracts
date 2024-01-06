methods {
    function allowance(address, address) external returns (uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
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
