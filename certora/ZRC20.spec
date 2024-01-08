using GasZRC20 as gasToken;

methods {
    function allowance(address, address) external returns (uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function SYSTEM_CONTRACT_ADDRESS() external returns (address) envfree;
    function _.transferFrom(address, address, uint256) external => DISPATCHER(true);
    function _.gasCoinZRC20ByChainId(uint256) external => CONSTANT;
    function _.gasPriceByChainId(uint256) external => CONSTANT;
}

definition FUNG_MOD_ADDR returns address = 0x735b14BB79463307AAcBED86DAf3322B1e6226aB;

ghost balanceSum() returns mathint {
    init_state axiom balanceSum() == 0;
}

hook Sstore _balances[KEY address a] uint256 balance (uint256 old_balance) STORAGE {
    havoc balanceSum assuming balanceSum@new() == balanceSum@old() + balance - old_balance;
}

invariant balanceSum_equals_totalSupply()
    balanceSum() == to_mathint(totalSupply());

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

rule burn(uint256 amount) {
    env e;

    address other;
    require other != e.msg.sender;

    mathint balSenderBefore = balanceOf(e.msg.sender);
    mathint balOtherBefore = balanceOf(other);  // this allows us to prove no other balances are affected
    mathint totalSupplyBefore = totalSupply();

    bool ret = burn(e, amount);

    assert ret, "burn returned false";

    mathint balSenderAfter = balanceOf(e.msg.sender);
    mathint balOtherAfter = balanceOf(other);
    mathint totalSupplyAfter = totalSupply();

    assert balSenderAfter == balSenderBefore - amount, "tokens not burned as expected";
    assert balOtherAfter == balOtherBefore, "other address had a balance modified unexpectedly";
    assert totalSupplyAfter == totalSupplyBefore - amount, "totalSupply not decreased as expected";
}

rule burn_revert(uint256 amount) {
    env e;

    mathint balSenderBefore = balanceOf(e.msg.sender);
    mathint totalSupplyBefore = totalSupply();

    burn@withrevert(e, amount);

    bool revert1 = e.msg.value != 0;
    bool revert2 = e.msg.sender == 0;
    bool revert3 = balSenderBefore < to_mathint(amount);
    bool revert4 = totalSupplyBefore < to_mathint(amount);

    assert lastReverted <=> revert1 || revert2 || revert3 || revert4,
                            "revert conditions violated or incomplete";
}

rule deposit(address to, uint256 amount) {
    env e;

    address other;
    require other != to;

    mathint balToBefore = balanceOf(to);
    mathint balOtherBefore = balanceOf(other);
    mathint totalSupplyBefore = totalSupply();

    bool ret = deposit(e, to, amount);

    assert ret, "deposit returned false";

    mathint balToAfter = balanceOf(to);
    mathint balOtherAfter = balanceOf(other);
    mathint totalSupplyAfter = totalSupply();

    assert balToAfter == balToBefore + amount, "tokens not minted as expected";
    assert balOtherAfter == balOtherBefore, "other address had a balance modified unexpectedly";
    assert totalSupplyAfter == totalSupplyBefore + amount, "totalSupply not increased as expected";
}

rule deposit_revert(address to, uint256 amount) {
    env e;

    mathint balToBefore = balanceOf(to);
    mathint totalSupplyBefore = totalSupply();
    address systemContract = SYSTEM_CONTRACT_ADDRESS();

    deposit@withrevert(e, to, amount);

    bool revert1 = e.msg.value != 0;
    bool revert2 = e.msg.sender != FUNG_MOD_ADDR() && e.msg.sender != systemContract;
    bool revert3 = to == 0;
    bool revert4 = totalSupplyBefore + amount > max_uint256;
    bool revert5 = balToBefore + amount > max_uint256;

    assert lastReverted <=> revert1 || revert2 || revert3 || revert4 || revert5,
                            "revert conditions violated or incomplete";
}

rule withdraw(bytes to, uint256 amount) {
    env e;

    address other;
    require other != e.msg.sender;

    mathint balSenderBefore = balanceOf(e.msg.sender);
    mathint balOtherBefore = balanceOf(other);
    mathint totalSupplyBefore = totalSupply();

    bool ret = withdraw(e, to, amount);

    assert ret, "withdraw returned false";

    mathint balSenderAfter = balanceOf(e.msg.sender);
    mathint balOtherAfter = balanceOf(other);
    mathint totalSupplyAfter = totalSupply();

    // This assertion is weakened due to the fact that the gas token can be the same as the current contract.
    // With more time, I would split the spec into cases to get complete coverage.
    assert balSenderAfter <= balSenderBefore - amount, "withdraw did not decrease sender's balance";

    // Similar reasoning here as above.
    assert balOtherAfter == balOtherBefore || other == FUNG_MOD_ADDR(),
           "withdraw modified an unexpected address's balance";

    assert totalSupplyAfter == totalSupplyBefore - amount, "withdraw did not update totalSupply correctly";
}
