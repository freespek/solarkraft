---------------------- MODULE xycloans_monitor_simpler -------------------------
(*
 * A simpler monitor for the xycLoans contract to detect the known issue.
 * We have understood that input generation for a single step allows us
 * to keep the monitor simple, in comparison to multiple steps.
 *
 * Igor Konnov, 2024
 *)

EXTENDS Integers, defs, xycloans_types

STROOP == 10000000

CONSTANT
    \* The token address for the xycLoans contract.
    \* @type: Str;
    XLM_TOKEN_SAC_TESTNET

\* @type: $tx => Bool;
initialize(tx) ==
    LET call == AsInitialize(tx.call) IN
    /\ IsInitialize(tx.call)
    /\ reverts_if(tx, tx.env.old_storage.self_instance.TokenId /= "")
    /\ succeeds_with(tx, tx.env.storage.self_instance.TokenId = XLM_TOKEN_SAC_TESTNET)

\* @type: $tx => Bool;
deposit(tx) ==
    LET call == AsDeposit(tx.call)
        token == tx.env.old_storage.self_instance.TokenId
    IN
    /\ IsDeposit(tx.call)
    \* the pool has received `amount` tokens
    /\  LET self == tx.env.current_contract_address IN
        /\ succeeds_with(tx, token_balance(tx.env, self) = old_token_balance(tx.env, self) + call.amount)
        \* the balance of the sender is increased by the amount
        /\ succeeds_with(tx,
            tx.env.storage.self_persistent.Balance =
                [ tx.env.old_storage.self_persistent.Balance EXCEPT ![call.from] = @ + call.amount ])

\* @type: $tx => Bool;
borrow(tx) ==
    \* note that we do not compute the fees here, as it may require good understanding of the protocol
    LET call == AsBorrow(tx.call)
        token == tx.env.old_storage.self_instance.TokenId
    IN
    /\ IsBorrow(tx.call)
    \* the receiver paid the expected fee to the pool
    /\ LET rcvr == call.receiver_id
           self == tx.env.current_contract_address IN
       /\ succeeds_with(tx, old_token_balance(tx.env, call.receiver_id) >= call.amount)
       /\ succeeds_with(tx, token_balance(tx.env, rcvr) = old_token_balance(tx.env, rcvr) - call.amount)
       /\ succeeds_with(tx, token_balance(tx.env, self) = old_token_balance(tx.env, self) + call.amount)
    /\ succeeds_with(tx, call.amount > 0)
    /\ succeeds_with(tx, tx.env.storage.self_instance.TokenId = token)

\* @type: $tx => Bool;
update_fee_rewards(tx) ==
    \* note that we do not compute the fees here, as it may require good understanding of the protocol
    LET call == AsUpdateFeeRewards(tx.call)
        token == tx.env.old_storage.self_instance.TokenId
    IN
    /\ IsUpdateFeeRewards(tx.call)
    /\ succeeds_with(tx, tx.env.storage.self_instance.TokenId = token)
    /\ succeeds_with(tx, tx.env.storage.token_persistent = tx.env.old_storage.token_persistent)

\* @type: $tx => Bool;
withdraw_matured(tx) ==
    \* note that we do not compute the fees here, as it may require good understanding of the protocol
    LET call == AsWithdrawMatured(tx.call)
        token == tx.env.old_storage.self_instance.TokenId
    IN
    /\ IsWithdrawMatured(tx.call)
    /\ succeeds_with(tx, tx.env.storage.self_instance.TokenId = token)
    \* otherwise, the contract reverts
    /\ succeeds_with(tx, tx.env.old_storage.self_persistent.MaturedFeesParticular[call.addr] > 0)
    \* the pool gets smaller
    /\  LET self == tx.env.current_contract_address IN
        \E amount \in Nat:
            \* we do not want into a precise computation, but only specify the conditions
            /\ (amount > 0) <=> (tx.env.old_storage.self_persistent.MaturedFeesParticular[call.addr] > 0)
            /\ succeeds_with(tx, token_balance(tx.env, self) = old_token_balance(tx.env, self) - amount)

\* @type: $tx => Bool;
withdraw(tx) ==
    \* note that we do not compute the fees here, as it may require good understanding of the protocol
    LET call == AsWithdraw(tx.call)
        token == tx.env.old_storage.self_instance.TokenId
    IN
    /\ IsWithdraw(tx.call)
    /\ succeeds_with(tx, tx.env.storage.self_instance.TokenId = token)
    \* the pool gets smaller by the amount
    /\  LET self == tx.env.current_contract_address IN
        /\ succeeds_with(tx, old_token_balance(tx.env, self) - call.amount >= 0)
        /\ succeeds_with(tx,
            token_balance(tx.env, self) = old_token_balance(tx.env, self) - call.amount)

=============================================================================