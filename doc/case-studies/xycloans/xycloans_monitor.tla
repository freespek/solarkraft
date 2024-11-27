-------------------------- MODULE xycloans_monitor --------------------------
(*
 * A monitor for the XY Loans contract to detect the known issue.
 *
 * This is a manual translation of the Typescript monitor from
 * verify_js_examples_xycloans.ts. Our goal is to produce a simple and readable
 * TLA+ specification that is used to monitor existing transactions and
 * generate new transactions, e.g., from the current state.
 *
 * After receiving feedback from the users, we would think about automation.
 *
 * Igor Konnov, 2024
 *)

EXTENDS Integers, xycloans_types

STROOP == 10000000

CONSTANT
    \* The token address for the XY Loans contract.
    \* @type: Str;
    XLM_TOKEN_SAC_TESTNET

(* The internal state of our monitor (not of the contract) *)
VARIABLES
    \* The last monitored transaction.
    \* @type: $tx;
    last_tx,
    \* Shares per address.
    \* @type: Str -> Int;
    shares,
    \* The sum over all shares.
    \* @type: Int;
    total_shares,
    \* Fee per share for the entire pool, in stroops.
    \* @type: Int;
    fee_per_share_universal

(* The core logic of the monitor for the contract data *)

\* @type: ($tx, Bool) => Bool;
reverts_with(tx, cond) == ~tx.status => cond
\* @type: ($tx, Bool) => Bool;
succeeds_with(tx, cond) == tx.status => cond
\* @type: (Str -> a, Str, a) => a;
get_or_else(map, key, default) ==
    IF key \in DOMAIN map THEN map[key] ELSE default
\* integer division with rounding up
div_ceil(a, b) == a + (b - 1) \div b
\* integer division with rounding down
div_floor(a, b) == a \div b
\* @type: ($env, Str) => Int;
token_balance(env, a) == get_or_else(env.storage.token_persistent.Balance, a, 0)
\* @type: ($env, Str) => Int;
old_token_balance(env, a) == get_or_else(env.old_storage.token_persistent.Balance, a, 0)

\* @type: $tx => Bool;
initialize(tx) ==
    LET call == AsInitialize(tx.call) IN
    /\ IsInitialize(tx.call)
    /\ reverts_with(tx, tx.env.old_storage.self_instance.TokenId /= "")
    /\ succeeds_with(tx, call.token = XLM_TOKEN_SAC_TESTNET)
    /\ succeeds_with(tx, tx.env.storage.self_instance.TokenId = call.token)
    \* these conditions are not required by a monitor, but needed to avoid spurious generated values
    /\ succeeds_with(tx,
        tx.env.storage.self_instance.FeePerShareUniversal = tx.env.old_storage.self_instance.FeePerShareUniversal)
    /\ last_tx' = tx
    /\ shares' = [ addr \in {} |-> 0 ]
    /\ total_shares' = 0
    /\ fee_per_share_universal' = 0    

\* @type: $tx => Bool;
deposit(tx) ==
    LET call == AsDeposit(tx.call)
        token == tx.env.storage.self_instance.TokenId
        new_shares == [ shares EXCEPT ![call.from] = @ + call.amount ]
    IN
    /\ IsDeposit(tx.call)
    \* the pool has received `amount` tokens
    /\  LET a == tx.env.current_contract_address IN
        succeeds_with(tx, token_balance(tx.env, a) = old_token_balance(tx.env, a) + call.amount)
    \* `from` received `amount` shares
    /\  LET b == get_or_else(tx.env.storage.self_persistent.Balance, call.from, 0)
            old_b == get_or_else(tx.env.old_storage.self_persistent.Balance, call.from, 0)
        IN
        /\ succeeds_with(tx, new_shares[call.from] = b)
        /\ succeeds_with(tx, b = old_b + call.amount)
    \* update the monitor state
    /\ last_tx' = tx
    /\ shares' = new_shares
    /\ total_shares' = total_shares + call.amount
    /\ UNCHANGED fee_per_share_universal

\* @type: $tx => Bool;
borrow(tx) ==
    LET call == AsBorrow(tx.call)
        expected_fee == div_ceil(call.amount * STROOP, 12500000000)
        expected_fee_per_share_universal ==
            tx.env.old_storage.self_instance.FeePerShareUniversal
                + div_floor(expected_fee * STROOP, total_shares)
    IN
    /\ IsBorrow(tx.call)
    \* `FeePerShareUniversal` has been updated correctly
    /\ succeeds_with(tx,
           expected_fee_per_share_universal = tx.env.storage.self_instance.FeePerShareUniversal)
    \* the receiver paid the expected fee to the pool
    /\ succeeds_with(tx, old_token_balance(tx.env, call.receiver_id) >= call.amount)
    /\ LET a == call.receiver_id IN
       succeeds_with(tx, token_balance(tx.env, a) = old_token_balance(tx.env, a) - call.amount)
    /\ LET a == tx.env.current_contract_address IN
       succeeds_with(tx, token_balance(tx.env, a) = old_token_balance(tx.env, a) + call.amount)
    \* update the monitor state
    /\ last_tx' = tx
    \* we update the fee per share to compute rewards later
    /\ fee_per_share_universal' = expected_fee_per_share_universal
    /\ UNCHANGED <<shares, total_shares>>

\* @type: $tx => Bool;
update_fee_rewards(tx) ==
    LET call == AsUpdateFeeRewards(tx.call)
        fees_not_yet_considered ==
            fee_per_share_universal - get_or_else(tx.env.old_storage.self_persistent.FeePerShareParticular, call.addr, 0)
        expected_reward == div_floor(get_or_else(shares, call.addr, 0) * fees_not_yet_considered, STROOP)
        mf == get_or_else(tx.env.storage.self_persistent.MaturedFeesParticular, call.addr, 0)
        old_mf == get_or_else(tx.env.old_storage.self_persistent.MaturedFeesParticular, call.addr, 0)
        actual_reward == mf - old_mf
    IN
    /\ IsUpdateFeeRewards(tx.call)
    \* fee per share for `addr` is bumped to the universal fee per share
    /\  LET fee == get_or_else(tx.env.storage.self_persistent.FeePerShareParticular, call.addr, 0) IN
        succeeds_with(tx, fee = fee_per_share_universal)
    \* delta of matured rewards for `addr` have been added
    /\ expected_reward = actual_reward
    \* update the monitor state
    /\ last_tx' = tx
    /\ UNCHANGED <<shares, total_shares, fee_per_share_universal>>

=============================================================================