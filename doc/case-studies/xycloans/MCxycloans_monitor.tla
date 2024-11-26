------------------------------- MODULE MCxycloans_monitor -------------------------------
(*
 * An instance of xycloans monitor for model checking and input generation.
 *
 * Igor Konnov, 2024
 *)
EXTENDS Integers, xycloans_types

\* the set of all possible token amounts
AMOUNTS == Nat
\* the contract address for the XY Loans contract
XYCLOANS == "xycloans"
\* the token address
XLM_TOKEN_SAC_TESTNET == "xlm-sac"

\* the pool of addresses to draw the values from
ADDR == { "alice", "bob", "eve", XLM_TOKEN_SAC_TESTNET, XYCLOANS }

VARIABLES
    \* @type: $tx;
    last_tx,
    \* @type: Str -> Int;
    shares,
    \* @type: Int;
    total_shares,
    \* @type: Int;
    fee_per_share_universal

INSTANCE xycloans_monitor

Init ==
    /\ last_tx = [
            call |-> Create("any"),
            status |-> TRUE,
            env |-> [
                current_contract_address |-> "any",
                storage |-> [
                    self_instance |-> [
                        FeePerShareUniversal |-> 0,
                        TokenId |-> ""
                    ],
                    self_persistent |-> [
                        Balance |-> [ addr \in {} |-> 0 ],
                        MaturedFeesParticular |-> [ addr \in {} |-> 0 ],
                        FeePerShareParticular |-> [ addr \in {} |-> 0 ]
                    ],
                    token_persistent |-> [ Balance |-> [ addr \in {} |-> 0 ] ]
                ],
                old_storage |-> [
                    self_instance |-> [
                        FeePerShareUniversal |-> 0,
                        TokenId |-> ""
                    ],
                    self_persistent |-> [
                        Balance |-> [ addr \in {} |-> 0 ],
                        MaturedFeesParticular |-> [ addr \in {} |-> 0 ],
                        FeePerShareParticular |-> [ addr \in {} |-> 0 ]
                    ],
                    token_persistent |-> [ Balance |-> [ addr \in {} |-> 0 ] ]
                ]
            ]
        ]
    /\ shares = [ addr \in {} |-> 0 ]
    /\ total_shares = 0
    /\ fee_per_share_universal = 0

Next ==
    \* generate some values for the storage
    \E fpsu \in AMOUNTS, tid \in { "", XLM_TOKEN_SAC_TESTNET }:
      \E b, mfp, fpsp, tb \in [ ADDR -> AMOUNTS ]:
        LET storage == [
                self_instance |-> [ FeePerShareUniversal |-> fpsu, TokenId |-> tid ],
                self_persistent |-> [ Balance |-> b, MaturedFeesParticular |-> mfp, FeePerShareParticular |-> fpsp ],
                token_persistent |-> [ Balance |-> tb ]
            ]
            env == [
                current_contract_address |-> XYCLOANS,
                storage |-> storage,
                old_storage |-> last_tx.env.storage
            ]
        IN
        \E method \in { "initialize", "deposit", "borrow", "update_fee_rewards" }:
            \E addr \in ADDR, amount \in AMOUNTS, success \in BOOLEAN:
                LET call ==
                    CASE method = "initialize" -> Initialize(XLM_TOKEN_SAC_TESTNET)
                      [] method = "deposit" -> Deposit(addr, amount)
                      [] method = "borrow" -> Borrow(addr, amount)
                      [] method = "update_fee_rewards" -> UpdateFeeRewards(addr)
                IN
                LET tx == [ env |-> env, call |-> call, status |-> success ] IN
                \/ initialize(tx)
                \/ deposit(tx)
                \/ borrow(tx)
                \/ update_fee_rewards(tx)

=========================================================================================