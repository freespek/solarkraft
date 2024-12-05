------------------------------- MODULE MCxycloans_monitor -------------------------------
(*
 * An instance of xycloans monitor for model checking and input generation.
 *
 * Igor Konnov, 2024
 *)
EXTENDS Integers, xycloans_types

\* the set of all possible token amounts
AMOUNTS == Nat
\* the contract address for the xycLoans contract
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
    fee_per_share_universal,
    \* Keep track of the current storage,
    \* which can be only changed by a successful transaction.
    \* @type: $storage;
    storage

INSTANCE xycloans_monitor

Init ==
    LET init_stor == [
        self_instance |-> [
            FeePerShareUniversal |-> 0,
            TokenId |-> ""
        ],
        self_persistent |-> [
            Balance |-> [ addr \in ADDR |-> 0 ],
            MaturedFeesParticular |-> [ addr \in ADDR |-> 0 ],
            FeePerShareParticular |-> [ addr \in ADDR |-> 0 ]
        ],
        token_persistent |-> [ Balance |-> [ addr \in ADDR |-> 0 ] ]
    ]
    IN
    \* initialize the monitor
    /\ shares = [ addr \in {} |-> 0 ]
    /\ total_shares = 0
    /\ fee_per_share_universal = 0
    \* initialize the contract state that we model
    /\ last_tx = [
            call |-> Constructor(XYCLOANS),
            status |-> TRUE,
            env |-> [
                current_contract_address |-> XYCLOANS,
                storage |-> init_stor,
                old_storage |-> init_stor
            ]
        ]
    /\ storage = init_stor

Next ==
    \* Generate some values for the storage.
    \* For value generation, we go over all addresses, not subsets of addresses.
    \E fpsu \in AMOUNTS, tid \in { "", XLM_TOKEN_SAC_TESTNET }:
      \E b, mfp, fpsp, tb \in [ ADDR -> AMOUNTS ]:
        LET new_stor == [
                self_instance |-> [ FeePerShareUniversal |-> fpsu, TokenId |-> tid ],
                self_persistent |->
                    [ Balance |-> b, MaturedFeesParticular |-> mfp, FeePerShareParticular |-> fpsp ],
                token_persistent |-> [ Balance |-> tb ]
            ]
            env == [
                current_contract_address |-> XYCLOANS,
                storage |-> new_stor,
                old_storage |-> storage
            ]
        IN
        \E addr \in ADDR, amount \in AMOUNTS, success \in BOOLEAN:
            /\  \/ LET tx == [ env |-> env, call |-> Initialize(XLM_TOKEN_SAC_TESTNET), status |-> success ] IN
                   initialize(tx) /\ last_tx' = tx
                \/ LET tx == [ env |-> env, call |-> Deposit(addr, amount), status |-> success ] IN
                   deposit(tx) /\ last_tx' = tx
                \/ LET tx == [ env |-> env, call |-> Borrow(addr, amount), status |-> success ] IN
                   borrow(tx) /\ last_tx' = tx
                \/ LET tx == [ env |-> env, call |-> UpdateFeeRewards(addr), status |-> success ] IN
                   update_fee_rewards(tx) /\ last_tx' = tx
            /\ storage' = IF success THEN new_stor ELSE storage

\* restrict the executions to the successful transactions
NextOk ==
    Next /\ last_tx'.status

\* use this falsy invariant to generate examples of successful transactions
NoSuccessInv ==
    ~IsConstructor(last_tx.call) => ~last_tx.status

\* use this view to generate better test coverage
\* apalache-mc check --max-error=10 --length=10 --inv=NoSuccessInv --view=View MCxycloans_monitor.tla
View == <<last_tx.status, VariantTag(last_tx.call)>>
=========================================================================================