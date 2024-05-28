(*
 * Monitor specification for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE timelock_mon ----

EXTENDS timelock_mon_defs

\*************************
\* Deposit method monitors
\*************************

MustFail_deposit_TooManyClaimants == 
    Len(args.claimants) > 10

MustFail_deposit_Unauthorized == 
    ~authorized(args.from)

\* This property would not be originally conceived 
\* if looking solely at the timelock contract source
MustFail_deposit_NotEnoughBalance == 
    token_balance(args.token, args.from) < args.amount

\* Balance is externally relevant; Init flag is not
\* What matters for users is that balance is not overwritten
MustFail_deposit_AlreadyInitialized == 
    instance_has("Balance")

\* The above failure conditions exhaust the precondition of deposit method
\* The default success condition is not needed, but we may provide it
MustPass_deposit_Default == TRUE

MustHold_deposit_BalanceRecordCreated ==
    next_instance_has("Balance")

MustHold_deposit_BalanceRecordCorrect ==
    /\ Balance'.token = args.token
    /\ Balance'.amount = args.amount
    /\ Balance'.time_bound = args.time_bound
    /\ Balance'.claimants = args.claimants

MustHold_deposit_TokenTransferred ==
    token_transferred(
        args.token, args.from, env.current_contract_address, args.amount
    )

\***********************
\* Claim method monitors
\***********************

MustFail_claim_Unauthorized == 
    ~authorized(args.claimant)

MustFail_claim_NoBalanceRecord == 
    ~instance_has("Balance")

MustFail_claim_NotClaimant == 
    \A i \in 1..Len(Balance.claimants): 
        Balance.claimants[i] /= args.claimant

\* One success condition: correctly claimed before time bound
MustPass_claim_BeforeTimeBound ==
    /\ args.time_bound.kind = "Before" 
    /\ env.ledger_timestamp <= Balance.time_bound.timestamp

\* Another success condition: correctly claimed after time bound
MustPass_claim_AfterTimeBound ==
    /\ args.time_bound.kind = "After" 
    /\ env.ledger_timestamp >= Balance.time_bound.timestamp

MustHold_claim_TokenTransferred ==
    token_transferred(
        Balance.token, env.current_contract_address, args.claimant, Balance.amount)

MustHold_claim_BalanceRecordRemoved ==
    ~next_instance_has("Balance")


\*******************************
\* Balance record effect monitor
\*******************************

\* This trigger fires when the balance record is created or destroyed
\* Notice that it doesn't track the record content
MonitorTrigger_Balance_RecordChanged ==
    instance_has("Balance") /= next_instance_has("Balance")

\* This trigger fires when the balance record content changes
\* Notice that it will panic (won't fire) if the record doesn't exist
MonitorTrigger_Balance_ContentChanged ==
    Balance /= Balance'

\* Only deposit and claim methods are allowed to alter balances
MonitorEffect_Balance_Changed ==
    \/ tx.method_name = "deposit"
    \/ tx.method_name = "claim"


\******************************
\* Token balance effect monitor
\******************************

\* This trigger fires when the token balance of this contract is reduced
\* Notice that it will panic (won't fire) if balance record doesn't exist
MonitorTrigger_TokenBalance_Reduced ==
    next_token_balance(Balance.token, env.current_contract_address) <
    token_balance(Balance.token, env.current_contract_address) 

\* Only claim method is allowed to reduce this contract token balance
MonitorEffect_TokenBalance_Reduced ==
    tx.method_name = "claim"

================================================
