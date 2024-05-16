(*
 * Monitor specification for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE timelock_monitor ----

\*************************
\* Deposit method monitors
\*************************

MustFail_deposit_TooManyClaimants == 
    claimants.len > 10

MustFail_deposit_Unauthorized == 
    ~authorized(from)

\* This property would not be originally conceived 
\* if looking solely at the timelock contract source
MustFail_deposit_NotEnoughBalance == 
    token.balance(from) < amount

\* Balance is externally relevant; initialized flag is not
\* What matters for users is that balance is not overwritten
MustFail_deposit_AlreadyInitialized == 
    exists(balance)

\* The above failure conditions exhaust the precondition of deposit method
\* The default success condition is not needed, but we may provide it
MustSucceed_deposit_Default = TRUE

MustAchieve_deposit_BalanceRecordCreated ==
    exists(balance')

MustAchieve_deposit_BalanceRecordCorrect ==
    /\ balance'.token = token
    /\ balance'.amount = amount
    /\ balance'.time_bound = time_bound
    /\ balance'.claimants = claimants

MustAchieve_deposit_TokenTransferred ==
    token.transferred(from, this, amount)


\***********************
\* Claim method monitors
\***********************

MustFail_claim_Unauthorized == 
    ~authorized(claimant)

MustFail_claim_NoBalanceRecord == 
    ~exists(balance)

MustFail_claim_NotClaimant == 
    claimant \notin claimants

\* One success condition: correctly claimed before time bound
MustSucceed_claim_BeforeTimeBount
    /\ time_bound.kind = "Before" 
    /\ env.ledger.timestamp <= balance.time_bound.timestamp

\* Another success condition: correctly claimed after time bound
MustSucceed_claim_AfterTimeBount
    /\ time_bound.kind = "After" 
    /\ env.ledger.timestamp >= balance.time_bound.timestamp

MustAchieve_claim_TokenTransferred ==
    balance.token.transferred(this, claimant, balance.amount)

MustAchieve_deposit_BalanceRecordRemoved ==
    ~exists(balance')


\************************
\* Balance record monitor
\************************

\* This trigger fires when the balance record is created or destroyed
\* Notice that it doesn't track the record content
MonitorTrigger_Balance_RecordAchieved ==
    exists(balance) /= exists(balance)'

\* This trigger fires when the balance record content Achieves
\* Notice that it will panic (won't fire) if the record doesn't exist
MonitorTrigger_Balance_ContentAchieved ==
    balance /= balance'

\* Only deposit and claim methods are allowed to alter balances
MonitorEffect_Balance_Achieved ==
    \/ method = "deposit"
    \/ method = "claim"


\************************
\* Token balance monitor
\************************

\* This trigger fires when the token balance of this contract is reduced
\* Notice that it will panic (won't fire) if balance record doesn't exist
MonitorTrigger_TokenBalance_Reduced ==
    token_balance(balance.token, this)' <
    token_balance(balance.token, this) 

\* Only claim method is allowed to reduce this contract token balance
MonitorEffect_TokenBalance_Reduced ==
    method = "claim"

=============================
