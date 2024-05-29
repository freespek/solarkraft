(*
 * Token balance effect monitor for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE token_balance ----

EXTENDS timelock

\* This trigger fires when the token balance of this contract is reduced
\* Notice that it will panic (won't fire) if balance record doesn't exist
MonitorTrigger_BalanceReduced ==
    next_token_balance(Balance.token, env.current_contract_address) <
    token_balance(Balance.token, env.current_contract_address) 

\* Only claim method is allowed to reduce this contract token balance
MonitorEffect_AllowedToReduce ==
    tx.status = TRUE => tx.method_name = "claim"


\* Everything below is deterministic, and will be generated automatically
\* For now, we encode this manually

MonitorTrigger ==
    \/ MonitorTrigger_BalanceReduced

MonitorEffect == 
    /\ MonitorEffect_AllowedToReduce

monitor ==
    MonitorTrigger => MonitorEffect

================================================
