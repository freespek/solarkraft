(*
 * Balance record effect monitor for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE balance_record ----

EXTENDS timelock

\* This trigger fires when the balance record is created or destroyed
\* Notice that it doesn't track the record content
MonitorTrigger_BalanceRecord_RecordChanged ==
    instance_has("Balance") /= next_instance_has("Balance")

\* This trigger fires when the balance record content changes
\* Notice that it will panic (won't fire) if the record doesn't exist
MonitorTrigger_BalanceRecord_ContentChanged ==
    Balance /= Balance'

\* Only deposit and claim methods are allowed to alter balances
MonitorEffect_BalanceRecord_AllowedToChange ==
    tx.status = TRUE => (
        \/ tx.method_name = "deposit"
        \/ tx.method_name = "claim"
    )


\* Everything below is deterministic, and will be generated automatically
\* For now, we encode this manually

MonitorTrigger_BalanceRecord ==
    \/ MonitorTrigger_BalanceRecord_RecordChanged
    \/ MonitorTrigger_BalanceRecord_ContentChanged

MonitorEffect_BalanceRecord == 
    /\ MonitorEffect_BalanceRecord_AllowedToChange

Monitor_BalanceRecord ==
    MonitorTrigger_BalanceRecord => MonitorEffect_BalanceRecord

================================================
