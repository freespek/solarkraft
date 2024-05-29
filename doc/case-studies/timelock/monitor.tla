(*
 * Monitor for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE monitor ----

EXTENDS deposit, claim, balance_record, token_balance

\* "deposit" and "claim" monitor operators are inherited
\* "monitor" for the effect monitors we define here explicitly

monitor == 
    /\ Monitor_BalanceRecord
    /\ Monitor_TokenBalance


================================================
