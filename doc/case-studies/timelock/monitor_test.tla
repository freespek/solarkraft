(*
 * Tests for main monitor spec of the Timelock contract
 *
 * The concrete values will be fetched from blockchain transactions
 * Here we manually create a few for testing purposes.
 * 
 * Andrey Kuprianov, 2024
 *)

---- MODULE monitor_test ----

EXTENDS monitor

\****************************************************************************************
\*
\* A monitor test N is validated via running
\* apalache-mc check --length=1 --init=Init_N --next=Next_N claim_test.tla
\* 
\****************************************************************************************

\* Successful claim call; executing "claim" monitor
Init_1 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 10 ]
    /\ tx = [ method_name |-> "claim", signatures |-> {"bob"}, status |-> TRUE ]
    /\ instance_storage = { "Balance" }
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"bob", 100>>, <<"this", 100>>}) >>
       })
    /\ Balance = [
            token |-> "TOK", 
            amount |-> 100, 
            claimants |-> <<"alice", "bob">>,
            time_bound |-> [kind |-> "Before", timestamp |-> 42]
        ]

Next_1 ==
    /\ env' = env
    /\ tx' = tx
    /\ instance_storage' = {}
    /\ token_balances' = SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"bob", 200>>, <<"this", 0>>}) >>
       })
    /\ Balance' = [
            token |-> "", 
            amount |-> 0, 
            claimants |-> <<>>,
            time_bound |-> [kind |-> "", timestamp |-> 0]
        ]
    /\ claim("bob")

\* Successful claim call; executing "monitor"
Init_2 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 10 ]
    /\ tx = [ method_name |-> "claim", signatures |-> {"bob"}, status |-> TRUE ]
    /\ instance_storage = { "Balance" }
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"bob", 100>>, <<"this", 100>>}) >>
       })
    /\ Balance = [
            token |-> "TOK", 
            amount |-> 100, 
            claimants |-> <<"alice", "bob">>,
            time_bound |-> [kind |-> "Before", timestamp |-> 42]
        ]

Next_2 ==
    /\ env' = env
    /\ tx' = tx
    /\ instance_storage' = {}
    /\ token_balances' = SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"bob", 200>>, <<"this", 0>>}) >>
       })
    /\ Balance' = [
            token |-> "", 
            amount |-> 0, 
            claimants |-> <<>>,
            time_bound |-> [kind |-> "", timestamp |-> 0]
        ]
    /\ monitor


\* Failure: Contract balance record is changed by another call (caught by "monitor")
\* Apalache should report a deadlock!
Init_3 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 10 ]
    /\ tx = [ method_name |-> "withdraw", signatures |-> {"bob"}, status |-> TRUE ]
    /\ instance_storage = { "Balance" }
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"bob", 100>>, <<"this", 100>>}) >>
       })
    /\ Balance = [
            token |-> "TOK", 
            amount |-> 100, 
            claimants |-> <<"alice", "bob">>,
            time_bound |-> [kind |-> "Before", timestamp |-> 42]
        ]

Next_3 ==
    /\ env' = env
    /\ tx' = tx
    /\ instance_storage' = {}
    /\ token_balances' = SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"bob", 250>>, <<"this", 50>>}) >>
       })
    /\ Balance' = [
            token |-> "TOK", 
            amount |-> 50, 
            claimants |-> <<"alice", "bob">>,
            time_bound |-> [kind |-> "Before", timestamp |-> 42]
        ]
    /\ monitor

================================================