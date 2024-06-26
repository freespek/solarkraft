(*
 * Tests for the claim method of the Timelock contract
 *
 * The concrete values will be fetched from blockchain transactions
 * Here we manually create a few for testing purposes.
 * 
 * Andrey Kuprianov, 2024
 *)

---- MODULE claim_test ----

EXTENDS claim

\****************************************************************************************
\*
\* A monitor test N is validated via running
\* apalache-mc check --length=1 --init=Init_N --next=Next_N claim_test.tla
\* 
\****************************************************************************************

\* Successful claim call
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


\* Failing claim call: no balance record
Init_2 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 10 ]
    /\ tx = [ method_name |-> "claim", signatures |-> {"bob"}, status |-> FALSE ]
    /\ instance_storage = { }
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
    /\ instance_storage' = instance_storage
    /\ token_balances' = token_balances
    /\ Balance' = Balance
    /\ claim("bob")


\* Failing claim call: not a claimant
Init_3 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 10 ]
    /\ tx = [ method_name |-> "claim", signatures |-> {"bob"}, status |-> FALSE ]
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
    /\ instance_storage' = instance_storage
    /\ token_balances' = token_balances
    /\ Balance' = Balance
    /\ claim("carol")

================================================