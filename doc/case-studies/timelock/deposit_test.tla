(*
 * Tests for the deposit method of the Timelock contract
 *
 * The concrete values will be fetched from blockchain transactions
 * Here we manually create a few for testing purposes.
 * 
 * Andrey Kuprianov, 2024
 *)

---- MODULE deposit_test ----

EXTENDS deposit

\****************************************************************************************
\*
\* A monitor test N is validated via running
\* apalache-mc check --length=1 --init=Init_N --next=Next_N deposit_test.tla
\* 
\****************************************************************************************

\* Successful deposit call
Init_1 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 0 ]
    /\ tx = [ method_name |-> "deposit", signatures |-> {"alice"}, status |-> TRUE ]
    /\ instance_storage = {}
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"this", 0>>}) >>
       })
    /\ Balance = [
            token |-> "", 
            amount |-> 0, 
            claimants |-> <<>>,
            time_bound |-> [kind |-> "", timestamp |-> 0]
        ]

Next_1 ==
    /\ env' = env
    /\ tx' = tx
    /\ instance_storage' = { "Balance" }
    /\ token_balances' = SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 0>>, <<"this", 100>>}) >>
       })
    /\ Balance' = [
            token |-> "TOK", 
            amount |-> 100, 
            claimants |-> <<"alice", "bob">>,
            time_bound |-> [kind |-> "Before", timestamp |-> 42]
        ]
    /\ deposit("alice", "TOK", 100, <<"alice", "bob">>, [kind |-> "Before", timestamp |-> 42])


\* Failing deposit call: Balance record exists
Init_2 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 0 ]
    /\ tx = [ method_name |-> "deposit", signatures |-> {"alice"}, status |-> FALSE ]
    /\ instance_storage = { "Balance" }
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"this", 0>>}) >>
       })
    /\ Balance = [
            token |-> "", 
            amount |-> 0, 
            claimants |-> <<>>,
            time_bound |-> [kind |-> "", timestamp |-> 0]
        ]

Next_2 == 
    /\ env' = env
    /\ tx' = tx
    /\ instance_storage' = instance_storage
    /\ token_balances' = token_balances
    /\ Balance' = Balance
    /\ deposit("alice", "TOK", 100, <<"alice", "bob">>, [kind |-> "Before", timestamp |-> 42])

\* Failing deposit call: Too many claimants
Init_3 == 
    /\ env = [ current_contract_address |-> "this", ledger_timestamp |-> 0 ]
    /\ tx = [ method_name |-> "deposit", signatures |-> {"alice"}, status |-> FALSE ]
    /\ instance_storage = {}
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>, <<"this", 0>>}) >>
       })
    /\ Balance = [
            token |-> "", 
            amount |-> 0, 
            claimants |-> <<>>,
            time_bound |-> [kind |-> "", timestamp |-> 0]
        ]

Next_3 == 
    /\ env' = env
    /\ tx' = tx
    /\ instance_storage' = instance_storage
    /\ token_balances' = token_balances
    /\ Balance' = Balance
    /\ deposit("alice", "TOK", 100, <<"1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11">>, 
        [kind |-> "Before", timestamp |-> 42])


================================================