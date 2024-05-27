---- MODULE timelock_mon_txs ----

EXTENDS timelock_mon

\************************
\* Initial states
\************************

\* A completely non-deterministic initial state

Init_Nondet == 
    /\ env = Gen(10)
    /\ tx = Gen(10)
    /\ args = Gen(11)
    /\ Balance = Gen(10)
    /\ token_balances = Gen(10)


Init_NoTokens == Init_Nondet
    /\ token_balances =  SetAsFun({})
    /\ env.instance_storage = {}

Init_AliceHasTokens_NoBalance == Init_Nondet
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>}) >>
       })
    /\ env.instance_storage = {}

\************************
\* Transactions
\************************

\* A completely non-deterministic transaction state

Tx_Nondet == 
    /\ env' = Gen(10)
    /\ tx' = Gen(10)
    /\ args' = args
    /\ Balance' = Gen(10)
    /\ token_balances' = Gen(10)


Tx_Deposit1 == Tx_Nondet
    /\ tx.method_name = "deposit"
    /\ tx.signatures = { "alice", "bob", "carol" }
    /\ args.token = "TOK"
    /\ args.amount = 100
    /\ args.from = "alice"
    /\ args.claimants = << "alice", "bob", "carol" >>
    /\ args.time_bound = [ kind |-> "Before", timestamp |-> 42 ]


\************************
\* Resulting states
\************************

Res_Pass == Tx_Nondet
    /\ tx'.status = TRUE

Res_Fail == Tx_Nondet
    /\ tx'.status = FALSE


===========================================