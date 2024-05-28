(*
 * Example transactions and results,
 * for testing of the Timelock contract monitor specs.
 * Real transactions/results will be fetched from the blockchain.
 *
 * Andrey Kuprianov, 2024
 *)

---- MODULE timelock_mon_txs ----

EXTENDS timelock_mon

\************************
\* Initial states
\************************

\* A completely non-deterministic initial state
Init_Nondet == 
    /\ env = Gen(4)
    /\ tx = Gen(4)
    /\ args = Gen(12)
    /\ Balance = Gen(4)
    /\ token_balances = Gen(4)

Init_NoBalance_NoTokens == Init_Nondet
    /\ token_balances =  SetAsFun({})
    /\ env.instance_storage = {}

Init_NoBalance_AliceHas10TOK == Init_Nondet
    /\ env.instance_storage = {}
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 10>>}) >>
       })

Init_NoBalance_AliceHas100TOK == Init_Nondet
    /\ env.instance_storage = {}
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>}) >>
       })

Init_NoBalance_AliceHas200TOK == Init_Nondet
    /\ env.instance_storage = {}
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>}) >>
       })

Init_NoBalance_AliceHas100KOT == Init_Nondet
    /\ env.instance_storage = {}
    /\ token_balances =  SetAsFun({
        << "KOT", SetAsFun({ <<"alice", 100>>}) >>
       })

Init_HasBalance_AliceHas100TOK == Init_Nondet
    /\ env.instance_storage = { "Balance" }
    /\ token_balances =  SetAsFun({
        << "TOK", SetAsFun({ <<"alice", 100>>}) >>
       })

\************************
\* Transactions
\************************

\* A completely non-deterministic transaction 
\* (with some natural restrictions)
Tx_Nondet == 
    /\ env' = Gen(4)
    /\ env'.current_contract_address = env.current_contract_address
    /\ tx' = Gen(4)
    /\ tx'.method_name = tx.method_name
    /\ tx'.signatures = tx.signatures
    /\ args' = args
    /\ Balance' = Gen(4)
    /\ token_balances' = Gen(4)

\* Alice deposits 100 TOK; allows to claim it before ledger 42
Tx_Deposit_Alice_100_BobCarol_Before == Tx_Nondet
    /\ tx.method_name = "deposit"
    /\ tx.signatures = { "alice" }
    /\ args.token = "TOK"
    /\ args.amount = 100
    /\ args.from = "alice"
    /\ args.claimants = << "bob", "carol" >>
    /\ args.time_bound = [ kind |-> "Before", timestamp |-> 42 ]

\* Alice deposits 100 TOK; allows to claim it after ledger 42
Tx_Deposit_Alice__100_BobCarol_After == Tx_Nondet
    /\ tx.method_name = "deposit"
    /\ tx.signatures = { "alice" }
    /\ args.token = "TOK"
    /\ args.amount = 100
    /\ args.from = "alice"
    /\ args.claimants = << "bob", "carol" >>
    /\ args.time_bound = [ kind |-> "After", timestamp |-> 42 ]

\* Alice deposits 200 TOK; allows to claim it before ledger 42
Tx_Deposit_Alice_200_Dave_Before == Tx_Nondet
    /\ tx.method_name = "deposit"
    /\ tx.signatures = { "alice" }
    /\ args.token = "TOK"
    /\ args.amount = 100
    /\ args.from = "alice"
    /\ args.claimants = << "bob", "carol" >>
    /\ args.time_bound = [ kind |-> "Before", timestamp |-> 42 ]

\* Alice deposits 200 TOK; allows to claim it after ledger 42
Tx_Deposit_Alice_200_Dave_After == Tx_Nondet
    /\ tx.method_name = "deposit"
    /\ tx.signatures = { "alice" }
    /\ args.token = "TOK"
    /\ args.amount = 100
    /\ args.from = "alice"
    /\ args.claimants = << "bob", "carol" >>
    /\ args.time_bound = [ kind |-> "After", timestamp |-> 42 ]


\************************
\* Resulting states
\************************

Res_Pass == Tx_Nondet
    /\ tx'.status = TRUE

Res_Fail == Tx_Nondet
    /\ tx'.status = FALSE

Res_NextBalanceRecordExists_Pass == Tx_Nondet
    /\ next_instance_has("Balance")
    /\ tx'.status = TRUE

Res_NextBalanceRecordExists_Fail == Tx_Nondet
    /\ next_instance_has("Balance")
    /\ tx'.status = FALSE

Res_NextBalanceRecordNotExists_Pass == Tx_Nondet
    /\ ~next_instance_has("Balance")
    /\ tx'.status = TRUE

Res_NextBalanceRecordNotExists_Fail == Tx_Nondet
    /\ ~next_instance_has("Balance")
    /\ tx'.status = FALSE

Res_BalanceRecordCorrect_Pass == Tx_Nondet
    /\ Balance'.token = args.token
    /\ Balance'.amount = args.amount
    /\ Balance'.time_bound = args.time_bound
    /\ Balance'.claimants = args.claimants
    /\ tx'.status = TRUE

Res_BalanceRecordCorrect_Fail == Tx_Nondet
    /\ Balance'.token = args.token
    /\ Balance'.amount = args.amount
    /\ Balance'.time_bound = args.time_bound
    /\ Balance'.claimants = args.claimants
    /\ tx'.status = FALSE

Res_BalanceRecordIncorrect_Pass == Tx_Nondet
    /\ \/ Balance'.token /= args.token
       \/ Balance'.amount /= args.amount
       \/ Balance'.time_bound /= args.time_bound
       \/ Balance'.claimants /= args.claimants
    /\ tx'.status = TRUE

Res_BalanceRecordIncorrect_Fail == Tx_Nondet
    /\ \/ Balance'.token /= args.token
       \/ Balance'.amount /= args.amount
       \/ Balance'.time_bound /= args.time_bound
       \/ Balance'.claimants /= args.claimants
    /\ tx'.status = FALSE

Res_TokenTransferredToContract_Pass == Tx_Nondet
    /\ token_transferred(args.token, args.from, env.current_contract_address, args.amount)
    /\ tx'.status = TRUE

Res_TokenTransferredToContract_Fail == Tx_Nondet
    /\ token_transferred(args.token, args.from, env.current_contract_address, args.amount)
    /\ tx'.status = FALSE

Res_TokenNotTransferredToContract_Pass == Tx_Nondet
    /\ ~token_transferred(args.token, args.from, env.current_contract_address, args.amount)
    /\ tx'.status = TRUE

Res_TokenNotTransferredToContract_Fail == Tx_Nondet
    /\ ~token_transferred(args.token, args.from, env.current_contract_address, args.amount)
    /\ tx'.status = FALSE

Res_TokenTransferredFromContract_Pass == Tx_Nondet
    /\ token_transferred(Balance.token, env.current_contract_address, args.claimant, Balance.amount)
    /\ tx'.status = TRUE

Res_TokenTransferredFromContract_Fail == Tx_Nondet
    /\ token_transferred(Balance.token, env.current_contract_address, args.claimant, Balance.amount)
    /\ tx'.status = FALSE

Res_TokenNotTransferredFromContract_Pass == Tx_Nondet
    /\ ~token_transferred(Balance.token, env.current_contract_address, args.claimant, Balance.amount)
    /\ tx'.status = TRUE

Res_TokenNotTransferredFromContract_Fail == Tx_Nondet
    /\ ~token_transferred(Balance.token, env.current_contract_address, args.claimant, Balance.amount)
    /\ tx'.status = FALSE

Res_NextBalanceRecordExists_BalanceRecordCorrect_TokenNotTransferredToContract_Pass == Tx_Nondet
    /\ next_instance_has("Balance")
    /\ Balance'.token = args.token
    /\ Balance'.amount = args.amount
    /\ Balance'.time_bound = args.time_bound
    /\ Balance'.claimants = args.claimants
    /\ token_transferred(args.token, args.from, env.current_contract_address, args.amount)
    /\ tx'.status = TRUE

================================================