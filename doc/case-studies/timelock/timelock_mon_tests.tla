---- MODULE timelock_mon_tests ----

EXTENDS timelock_mon_txs


\****************************************************************************************
\* Monitor tests (aka verification conditions)
\* Each monitor test is a tuple to be produced/filled by fetcher/verifier
\* (Init, TxRes, Inv), where:
\* - Init is any initial predicate
\* - TxRes is a conjunction of any of Tx and Res predicates
\* - Inv is any monitor predicate; produced from monitor specs
\*
\* A monitor test is validated via running
\* apalache-mc check --length=1 --init=Init --next=TxRes --inv=Inv timelock_mon_tests.tla
\* 
\****************************************************************************************


\*******************************************
\* Monitor predicates
\* Produced automatically from monitor specs
\*******************************************

\*************************
\* Deposit method monitors
\*************************

\* Auxiliary predicate describing the failure condition
MustFail_deposit ==
    \/ MustFail_deposit_TooManyClaimants
    \/ MustFail_deposit_Unauthorized
    \/ MustFail_deposit_NotEnoughBalance
    \/ MustFail_deposit_AlreadyInitialized

\* Auxiliary predicate describing the success condition
MustPass_deposit ==
    \/ MustPass_deposit_Default

\* Auxiliary predicate describing the effect
MustHold_deposit ==
    /\ MustHold_deposit_BalanceRecordCreated
    /\ MustHold_deposit_BalanceRecordCorrect
    /\ MustHold_deposit_TokenTransferred

\* Monitor predicates to be checked

Inv_MustFail_deposit ==
    (   /\ tx.method_name = "deposit" 
        /\ MustFail_deposit
    )   => tx'.status = FALSE

Inv_MustPass_deposit ==
    (   /\ tx.method_name = "deposit" 
        /\ ~MustFail_deposit 
        /\ MustPass_deposit
    )   => tx'.status = TRUE

Inv_MustHold_deposit ==
    (   /\ tx.method_name = "deposit"
        /\ tx'.status = TRUE
    )   => MustHold_deposit


\***********************
\* Claim method monitors
\***********************

\* Auxiliary predicate describing the failure condition
MustFail_claim ==
    \/ MustFail_claim_Unauthorized
    \/ MustFail_claim_NoBalanceRecord
    \/ MustFail_claim_NotClaimant

\* Auxiliary predicate describing the success condition
MustPass_claim ==
    \/ MustPass_claim_BeforeTimeBound
    \/ MustPass_claim_AfterTimeBound

\* Auxiliary predicate describing the effect
MustHold_claim ==
    /\ MustHold_claim_TokenTransferred
    /\ MustHold_claim_BalanceRecordRemoved

\* Monitor predicates to be checked

Inv_MustFail_claim ==
    (   /\ tx.method_name = "claim"
        /\ MustFail_claim
    )   => tx'.status = FALSE

Inv_MustPass_claim ==
    (   /\ tx.method_name = "claim"
        /\ ~MustFail_claim 
        /\ MustPass_claim
    ) => tx'.status = TRUE

Inv_MustHold_claim ==
    (   /\ tx.method_name = "claim"
        /\ tx'.status = TRUE
    )   => MustHold_claim


\*******************************
\* Balance record effect monitor
\*******************************

MonitorTrigger_Balance ==
    \/ MonitorTrigger_Balance_RecordChanged
    \/ MonitorTrigger_Balance_ContentChanged

MonitorEffect_Balance == 
    /\ MonitorEffect_Balance_Changed

Inv_Monitor_Balance ==
    MonitorTrigger_Balance => MonitorEffect_Balance


\******************************
\* Token balance effect monitor
\******************************

MonitorTrigger_TokenBalance ==
    \/ MonitorTrigger_TokenBalance_Reduced

MonitorEffect_TokenBalance == 
    /\ MonitorEffect_TokenBalance_Reduced

Inv_Monitor_TokenBalance ==
    MonitorTrigger_TokenBalance => MonitorEffect_TokenBalance


\***********************************************
\* Tx & Result combined
\* In the real system are fetched and translated 
\* from the blockchain transactions
\* Here, some are encoded manually for testing 
\***********************************************

TxRes_Deposit_Alice_100_BobCarol_Before_Pass == 
    /\ Tx_Deposit_Alice_100_BobCarol_Before
    /\ Res_Pass

TxRes_Deposit_Alice_100_BobCarol_Before_Fail == 
    /\ Tx_Deposit_Alice_100_BobCarol_Before
    /\ Res_Fail

TxRes_Deposit_Alice_100_BobCarol_Before_NextBalanceRecordExists_BalanceRecordCorrect_TokenNotTransferredToContract_Pass ==
    /\ Tx_Deposit_Alice_100_BobCarol_Before
    /\ Res_NextBalanceRecordExists_BalanceRecordCorrect_TokenNotTransferredToContract_Pass

================================================