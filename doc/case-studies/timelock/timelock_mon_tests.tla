---- MODULE timelock_mon_tests ----

EXTENDS timelock_mon_txs


\****************************************************************************************
\* Monitor tests
\* Each monitor test is a tuple of 
\* (Init, TxRes, Mon) which should be produced / filled 
\* by fetcher / verifier, where:
\* - Init is any initial predicate
\* - TxRes is a conjunction of any of Tx and Res predicates
\* - Mon is any monitor predicate; produced from monitor specs
\*
\* A monitor test is validated via running
\* apalache-mc check --length=1 --init=Init --next=TxRes --inv=Mon timelock_mon_tests.tla
\* 
\****************************************************************************************


\*****************************
\* Monitor predicates
\* Produced from monitor specs
\*****************************

Mon_MustFail_deposit_TooManyClaimants == 
    MustFail_deposit_TooManyClaimants => tx'.status = FALSE

Mon_MustFail_deposit_Unauthorized ==
    MustFail_deposit_Unauthorized => tx'.status = FALSE

Mon_MustFail_deposit_NotEnoughBalance ==
    MustFail_deposit_NotEnoughBalance => tx'.status = FALSE



\******************************
\* Tx & Result combined
\* Used here for manual testing
\******************************

TxRes_Deposit1_Pass == 
    /\ Tx_Deposit1
    /\ Res_Pass

TxRes_Deposit1_Fail == 
    /\ Tx_Deposit1
    /\ Res_Fail


===========================================