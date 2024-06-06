(*
 * Claim method monitors for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE claim ----

EXTENDS timelock

(*
    @typeAlias: claimArgs = { 
        claimant: $address
    };
*)
claim_typedefs == TRUE


\* @type: ($claimArgs) => Bool;
MustFail_claim_Unauthorized(args) == 
    ~authorized(args.claimant)

MustFail_claim_NoBalanceRecord(args) == 
    ~instance_has("Balance")

\* @type: ($claimArgs) => Bool;
MustFail_claim_NotClaimant(args) == 
    \A i \in DOMAIN Balance.claimants: 
        Balance.claimants[i] /= args.claimant

\* One success condition: correctly claimed before time bound
MustPass_claim_BeforeTimeBound(args) ==
    /\ Balance.time_bound.kind = "Before" 
    /\ env.ledger_timestamp <= Balance.time_bound.timestamp

\* Another success condition: correctly claimed after time bound
MustPass_claim_AfterTimeBound(args) ==
    /\ Balance.time_bound.kind = "After" 
    /\ env.ledger_timestamp >= Balance.time_bound.timestamp

\* @type: ($claimArgs) => Bool;
MustHold_claim_TokenTransferred(args) ==
    token_transferred(
        Balance.token, env.current_contract_address, args.claimant, Balance.amount)

MustHold_claim_BalanceRecordRemoved(args) ==
    ~next_instance_has("Balance")



\* Everything below is deterministic, and will be generated automatically
\* For now, we encode this manually

\* Auxiliary predicate describing the failure condition
\* (formed as a disjunction of all "MustFail" predicates)
MustFail_claim(args) ==
    \/ MustFail_claim_NoBalanceRecord(args)
    \/ MustFail_claim_NotClaimant(args)
    \* Checking of the condition(s) below is not yet supported 
    \* \/ MustFail_claim_Unauthorized(args)

\* Auxiliary predicate describing the success condition
\* (formed as a disjunction of all "MustPass" predicates)
MustPass_claim(args) ==
    \/ MustPass_claim_BeforeTimeBound(args)
    \/ MustPass_claim_AfterTimeBound(args)

\* Auxiliary predicate describing the effect
\* (formed as a conjunction of all "MustHold" predicates)
MustHold_claim(args) ==
    /\ MustHold_claim_BalanceRecordRemoved(args)
    \* Checking of the condition(s) below is not yet supported 
    \* /\ MustHold_claim_TokenTransferred(args)


\* Monitor invariants to be checked
\* (encode the expected interpretation of monitor predicates)
Inv_MustFail_claim(args) ==
    (   /\ tx.method_name = "claim" 
        /\ MustFail_claim(args)
    )   => tx.status = FALSE

Inv_MustPass_claim(args) ==
    (   /\ tx.method_name = "claim" 
        /\ ~MustFail_claim(args)
        /\ MustPass_claim(args)
    )   => tx.status = TRUE

Inv_MustHold_claim(args) ==
    (   /\ tx.method_name = "claim"
        /\ tx.status = TRUE
    )   => MustHold_claim(args)


\* The main invariant
\* (formed as a conjunction of all auxiliary invariants)
\* @type: ($claimArgs) => Bool;
Inv_claim(args) ==
    /\ Inv_MustFail_claim(args)
    /\ Inv_MustPass_claim(args)
    /\ Inv_MustHold_claim(args)

claim(claimant) ==
    LET args == [ 
        claimant |-> claimant
    ] IN 
    Inv_claim(args)

================================================
