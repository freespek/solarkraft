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
MustFail_Unauthorized(args) == 
    ~authorized(args.claimant)

MustFail_NoBalanceRecord(args) == 
    ~instance_has("Balance")

\* @type: ($claimArgs) => Bool;
MustFail_NotClaimant(args) == 
    \A i \in DOMAIN Balance.claimants: 
        Balance.claimants[i] /= args.claimant

\* One success condition: correctly claimed before time bound
MustPass_BeforeTimeBound(args) ==
    /\ Balance.time_bound.kind = "Before" 
    /\ env.ledger_timestamp <= Balance.time_bound.timestamp

\* Another success condition: correctly claimed after time bound
MustPass_AfterTimeBound(args) ==
    /\ Balance.time_bound.kind = "After" 
    /\ env.ledger_timestamp >= Balance.time_bound.timestamp

\* @type: ($claimArgs) => Bool;
MustHold_TokenTransferred(args) ==
    token_transferred(
        Balance.token, env.current_contract_address, args.claimant, Balance.amount)

MustHold_BalanceRecordRemoved(args) ==
    ~next_instance_has("Balance")



\* Everything below is deterministic, and will be generated automatically
\* For now, we encode this manually

\* Auxiliary predicate describing the failure condition
\* (formed as a disjunction of all "MustFail" predicates)
MustFail(args) ==
    \/ MustFail_Unauthorized(args)
    \/ MustFail_NoBalanceRecord(args)
    \/ MustFail_NotClaimant(args)

\* Auxiliary predicate describing the success condition
\* (formed as a disjunction of all "MustPass" predicates)
MustPass(args) ==
    \/ MustPass_BeforeTimeBound(args)
    \/ MustPass_AfterTimeBound(args)

\* Auxiliary predicate describing the effect
\* (formed as a conjunction of all "MustHold" predicates)
MustHold(args) ==
    /\ MustHold_TokenTransferred(args)
    /\ MustHold_BalanceRecordRemoved(args)


\* Monitor invariants to be checked
\* (encode the expected interpretation of monitor predicates)
Inv_MustFail(args) ==
    (   /\ tx.method_name = "claim" 
        /\ MustFail(args)
    )   => tx.status = FALSE

Inv_MustPass(args) ==
    (   /\ tx.method_name = "claim" 
        /\ ~MustFail(args)
        /\ MustPass(args)
    )   => tx.status = TRUE

Inv_MustHold(args) ==
    (   /\ tx.method_name = "claim"
        /\ tx.status = TRUE
    )   => MustHold(args)


\* The main invariant
\* (formed as a conjunction of all auxiliary invariants)
\* @type: ($claimArgs) => Bool;
Inv(args) ==
    /\ Inv_MustFail(args)
    /\ Inv_MustPass(args)
    /\ Inv_MustHold(args)

claim(claimant) ==
    LET args == [ 
        claimant |-> claimant
    ] IN 
    Inv(args)

================================================
