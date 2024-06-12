(*
 * Claim method monitors for the Timelock contract
 * 
 * Per our original discussion in https://github.com/freespek/solarkraft/blob/32f48e5f26e4cce76df4703a1b29fd1752cd1677/doc/case-studies/timelock/README.md
 * the MustHold_<method>_<id>, MustPass_<method>_<id>, and MustFail_<method>_<id> ( MustRevert here ) invariants could, in the future,
 * get automatically composed into Must<X>_<method>, and ultimately into a single Inv_<method> operator, since the
 * compositions are fully deterministic.
 *
 * As this monitor is written to illustrate our intended approach, these compositions are written manually from their respective 
 * sub-components, following the shape outlined in the above README, and as such this monitor is larger than what a user would
 * be expected to write (namely only the individual Must<X>_<method>_<id> invariants).
 *
 * Andrey Kuprianov, Jure Kukovec, 2024
 *)
---- MODULE claim ----

EXTENDS state, typedefs, Variants

(*
    @typeAlias: claimArgs = { 
        claimant: $address
    };
*)
claim_typedefs == TRUE


\* We don't support signatures ATM, see #85
\* $type: ($claimArgs, $env) => Bool;
\* MustRevert_claim_Unauthorized(args, env) == 
\*     ~authorized(args.claimant, env)

\* @type: ($env) => Bool;
MustRevert_claim_NoBalanceRecord(env) == 
    ~instance_has("Balance", env)

\* @type: ($claimArgs) => Bool;
MustRevert_claim_NotClaimant(args) == 
    \A i \in DOMAIN Balance.claimants: 
        Balance.claimants[i] /= args.claimant

\* A note on MustPass_*: Our instrumentation only accepts successful transactions (see #61). If we were to design invariants of the shape
\* X => tx_is_succesful (i.e. the proposed MustPass_* format), they would be vacuously true, regardless of the shape of X.
\* To this end, we instead negate MustPass_* properties, and turn them into MustRevert_* properties. (see https://github.com/freespek/solarkraft/pull/58#discussion_r1629575199)

\* One success condition: correctly claimed before time bound
\* @type: ($env) => Bool;
MustRevert_claim_BeforeTimeBound(env) ==
    /\ Balance.time_bound.kind = Variant("Before", "U_OF_UNIT")
    /\ env.timestamp > Balance.time_bound.timestamp

\* Another success condition: correctly claimed after time bound
\* @type: ($env) => Bool;
MustRevert_claim_AfterTimeBound(env) ==
    /\ Balance.time_bound.kind = Variant("After", "U_OF_UNIT")
    /\ env.timestamp < Balance.time_bound.timestamp

\* @type: ($env) => Bool;
MustHold_claim_BalanceRecordRemoved(env) ==
    ~next_instance_has("Balance", env)

\* ----------------------------------------------------------
\* The invariants below 
\* ----------------------------------------------------------

\* Auxiliary predicate describing the failure condition
\* (formed as a disjunction of all "MustRevert" predicates)
\* @type: ($claimArgs, $env) => Bool;
MustRevert_claim(args, env) ==
    \/ MustRevert_claim_NoBalanceRecord(env)
    \/ MustRevert_claim_NotClaimant(args)
    \/ MustRevert_claim_BeforeTimeBound(env)
    \/ MustRevert_claim_AfterTimeBound(env)
    \* Checking of the condition(s) below is not yet supported 
    \* \/ MustRevert_claim_Unauthorized(args)

\* Auxiliary predicate describing the effect
\* (formed as a conjunction of all "MustHold" predicates)
\* @type: ($env) => Bool;
MustHold_claim(env) ==
    /\ MustHold_claim_BalanceRecordRemoved(env)


\* Monitor invariants to be checked
\* By our convention, if the method is `claim`, and any MustRevert_claim_X property holds, the transcation should
\* be unsuccesful. Since we only read succesful transactions, we use the property of implication, A => B equals ~B => ~A, 
\* and assert that ~MustRevert_claim_X for all MustRevert_claim_X predicates (upon succss)
\* @type: ($claimArgs, $env) => Bool;
Inv_MustRevert_claim(args, env) == ~MustRevert_claim(args, env)

\* @type: ($claimArgs, $env) => Bool;
Inv_MustPass_claim(args, env) == TRUE

\* @type: ($env) => Bool;
Inv_MustHold_claim(env) == MustHold_claim(env)


\* The main invariant
\* (formed as a conjunction of all auxiliary invariants)
\* @type: ($claimArgs, $env) => Bool;
Inv_claim(args, env) ==
    /\ Inv_MustRevert_claim(args, env)
    /\ Inv_MustPass_claim(args, env)
    /\ Inv_MustHold_claim(env)

\* @type: ($env, $address) => Bool;
claim(env, claimant) ==
    LET args == [ 
        claimant |-> claimant
    ] IN 
    Inv_claim(args, env)

================================================
