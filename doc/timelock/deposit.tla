(*
 * Deposit method monitors for the Timelock contract
 *
 * Andrey Kuprianov, Jure Kukovec, 2024
 *)
---- MODULE deposit ----

EXTENDS state, typedefs

(*
    @typeAlias: depositArgs = { 
        from: $address,
        token: $address,
        amount: Int,
        claimants: Seq($address),
        time_bound: $timeBound
    };
*)
deposit_typedefs == TRUE

\* @type: ($depositArgs) => Bool;
MustFail_deposit_TooManyClaimants(args) == 
    Len(args.claimants) > 10

\* We don't support signatures ATM, see #85
\* $type: ($depositArgs, $env) => Bool;
\* MustFail_deposit_Unauthorized(args, env) == 
    \* ~authorized(args.from, env)

\* Balance is externally relevant; Init flag is not
\* What matters for users is that balance is not overwritten
\* @type: ($env) => Bool;
MustFail_deposit_AlreadyInitialized(env) == 
    instance_has("Balance", env)

\* @type: ($env) => Bool;
MustHold_deposit_BalanceRecordCreated(env) ==
    next_instance_has("Balance", env)

\* @type: ($depositArgs) => Bool;
MustHold_deposit_BalanceRecordCorrect(args) ==
    /\ Balance'.token = args.token
    /\ Balance'.amount = args.amount
    /\ Balance'.time_bound = args.time_bound
    /\ Balance'.claimants = args.claimants

\* Everything below is deterministic, and will be generated automatically
\* For now, we encode this manually

\* Auxiliary predicate describing the failure condition
\* (formed as a disjunction of all "MustFail" predicates)
\* @type: ($depositArgs, $env) => Bool;
MustFail_deposit(args, env) ==
    \/ MustFail_deposit_TooManyClaimants(args)
    \/ MustFail_deposit_AlreadyInitialized(env)
    \* Checking of the condition(s) below is not yet supported 
    \* \/ MustFail_deposit_Unauthorized(args)

\* Auxiliary predicate describing the effect
\* (formed as a conjunction of all "MustHold" predicates)
\* @type: ($depositArgs, $env) => Bool;
MustHold_deposit(args, env) ==
    /\ MustHold_deposit_BalanceRecordCreated(env)
    /\ MustHold_deposit_BalanceRecordCorrect(args)

\* Monitor invariants to be checked
\* By our convention, if the method is `deposit`, and any MustFail_deposit_X property holds, the transcation should
\* be unsuccesful. Since we only read succesful transactions, we use the property of implication, A => B equals ~B => ~A, 
\* and assert that ~MustFail_deposit_X for all MustFail_deposit_X predicates (upon succss)
\* @type: ($depositArgs, $env) => Bool;
Inv_MustFail_deposit(args, env) == ~MustFail_deposit(args, env)

\* We don't have MustPass_ here
\* @type: ($depositArgs, $env) => Bool;
Inv_MustPass_deposit(args, env) == TRUE

\* @type: ($depositArgs, $env) => Bool;
Inv_MustHold_deposit(args, env) == MustHold_deposit(args, env)


\* The main invariant
\* (formed as a conjunction of all auxiliary invariants)
\* @type: ($depositArgs, $env) => Bool;
Inv_deposit(args, env) ==
    /\ Inv_MustFail_deposit(args, env)
    /\ Inv_MustPass_deposit(args, env)
    /\ Inv_MustHold_deposit(args, env)

\* Operator that enforces the main invariant,
\* specialized for transaction arguments
\* @type: ($env, $address, $address, Int, Seq($address), $timeBound) => Bool;
deposit(env, from, token, amount, claimants, time_bound) ==
    LET args == [ 
        from |-> from, 
        token |-> token,
        amount |-> amount,
        claimants |-> claimants,
        time_bound |-> time_bound
    ] IN 
    Inv_deposit(args, env)

================================================
