(*
 * Deposit method monitors for the Timelock contract
 * 
 * Per our original discussion in https://github.com/freespek/solarkraft/blob/32f48e5f26e4cce76df4703a1b29fd1752cd1677/doc/case-studies/timelock/README.md
 * the MustHold_<method>_<id>, MustPass_<method>_<id>, and MustFail_<method>_<id> ( MustRevert here ) invariants could, in the future,
 * get automatically composed into Must<X>_<method>, and ultimately into a single Inv_<method> operator, since the
 * compositions are fully deterministic.
 *
 * As this monitor is written to illustrate our intended approach, these compositions are written manually from their respective 
 * sub-components, following the shape outlined in the above README.
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

\* `deposit` reverts if invoked with too many claimants.
\* @type: ($depositArgs) => Bool;
MustRevert_deposit_TooManyClaimants(args) == 
    Len(args.claimants) > 10

\* We don't support signatures ATM, see #85
\* $type: ($depositArgs, $env) => Bool;
\* MustRevert_deposit_Unauthorized(args, env) == 
    \* ~authorized(args.from, env)

\* `deposit` reverts if the contract is already initialized.
\* The contract internally checks the "Init" flag, however
\* what matters for users is that balance is not overwritten.
\* @type: ($env) => Bool;
MustRevert_deposit_AlreadyInitialized(env) == 
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

\* Auxiliary predicate describing the failure condition
\* (formed as a disjunction of all "MustRevert" predicates)
\* @type: ($depositArgs, $env) => Bool;
MustRevert_deposit(args, env) ==
    \/ MustRevert_deposit_TooManyClaimants(args)
    \/ MustRevert_deposit_AlreadyInitialized(env)
    \* Checking of the condition(s) below is not yet supported 
    \* \/ MustRevert_deposit_Unauthorized(args)

\* Auxiliary predicate describing the effect
\* (formed as a conjunction of all "MustHold" predicates)
\* @type: ($depositArgs, $env) => Bool;
MustHold_deposit(args, env) ==
    /\ MustHold_deposit_BalanceRecordCreated(env)
    /\ MustHold_deposit_BalanceRecordCorrect(args)

\* Monitor invariants to be checked
\* By our convention, if the method is `deposit`, and any MustRevert_deposit_X property holds, the transcation should
\* be unsuccesful. Since we only read succesful transactions, we use the property of implication, A => B equals ~B => ~A, 
\* and assert that ~MustRevert_deposit_X for all MustRevert_deposit_X predicates (upon succss)
\* @type: ($depositArgs, $env) => Bool;
Inv_MustRevert_deposit(args, env) == ~MustRevert_deposit(args, env)

\* We don't have MustPass_ here
\* @type: ($depositArgs, $env) => Bool;
Inv_MustPass_deposit(args, env) == TRUE

\* @type: ($depositArgs, $env) => Bool;
Inv_MustHold_deposit(args, env) == MustHold_deposit(args, env)


\* The main invariant
\* (formed as a conjunction of all auxiliary invariants)
\* @type: ($depositArgs, $env) => Bool;
Inv_deposit(args, env) ==
    /\ Inv_MustRevert_deposit(args, env)
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
