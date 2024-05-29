(*
 * Deposit method monitors for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE deposit ----

EXTENDS timelock


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
MustFail_TooManyClaimants(args) == 
    Len(args.claimants) > 10

\* @type: ($depositArgs) => Bool;
MustFail_Unauthorized(args) == 
    ~authorized(args.from)

\* This property would not be originally conceived 
\* if looking solely at the timelock contract source
\* @type: ($depositArgs) => Bool;
MustFail_NotEnoughBalance(args) == 
    token_balance(args.token, args.from) < args.amount

\* Balance is externally relevant; Init flag is not
\* What matters for users is that balance is not overwritten
MustFail_AlreadyInitialized(args) == 
    instance_has("Balance")

\* The above failure conditions exhaust the precondition of deposit method
\* The default success condition is not needed, but we may provide it
MustPass_Default(args) == TRUE

MustHold_BalanceRecordCreated(args) ==
    next_instance_has("Balance")

\* @type: ($depositArgs) => Bool;
MustHold_BalanceRecordCorrect(args) ==
    /\ Balance'.token = args.token
    /\ Balance'.amount = args.amount
    /\ Balance'.time_bound = args.time_bound
    /\ Balance'.claimants = args.claimants

\* @type: ($depositArgs) => Bool;
MustHold_TokenTransferred(args) ==
    token_transferred(
        args.token, args.from, env.current_contract_address, args.amount
    )


\* Everything below is deterministic, and will be generated automatically
\* For now, we encode this manually

\* Auxiliary predicate describing the failure condition
\* (formed as a disjunction of all "MustFail" predicates)
MustFail(args) ==
    \/ MustFail_TooManyClaimants(args)
    \/ MustFail_Unauthorized(args)
    \/ MustFail_NotEnoughBalance(args)
    \/ MustFail_AlreadyInitialized(args)

\* Auxiliary predicate describing the success condition
\* (formed as a disjunction of all "MustPass" predicates)
MustPass(args) ==
    \/ MustPass_Default(args)

\* Auxiliary predicate describing the effect
\* (formed as a conjunction of all "MustHold" predicates)
MustHold(args) ==
    /\ MustHold_BalanceRecordCreated(args)
    /\ MustHold_BalanceRecordCorrect(args)
    /\ MustHold_TokenTransferred(args)

\* Monitor invariants to be checked
\* (encode the expected interpretation of monitor predicates)
Inv_MustFail(args) ==
    (   /\ tx.method_name = "deposit" 
        /\ MustFail(args)
    )   => tx.status = FALSE

Inv_MustPass(args) ==
    (   /\ tx.method_name = "deposit" 
        /\ ~MustFail(args)
        /\ MustPass(args)
    )   => tx.status = TRUE

Inv_MustHold(args) ==
    (   /\ tx.method_name = "deposit"
        /\ tx.status = TRUE
    )   => MustHold(args)


\* The main invariant
\* (formed as a conjunction of all auxiliary invariants)
\* @type: ($depositArgs) => Bool;
Inv(args) ==
    /\ Inv_MustFail(args)
    /\ Inv_MustPass(args)
    /\ Inv_MustHold(args)

\* Operator that enforces the main invariant,
\* specialized for transaction arguments
deposit(from, token, amount, claimants, time_bound) ==
    LET args == [ 
        from |-> from, 
        token |-> token,
        amount |-> amount,
        claimants |-> claimants,
        time_bound |-> time_bound
    ] IN 
    Inv(args)

================================================
