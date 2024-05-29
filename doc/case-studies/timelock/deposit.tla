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
MustFail_deposit_TooManyClaimants(args) == 
    Len(args.claimants) > 10

\* @type: ($depositArgs) => Bool;
MustFail_deposit_Unauthorized(args) == 
    ~authorized(args.from)

\* This property would not be originally conceived 
\* if looking solely at the timelock contract source
\* @type: ($depositArgs) => Bool;
MustFail_deposit_NotEnoughBalance(args) == 
    token_balance(args.token, args.from) < args.amount

\* Balance is externally relevant; Init flag is not
\* What matters for users is that balance is not overwritten
MustFail_deposit_AlreadyInitialized(args) == 
    instance_has("Balance")

\* The above failure conditions exhaust the precondition of deposit method
\* The default success condition is not needed, but we may provide it
MustPass_deposit_Default(args) == TRUE

MustHold_deposit_BalanceRecordCreated(args) ==
    next_instance_has("Balance")

\* @type: ($depositArgs) => Bool;
MustHold_deposit_BalanceRecordCorrect(args) ==
    /\ Balance'.token = args.token
    /\ Balance'.amount = args.amount
    /\ Balance'.time_bound = args.time_bound
    /\ Balance'.claimants = args.claimants

\* @type: ($depositArgs) => Bool;
MustHold_deposit_TokenTransferred(args) ==
    token_transferred(
        args.token, args.from, env.current_contract_address, args.amount
    )


\* Everything below is deterministic, and will be generated automatically
\* For now, we encode this manually

\* Auxiliary predicate describing the failure condition
\* (formed as a disjunction of all "MustFail" predicates)
MustFail_deposit(args) ==
    \/ MustFail_deposit_TooManyClaimants(args)
    \/ MustFail_deposit_Unauthorized(args)
    \/ MustFail_deposit_NotEnoughBalance(args)
    \/ MustFail_deposit_AlreadyInitialized(args)

\* Auxiliary predicate describing the success condition
\* (formed as a disjunction of all "MustPass" predicates)
MustPass_deposit(args) ==
    \/ MustPass_deposit_Default(args)

\* Auxiliary predicate describing the effect
\* (formed as a conjunction of all "MustHold" predicates)
MustHold_deposit(args) ==
    /\ MustHold_deposit_BalanceRecordCreated(args)
    /\ MustHold_deposit_BalanceRecordCorrect(args)
    /\ MustHold_deposit_TokenTransferred(args)

\* Monitor invariants to be checked
\* (encode the expected interpretation of monitor predicates)
Inv_MustFail_deposit(args) ==
    (   /\ tx.method_name = "deposit" 
        /\ MustFail_deposit(args)
    )   => tx.status = FALSE

Inv_MustPass_deposit(args) ==
    (   /\ tx.method_name = "deposit" 
        /\ ~MustFail_deposit(args)
        /\ MustPass_deposit(args)
    )   => tx.status = TRUE

Inv_MustHold_deposit(args) ==
    (   /\ tx.method_name = "deposit"
        /\ tx.status = TRUE
    )   => MustHold_deposit(args)


\* The main invariant
\* (formed as a conjunction of all auxiliary invariants)
\* @type: ($depositArgs) => Bool;
Inv_deposit(args) ==
    /\ Inv_MustFail_deposit(args)
    /\ Inv_MustPass_deposit(args)
    /\ Inv_MustHold_deposit(args)

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
    Inv_deposit(args)

================================================
