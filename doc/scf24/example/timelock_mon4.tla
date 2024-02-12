(*
 * This specification ensures that a timelock is respected.
 *)
---- MODULE timelock_mon4 ----
VARIABLES
    \* @type: { kind: Str, timestamp: Int };
    time_bound,
    \* @type: Str;
    last_error

is_within_time_bound(env) ==
    \/ time_bound.kind = "Before" /\ env.ledger.timestamp <= time_bound.timestamp
    \/ time_bound.kind = "After" /\ env.ledger.timestamp >= time_bound.timestamp

Deposit(env, from, token, amount, claimants, time_bound_) ==
    \/ /\ time_bound' = time_bound_
       /\ last_error' = ""
    \/ /\ UNCHANGED time_bound
       /\ last_error' = ".+"

Claim(env, claimant) ==
    \/ /\ ~is_within_time_bound(env)
       /\ UNCHANGED time_bound
       /\ last_error' = "time predicate is not fulfilled"
    \/ /\ is_within_time_bound(env)
       /\ UNCHANGED time_bound
       /\ last_error' \in { "", "claimant is not allowed to claim this balance" }

=============================