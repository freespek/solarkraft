(*
 * This specification ensures that a token is properly
 * deposited and claimed.
 *)
---- MODULE timelock_mon2 ----
VARIABLES
    \* @type: Int;
    balance,
    \* @type: Str;
    last_error

Deposit(env, from, token, amount, claimants, time_bound) ==
    \/ /\ balance' = amount
       /\ last_error' = ""
    \/ /\ UNCHANGED balance
       /\ last_error' = ".+"

Claim(env, claimant) ==
    /\ \/ /\ UNCHANGED balance
          /\ last_error' \in { "", ".+" }
       \/ /\ balance' = 0
          /\ last_error' = "" 

=============================