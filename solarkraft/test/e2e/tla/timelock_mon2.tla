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
    \/ /\ balance' = balance
       /\ last_error' = "contract is not initialized"

Claim(env, claimant) ==
    \/ /\ balance' = balance
       /\ last_error' \in { "", "contract is not initialized" }
    \/ /\ balance' = 0
       /\ last_error' = ""

=============================