(*
 * This specification ensures that the Timelock methods properly
 * handle initialization.
 *)
---- MODULE timelock_mon1 ----
VARIABLES
    \* @type: Bool;
    is_initialized,
    \* @type: Str;
    last_error

Deposit(env, from, token, amount, claimants, time_bound) ==
    \/ /\ ~is_initialized
       /\ is_initialized' = TRUE
       /\ last_error' = ""
    \/ /\ is_initialized
       /\ UNCHANGED is_initialized
       /\ last_error' = "contract has been already initialized"

Claim(env, claimant) ==
    \/ /\ ~is_initialized
       /\ UNCHANGED is_initialized
       (* the contract simply panics instead of reporting a nice error *)
       /\ last_error' = "contract is not initialized"
    \/ /\ is_initialized
       /\ UNCHANGED is_initialized
       /\ last_error' \in {
            "",
            "time predicate is not fulfilled",
            "claimant is not allowed to claim this balance"
          }
    (* the below behavior is not present in the contract *)
    \/ /\ is_initialized
       /\ is_initialized' = FALSE
       /\ last_error' = "" 
=============================
