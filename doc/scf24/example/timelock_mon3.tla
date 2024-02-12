(*
 * This specification ensures that only proper claimants
 * may claim the token.
 *)
---- MODULE timelock_mon3 ----
VARIABLES
    \* @type: Set(Str);
    claimants,
    \* @type: Str;
    last_error

Deposit(env_, from_, token_, amount_, claimants_, time_bound_) ==
    \/ /\ claimants' = claimants_
       /\ last_error' = ""
    \/ /\ UNCHANGED claimants
       (*  this monitor is missing the error case of "too many claimants" *) 
       /\ last_error' \in { "contract has been already initialized" }

Claim(env, claimant) ==
    /\ \/ /\ claimant \notin claimants
          /\ UNCHANGED claimants
          /\ last_error' = "claimant is not allowed to claim this balance"
    /\ \/ /\ claimant \in claimants
          /\ claimants' = {}
          /\ last_error' \in { "", ".+" }

=============================