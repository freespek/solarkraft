(*
 * This specification ensures that the Timelock methods properly
 * handle initialization.
 *)
---- MODULE timelock_mon3 ----
VARIABLES
    \* @type: Bool;
    is_initialized,
    \* @type: Str;
    last_error,
    \* Bogus should not be present in the tx data, so we can test that Gen(1) gets added correctly
    \* @type: Str;
    bogus

Deposit(env, from, token, amount, claimants, time_bound) == TRUE

Claim(env, claimant) == TRUE
=============================
