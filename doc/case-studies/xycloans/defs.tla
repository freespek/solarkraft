------------------------------ MODULE defs ------------------------------------
(*
 * Common definitions for the xycloans contract.
 *)
EXTENDS Integers, xycloans_types

\* @type: ($tx, Bool) => Bool;
reverts_if(tx, cond) == cond => ~tx.status
\* @type: ($tx, Bool) => Bool;
succeeds_with(tx, cond) == tx.status => cond
\* @type: (Str -> a, Str, a) => a;
get_or_else(map, key, default) ==
    IF key \in DOMAIN map THEN map[key] ELSE default
\* integer division with rounding up
div_ceil(a, b) == (a + (b - 1)) \div b
\* integer division with rounding down
div_floor(a, b) == a \div b
\* @type: ($env, Str) => Int;
token_balance(env, a) == get_or_else(env.storage.token_persistent.Balance, a, 0)
\* @type: ($env, Str) => Int;
old_token_balance(env, a) == get_or_else(env.old_storage.token_persistent.Balance, a, 0)

===============================================================================