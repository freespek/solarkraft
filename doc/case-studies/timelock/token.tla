(*
 * SEP-41 Token interface implementation
 * Can be used to track multiple tokens
 *
 * Andrey Kuprianov, 2024
 *)

---- MODULE token ----

EXTENDS env

VARIABLES
    (*  
        @type: $address -> $address -> Int;
    *)
    token_balances


\* @type: ($address, $address) => Int;
token_balance(token, id) ==
    IF token \in DOMAIN token_balances THEN
        IF id \in DOMAIN token_balances[token] THEN
            token_balances[token][id]
        ELSE 0
    ELSE 0

\* @type: ($address, $address) => Int;
next_token_balance(token, id) ==
    IF token \in DOMAIN token_balances' THEN
        IF id \in DOMAIN token_balances'[token] THEN
            token_balances'[token][id]
        ELSE 0
    ELSE 0


\* @type: ($address, $address, $address, Int) => Bool;
token_transferred(token, from, to, amount) ==
    /\ next_token_balance(token, from) = token_balance(token, from) - amount
    /\ next_token_balance(token, to) = token_balance(token, from) + amount



================================================
