(*
 * Typedefs and variables for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE timelock ----

EXTENDS env, token

(*
    @typeAlias: timeBoundKind = Str;
    @typeAlias: timeBound = { kind: $timeBoundKind, timestamp: Int };

*)
module_typedefs == TRUE

VARIABLES
    (*  ClaimableBalance
        @type: { 
            token: $address,
            amount: Int,
            claimants: Seq($address),
            time_bound: $timeBound
        };
    *)
    Balance

================================================
