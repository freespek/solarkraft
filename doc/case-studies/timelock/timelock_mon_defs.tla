(*
 * Definitions for monitor specification for the Timelock contract
 *
 * Andrey Kuprianov, 2024
 *)
---- MODULE timelock_mon_defs ----

EXTENDS env, token

(*
    @typeAlias: timeBoundKind = Str;
    @typeAlias: timeBound = { kind: $timeBoundKind, timestamp: Int };

*)
module_typedefs == TRUE


VARIABLES
    (*  Arguments for contract methods
        @type: { 
            // deposit args
            from: $address,
            token: $address,
            amount: Int,
            claimants: Seq($address),
            time_bound: $timeBound,
            // claim args
            claimant: $address
        };
    *)
    args,

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
