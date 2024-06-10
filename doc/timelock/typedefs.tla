(*
 * Soroban environment type specification
 * 
 * Andrey Kuprianov, Jure Kukovec, 2024
 *)

---- MODULE typedefs ----

(*
    @typeAlias: timeBoundKind = Before(UNIT) | After(UNIT);
    @typeAlias: timeBound = { kind: $timeBoundKind, timestamp: Int };
    @typeAlias: address = Str;
    @typeAlias: storageKey = Str;
    @typeAlias: env = {
        current_contract_address: $address,
        timestamp: Int,
        sequence: Int,
        invoked_function_name: Str,
        storage_before: Set($storageKey),
        storage_after: Set($storageKey)
    };
*)
typedefs == TRUE

================================================
