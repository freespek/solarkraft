(*
 * Model of Soroban environment
 * 
 * Andrey Kuprianov, 2024
 *)

---- MODULE env ----

EXTENDS Integers, Sequences, Apalache

(*
    @typeAlias: address = Str;
    @typeAlias: dataKey = Str;
*)
typedefs == TRUE

VARIABLES
    (*  Soroban's environment 
        @type: {
            current_contract_address: $address,
            ledger_timestamp: Int,
            instance_storage: Set($dataKey),
        };
    *)
    env,

    (*  Transaction metadata 
        @type: { 
            method_name: Str, 
            signatures: Set($address), 
            status: Bool 
        };
    *)
    tx


\************************
\* Authorization
\************************

\* Whether id has authorized this call
\* @type: ($address) => Bool;
authorized(id) ==
    id \in env.signatures
    \* Should be as below, but we might need to mock that as below
    \* TRUE


\************************************************************************************
\* Stellar storage layer
\* 
\* Storage generally has three types: Persistent, Instance, Temporary,
\* where each storage type is a map from a data key to data value; see here:
\* https://developers.stellar.org/docs/learn/smart-contract-internals/persisting-data
\* 
\* In TLA+ it would be difficult to maintain maps with heterogeneous values,
\* so we take a different approach: we model each contract data 
\* as a standard TLA+ variable, and maintain (for each storage type)
\* a set of data keys for variables that belong to that storage
\*
\* Initially we support only a single Instance storage type.
\************************************************************************************

\* @type: ($dataKey) => Bool;
instance_has(key) ==
    key \in env.instance_storage

\* @type: ($dataKey) => Bool;
next_instance_has(key) ==
    key \in env.instance_storage'

\* @type: ($dataKey) => Bool;
instance_set(key) ==
    env'.instance_storage = env.instance_storage \union {key}

\* @type: ($dataKey) => Bool;
instance_remove(key) ==
    env'.instance_storage = env.instance_storage \ {key}

=============================
