(*
 * Model of Soroban environment
 * 
 * Andrey Kuprianov, 2024
 *)

---- MODULE env ----

EXTENDS typedefs

VARIABLES
    (*  Soroban's environment 
        @type: { 
            current_contract_address: $address,
            ledger_timestamp: Int,
            method_name: Str
        };
    *)
    env


\************************
\* Authorization
\************************

VARIABLES

    (*  Addresses that have authorized the current method call
        @type: Set($address);
    *)
    signatures

\* Whether id has authorized this call
\* @type: ($address) => Bool;
authorized(id) ==
    TRUE
    \* Should be as below, but we mock that for the time being
    \* id \in signatures


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
VARIABLES
    (*  
        @type: Set($dataKey);
    *)
    instance_storage

\* @type: ($dataKey) => Bool;
instance_has(key) ==
    key \in instance_storage

\* @type: ($dataKey) => Bool;
next_instance_has(key) ==
    key \in instance_storage'

\* @type: ($dataKey) => Bool;
instance_set(key) ==
    instance_storage' = instance_storage \union {key}

\* @type: ($dataKey) => Bool;
instance_remove(key) ==
    instance_storage' = instance_storage \ {key}

=============================
