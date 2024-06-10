(*
 * Variables for the Timelock contract, and `env` pseudostate management
 *
 * Modeled from https://github.com/stellar/soroban-examples/blob/v20.0.0/timelock/src/lib.rs
 *
 * Andrey Kuprianov, Jure Kukovec, 2024
 *)
---- MODULE state ----

EXTENDS Integers, Sequences, Apalache, typedefs

VARIABLES
    (*  
        @type: { 
            token: $address,
            amount: Int,
            claimants: Seq($address),
            time_bound: $timeBound
        };
    *)
    Balance
    \* Even though the original contract declares a storage variable "Init", it is only used to 
    \* check whether or not it was set once at any point.
    \* We can use (next_)instance_has from env to check for that

\************************
\* Authorization
\************************

\* Whether id has authorized this call
\* @type: ($address, $env) => Bool;
authorized(id, env) ==
    \* Signature checking is not implemented yet, see #85
    TRUE


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

\* @type: ($storageKey, $env) => Bool;
instance_has(key, env) ==
    key \in env.storage_before

\* @type: ($storageKey, $env) => Bool;
next_instance_has(key, env) ==
    key \in env.storage_after

\* @type: ($storageKey, $env) => Bool;
instance_set(key, env) ==
    env.storage_after \ env.storage_before = {key}

\* @type: ($storageKey, $env) => Bool;
instance_remove(key, env) ==
    env.storage_before \ env.storage_after = {key}

================================================
