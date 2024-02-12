# A simple manual demo with Timelock

In this demo, we are using the [timelock][] contract as an example.  We do not
have an actual implementation of Solarkraft yet. Hence, we are manually
producing the verification steps that will be done by Solarkraft automatically
in the future.

We have written four monitors that capture various aspects of the smart contract:

 - [timelock_mon1.tla][] checks, whether the contract is initialized properly.
 - [timelock_mon2.tla][] checks, whether the contract balance is changing properly.
 - [timelock_mon3.tla][] checks, whether the `claimants` argument is respected.
 - [timelock_mon4.tla][] checks, whether the time bound is respected.

## 1. Setting up the dev environment

Follow the [setup][] guidelines from the Soroban tutorial.

After installing all the packages, we have generated one identity:

```sh
soroban config identity generate --global alice
```

## 2. Installing the timelock contract

Assuming that you have cloned [soroban-examples][] into `$EXAMPLES_HOME`,
do the following:

```sh
$ cd $EXAMPLES_HOME/timelock
$ soroban contract deploy \
  --wasm target/wasm32-unknown-unknown/release/soroban_timelock_contract.wasm \
  --source alice \
  --network testnet | tee .soroban/timelock-id
```

Make sure that the command output contains no errors but a contract id that
looks similar to the one below:

```
CC2SFVF5CWKUDLAQ2DT6OAYWA5DVEMLNWGPFCKIH6BK7GSVFSADX2TIX
```

## 3. Invoking an erroneous transaction

To illustrate the future workflow of Solakraft, we manually invoke the following
transaction, which fails in the simulation phase:

```sh
$ soroban contract invoke --id $(cat .soroban/timelock-id) \
  --source alice --network testnet --  claim --claimant alice
...
ERROR soroban_cli::log::diagnostic_event: 0: ...
error: transaction simulation failed: host invocation failed

Caused by:
    ...
    Event log (newest first):
       0: [Diagnostic Event] contract:b522d4bd159541ac10d0e7e70316074752316db19e512907f055f34aa590077d, topics:[error, Error(WasmVm, InvalidAction)], data:["VM call trapped: UnreachableCodeReached", claim]
```

## 4. Instrumenting the monitor

To check the above transaction, Solakraft will instrument the monitor
specification [timelock_mon1.tla][]:

```tla
---- MODULE timelock_mon1_instrumented ----
EXTENDS timelock_mon1

Init ==
    (* is_initialized is initialized from the current ledger state *)
    /\ is_initialized = FALSE
    /\ last_error = ""

Next ==
    (* the contract method being called along with its parameters *)
    /\ Claim([ timestamp |-> 100 ], "alice")
    (* the error message as produced by the contract invocation *)
    /\ last_error' = "transaction simulation failed: host invocation failed"
===========================================
```

In essense, the instrumented specification instantiates the general monitor to
the concrete parameters passed in the transaction as well as to the returned
result (that is, `last_error`). If the monitor admits the transaction, then the
state machine should be able to make a single step as defined by `Next` from the
initial state, as defined by `Init`.

## 5. Checking the instrumented specification

Having produced the [instrumented specification][], Solakraft will invoke Apalache
to check feasibility of the instrumented specification. Solarkraft will do that
via the Apalache server mode. For illustration purposes, we invoke the same
check manually:

```sh
$ apalache-mc check timelock_mon1_instrumented.tla
...
The outcome is: Deadlock
```

Apalache has reported a deadlock. This means that the monitor is not able to
reproduce the step invoked by the contract. If look at the monitor specification,
it indeed does not admit the error message that was produced by the contract:

```tla
Claim(env, claimant) ==
    \/ /\ ~is_initialized
       /\ UNCHANGED is_initialized
       (* the contract simply panics instead of reporting a nice error *)
       /\ last_error' = "contract is not initialized"
    \/ /\ is_initialized
       ...
```

Whereas our monitor has expected the error message `"contract is not
initialized"`, the contract has panicked with a low-level error message.


[timelock]: https://github.com/stellar/soroban-examples/blob/v20.0.0/timelock/src/lib.rs
[setup]: https://github.com/stellar/soroban-examples/blob/v20.0.0/timelock/src/lib.rs
[soroban-examples]: https://github.com/stellar/soroban-examples/tree/v20.0.0
[Apalache manual]: https://apalache.informal.systems/docs/apalache/index.html
[timelock_mon1.tla]: ./timelock_mon1.tla
[timelock_mon1_instrumented.tla]: ./timelock_mon1_instrumented.tla
[instrumented specification]: ./timelock_mon1_instrumented.tla
[timelock_mon2.tla]: ./timelock_mon2.tla
[timelock_mon3.tla]: ./timelock_mon3.tla
[timelock_mon4.tla]: ./timelock_mon4.tla