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