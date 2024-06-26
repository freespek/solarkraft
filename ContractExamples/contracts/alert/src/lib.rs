#![no_std]
use soroban_sdk::{contract, contractimpl, contracttype, symbol_short, Env, Symbol, Vec, String};

const ALERTS: Symbol = symbol_short!("ALERTS");

const VIOLATION: Symbol = symbol_short!("VIOLATION");
const OK: Symbol = symbol_short!("OK");
const UNKNOWN: Symbol = symbol_short!("UNKNOWN");


#[contract]
pub struct Alert;

#[contracttype]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum VerificationStatus {
    NoViolation = 0,
    Violation = 1,
    Unknown = 2
}

type AlertVec = Vec<String>;

/*
    The Alert contract gets called by `solarkraft verify`, whenever a transaction gets analyzed, if the `--alert` flag is set.
    It stores a list of all previously detected violations.

    For each tx hash, for which alert was called, stores VerificationStatus, the value of which
    depends on whether the monitor detected a violation for that transaction.
*/
#[contractimpl]
impl Alert {

    // Main entry-point. Emits and returns `status`, and stores it iff it is a violation.
    pub fn emit_and_store_violation(env: Env, tx_hash: String, status: VerificationStatus) -> VerificationStatus {
        // Get the current alerts
        let mut alerts: AlertVec = env.storage().instance().get(&ALERTS).unwrap_or(AlertVec::new(&env));

        // We always publish an event, but we only store violations.
        match status {
            VerificationStatus::NoViolation => {
                env.events().publish((ALERTS, OK), status);
            }
            VerificationStatus::Unknown => {
                env.events().publish((ALERTS, UNKNOWN), status);
            }
            VerificationStatus::Violation => {
                env.events().publish((ALERTS, VIOLATION), status);
                // Add to history and save
                alerts.push_back(tx_hash);
                env.storage().instance().set(&ALERTS, &alerts);
            }
        }    

        return status
    }

    // Returns the list of all detected violations.
    pub fn alerts(env: Env) -> AlertVec {
        return env.storage().instance().get(&ALERTS).unwrap_or(AlertVec::new(&env));
    }
}

mod test;
