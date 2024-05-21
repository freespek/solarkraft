#![no_std]
use soroban_sdk::{contract, contractimpl, contracttype, symbol_short, Env, Symbol, Map, String};

const ALERTS: Symbol = symbol_short!("ALERTS");
const VIOLATION: Symbol = symbol_short!("VIOLATION");

#[contract]
pub struct Alert;

#[contracttype]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum MonitorAnalysisStatus {
    NoViolation = 0,
    Violation = 1,
    Unknown = 2
}

type AlertMap = Map<String, MonitorAnalysisStatus>;

/*
    The Alert contract gets called by the monitor executor, whenever a transaction gets analyzed.
    If the monitor detected a property violation, then the Alert contract emits a warning.

    For each tx hash, for which alert was called, stores MonitorAnalysisStatus, the value of which
    depends on whether the monitor detected a violation for that transaction.
*/
#[contractimpl]
impl Alert {

    pub fn emit_warning_if_violation(env: Env, tx_hash: String, status: MonitorAnalysisStatus) -> MonitorAnalysisStatus {
        // Get the current alerts
        let mut alerts: AlertMap = env.storage().instance().get(&ALERTS).unwrap_or(AlertMap::new(&env));

        // Add to history and save
        alerts.set(tx_hash, status);
        env.storage().instance().set(&ALERTS, &alerts);

        // The contract instance will be bumped to have a lifetime of at least 100 ledgers if the current expiration lifetime at most 50.
        // If the lifetime is already more than 100 ledgers, this is a no-op. Otherwise,
        // the lifetime is extended to 100 ledgers. This lifetime bump includes the contract
        // instance itself and all entries in storage().instance().
        env.storage().instance().extend_ttl(50, 100);

        // If there is a violation, emit an event.
        if status == MonitorAnalysisStatus::Violation {
            env.events().publish((ALERTS, VIOLATION), status);
        }

        return status
    }
}

mod test;
