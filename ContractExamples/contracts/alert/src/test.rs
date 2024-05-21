#![cfg(test)]

use super::*;
use soroban_sdk::{
    testutils::{Events as _},
    Env, vec, IntoVal
};

extern crate std;

#[test]
fn test() {
    let env = Env::default();
    let tx_hash: String = String::from_str(&env, "txhash");

    let contract_id = env.register_contract(None, Alert);
    // <X>Client is automagically created.
    let client = AlertClient::new(&env, &contract_id);


    assert_eq!(client.emit_warning_if_violation(&tx_hash, &MonitorAnalysisStatus::NoViolation), MonitorAnalysisStatus::NoViolation);
    // NoViolation triggers no emits -> events is empty
    assert_eq!(
        env.events().all(),
        vec![&env]
    );

    assert_eq!(client.emit_warning_if_violation(&tx_hash, &MonitorAnalysisStatus::Violation), MonitorAnalysisStatus::Violation);
    // // Violation emits
    assert_eq!(
        env.events().all(),
        vec![&env, (contract_id.clone(),(ALERTS, VIOLATION).into_val(&env),MonitorAnalysisStatus::Violation.into_val(&env))]
    );
}
