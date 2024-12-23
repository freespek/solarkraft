#![cfg(test)]

use super::*;
use soroban_sdk::{
    testutils::{Events as _},
    Env, vec, IntoVal
};

#[test]
fn test_ok() {
    let env = Env::default();
    let tx_hash: String = String::from_str(&env, "txhash");

    let contract_id = env.register(Alert, ());
    // <X>Client is automagically created.
    let client = AlertClient::new(&env, &contract_id);

    assert_eq!(client.emit_and_store_violation(&tx_hash, &VerificationStatus::NoViolation), VerificationStatus::NoViolation);
    // NoViolation triggers an emit but no store
    assert_eq!(
        env.events().all(),
        vec![&env, (contract_id.clone(),(ALERTS, OK).into_val(&env), VerificationStatus::NoViolation.into_val(&env))]
    );

    // should be empty
    let alerts = client.alerts();
    assert!(alerts.is_empty());
}

#[test]
fn test_violation() {
    let env = Env::default();
    let tx_hash: String = String::from_str(&env, "txhash");

    let contract_id = env.register(Alert, ());
    // <X>Client is automagically created.
    let client = AlertClient::new(&env, &contract_id);

    // Violation triggers an emit and a store
    assert_eq!(client.emit_and_store_violation(&tx_hash, &VerificationStatus::Violation), VerificationStatus::Violation);
    assert_eq!(
        env.events().all(),
        vec![&env, 
            (contract_id.clone(),(ALERTS, VIOLATION).into_val(&env), VerificationStatus::Violation.into_val(&env))
        ]
    );

    let alerts2 = client.alerts();
    assert_eq!(alerts2, vec![&env, tx_hash]);
}
