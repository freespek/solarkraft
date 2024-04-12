#![cfg(test)]

use super::*;
use soroban_sdk::{
    testutils::{Address as _},
    Address, Env
};

extern crate std;

#[test]
fn test() {
    let env = Env::default();
    let addr = Address::generate(&env);

    let contract_id = env.register_contract(None, MegaContract);
    // <X>Client is automagically created.
    let client = MegaContractClient::new(&env, &contract_id);

    assert!(client.get_addrs().is_empty());

    assert_eq!(client.next_val_and_save_addr(&addr),2);
    assert_eq!(client.next_val_and_save_addr(&addr),4);
    assert_eq!(client.next_val_and_save_addr(&addr),8);
    assert_eq!(client.next_val_and_save_addr(&addr),1);
    assert_eq!(client.next_val_and_save_addr(&addr),2);

    assert!(client.get_addrs().get(2u32).map_or(0, |a| a.len()) == 2);
}
