#![cfg(test)]
/**
 * Unit tests for Setter.
 *
 * Igor Konnov, 2024.
 *
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

use super::*;
use soroban_sdk::{
    testutils::Address as _,
    Address, Env
};

extern crate std;

#[test]
fn test() {
    let env = Env::default();
    let addr = Address::generate(&env);

    let contract_id = env.register_contract(None, SetterContract);
    // <X>Client is automagically created.
    let client = SetterContractClient::new(&env, &contract_id);

    assert_eq!(client.get_bool(), false);
    assert_eq!(client.set_bool(&true), false);
    assert_eq!(client.get_bool(), true);

    assert_eq!(client.get_u32(), 0u32);
    assert_eq!(client.set_u32(&42u32), 0);
    assert_eq!(client.get_u32(), 42);

    assert_eq!(client.get_i32(), 0i32);
    assert_eq!(client.set_i32(&42i32), 0);
    assert_eq!(client.get_i32(), 42);

    assert_eq!(client.get_u64(), 0u64);
    assert_eq!(client.set_u64(&42u64), 0);
    assert_eq!(client.get_u64(), 42);

    assert_eq!(client.get_i64(), 0i64);
    assert_eq!(client.set_i64(&42i64), 0);
    assert_eq!(client.get_i64(), 42);

    assert_eq!(client.get_u128(), 0u128);
    assert_eq!(client.set_u128(&42u128), 0);
    assert_eq!(client.get_u128(), 42);

    assert_eq!(client.get_i128(), 0i128);
    assert_eq!(client.set_i128(&42i128), 0);
    assert_eq!(client.get_i128(), 42);

    client.set_sym(&symbol_short!("FOO"));
    assert_eq!(client.get_sym(), symbol_short!("FOO"));

    client.set_bytes(&Bytes::from_array(&env, &[ 1u8, 2u8, 3u8]));
    assert_eq!(client.get_bytes(), Bytes::from_array(&env, &[ 1u8, 2u8, 3u8]));

    let bytes32: BytesN<32> = BytesN::from_array(&env, &[
            1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8, 9u8, 10u8, 11u8, 12u8, 13u8,
            14u8, 15u8, 16u8, 17u8, 18u8, 19u8, 20u8, 21u8, 22u8, 23u8, 24u8, 25u8,
            26u8, 27u8, 28u8, 29u8, 30u8, 31u8, 32u8
        ]);
    client.set_bytes32(&bytes32);
    assert_eq!(client.get_bytes32(), bytes32);

    client.map_set(&2, &3);
    client.map_set(&5, &6);

    assert_eq!(client.map_get(&2), 3);
    assert_eq!(client.map_get(&5), 6);
    assert_eq!(client.map_get(&7), 0);

    client.set_map(&Map::from_array(&env, [(3u32, 4i32), (6u32, 8i32)]));
    assert_eq!(client.map_get(&2), 0);
    assert_eq!(client.map_get(&3), 4);
    assert_eq!(client.map_get(&5), 0);
    assert_eq!(client.map_get(&6), 8);
    assert_eq!(client.map_get(&7), 0);

    client.vec_push(&2);
    client.vec_push(&3);
    client.vec_push(&4);

    assert_eq!(client.get_vec(), vec![&env, 2, 3, 4]);

    client.set_vec(&vec![&env, 5, 6, 7]);
    assert_eq!(client.get_vec(), vec![&env, 5, 6, 7]);

    client.set_address(&addr);
    assert_eq!(client.get_address(), Some(addr.clone()));

    client.set_my_struct(&MyStruct { a: 3u32, b: 4i128 });
    assert_eq!(client.get_my_struct(), MyStruct { a: 3u32, b: 4i128 });

    client.set_enum(&MyEnum::A(14u32));
    assert_eq!(client.get_enum(), MyEnum::A(14u32));

    client.set_enum(&MyEnum::B(14, -10));
    assert_eq!(client.get_enum(), MyEnum::B(14, -10));
}
