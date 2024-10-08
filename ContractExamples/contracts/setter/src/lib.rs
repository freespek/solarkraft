#![no_std]
/**
 * A test contract for better understanding of the ledger layout of Soroban contracts.
 *
 * Igor Konnov, 2024.
 *
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
use soroban_sdk::{
    bytes, bytesn, contract, contractimpl, contracttype, log, symbol_short, vec, Address, Bytes,
    BytesN, Env, Map, String, Symbol, Vec,
};

// scalar types
const MY_BOOL: Symbol = symbol_short!("MY_BOOL");
const MY_U32: Symbol = symbol_short!("MY_U32");
const MY_I32: Symbol = symbol_short!("MY_I32");
const MY_U64: Symbol = symbol_short!("MY_U64");
const MY_I64: Symbol = symbol_short!("MY_I64");
const MY_U128: Symbol = symbol_short!("MY_U128");
const MY_I128: Symbol = symbol_short!("MY_I128");
const MY_SYM: Symbol = symbol_short!("MY_SYM");

// aggregate types
const MY_BYTES: Symbol = symbol_short!("MY_BYTES");
const MY_BYTES32: Symbol = symbol_short!("MY_BTES32");
const MY_VEC: Symbol = symbol_short!("MY_VEC");
const MY_MAP: Symbol = symbol_short!("MY_MAP");
const MY_ADDR: Symbol = symbol_short!("MY_ADDR");
const MY_STRUCT: Symbol = symbol_short!("MY_STRUCT");
const MY_ENUM: Symbol = symbol_short!("MY_ENUM");

/**
 * A simple two-field structure.
 */
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MyStruct {
    pub a: u32,
    pub b: i128,
}

/**
 * A simple enum.
 */
#[contracttype]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MyEnum {
    A(u32),
    B(i128),
}

#[contract]
pub struct SetterContract;

/**
 * A test contract to try all kinds of types enumerated in:
 *
 * https://developers.stellar.org/docs/learn/smart-contract-internals/types/built-in-types
 */
#[contractimpl]
impl SetterContract {
    pub fn init(env: Env) {
        let zero_u32: u32 = 0;
        let zero_i32: i32 = 0;
        let zero_u64: u64 = 0;
        let zero_i64: i64 = 0;
        let zero_u128: u128 = 0;
        let zero_i128: i128 = 0;
        let init_str: String = String::from_str(&env, "CCLCX5GS3NRUHDLKFBTHWT5CD5US5BUNWCX6H2BN3RKXMVUZMYRXJLBT");
        let init_addr: Address = Address::from_string(&init_str);
        let zero_bytes: Bytes = bytes!(&env, 0x0);
        let init_bytes32: BytesN<32> = bytesn!(&env, 0xfded3f55dec47250a52a8c0bb7038e72fa6ffaae33562f77cd2b629ef7fd424d);
        let zero_enum: MyEnum = MyEnum::A(0u32);
        let zero_struct: MyStruct = MyStruct { a: 0u32, b: 0i128 };
        env.storage().instance().set(&MY_BOOL, &false);
        env.storage().instance().set(&MY_U32, &zero_u32);
        env.storage().instance().set(&MY_I32, &zero_i32);
        env.storage().instance().set(&MY_U64, &zero_u64);
        env.storage().instance().set(&MY_I64, &zero_i64);
        env.storage().instance().set(&MY_U128, &zero_u128);
        env.storage().instance().set(&MY_I128, &zero_i128);
        env.storage().instance().set(&MY_SYM, &symbol_short!(""));
        env.storage().instance().set(&MY_ADDR, &init_addr);
        env.storage().instance().set(&MY_BYTES, &zero_bytes);
        env.storage().instance().set(&MY_BYTES32, &init_bytes32);
        env.storage().instance().set(&MY_VEC, &Vec::<u128>::new(&env));
        env.storage().instance().set(&MY_MAP, &Map::<String, u128>::new(&env));
        env.storage().instance().set(&MY_ENUM, &zero_enum);
        env.storage().instance().set(&MY_STRUCT, &zero_struct);
    }

    pub fn set_bool(env: Env, v: bool) -> bool {
        let old: bool = env.storage().instance().get(&MY_BOOL).unwrap_or(false);
        env.storage().instance().set(&MY_BOOL, &v);
        env.storage().temporary().set(&MY_BOOL, &v);
        env.storage().persistent().set(&MY_BOOL, &v);
        log!(&env, "myBool: {}", v);
        // bump the lifetime
        // https://developers.stellar.org/docs/learn/smart-contract-internals/state-archival
        //
        // The TTL is extended to `max_ttl` when field TTL goes below `max_ttl` - 100
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_bool(env: Env) -> bool {
        env.storage().instance().get(&MY_BOOL).unwrap_or(false)
    }

    pub fn remove_bool(env: Env) -> bool {
        let old: bool = env.storage().instance().get(&MY_BOOL).unwrap_or(false);
        env.storage().instance().remove(&MY_BOOL);
        env.storage().temporary().remove(&MY_BOOL);
        env.storage().persistent().remove(&MY_BOOL);
        old
    }

    pub fn set_bool_if_notset(env: Env) {
        if env.storage().instance().has(&MY_BOOL) {
            panic!("already set");
        }
        env.storage().instance().set(&MY_BOOL, &true);
    }

    pub fn set_u32(env: Env, v: u32) -> u32 {
        let old: u32 = env.storage().instance().get(&MY_U32).unwrap_or(0);
        env.storage().instance().set(&MY_U32, &v);
        env.storage().temporary().set(&MY_U32, &v);
        env.storage().persistent().set(&MY_U32, &v);
        log!(&env, "myU32: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_u32(env: Env) -> u32 {
        env.storage().instance().get(&MY_U32).unwrap_or(0)
    }

    pub fn set_i32(env: Env, v: i32) -> i32 {
        let old: i32 = env.storage().instance().get(&MY_I32).unwrap_or(0);
        env.storage().instance().set(&MY_I32, &v);
        env.storage().temporary().set(&MY_I32, &v);
        env.storage().persistent().set(&MY_I32, &v);
        log!(&env, "myI32: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_i32(env: Env) -> i32 {
        env.storage().instance().get(&MY_I32).unwrap_or(0)
    }

    pub fn set_u64(env: Env, v: u64) -> u64 {
        let old: u64 = env.storage().instance().get(&MY_U64).unwrap_or(0);
        env.storage().instance().set(&MY_U64, &v);
        env.storage().temporary().set(&MY_U64, &v);
        env.storage().persistent().set(&MY_U64, &v);
        log!(&env, "myU64: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_u64(env: Env) -> u64 {
        env.storage().instance().get(&MY_U64).unwrap_or(0)
    }

    pub fn set_i64(env: Env, v: i64) -> i64 {
        let old: i64 = env.storage().instance().get(&MY_I64).unwrap_or(0);
        env.storage().instance().set(&MY_I64, &v);
        env.storage().temporary().set(&MY_I64, &v);
        env.storage().persistent().set(&MY_I64, &v);
        log!(&env, "myi64: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_i64(env: Env) -> i64 {
        env.storage().instance().get(&MY_I64).unwrap_or(0)
    }

    pub fn set_u128(env: Env, v: u128) -> u128 {
        let old: u128 = env.storage().instance().get(&MY_U128).unwrap_or(0);
        env.storage().instance().set(&MY_U128, &v);
        env.storage().temporary().set(&MY_U128, &v);
        env.storage().persistent().set(&MY_U128, &v);
        log!(&env, "myU128: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_u128(env: Env) -> u128 {
        env.storage().instance().get(&MY_U128).unwrap_or(0)
    }

    pub fn set_i128(env: Env, v: i128) -> i128 {
        let old: i128 = env.storage().instance().get(&MY_I128).unwrap_or(0);
        env.storage().instance().set(&MY_I128, &v);
        env.storage().temporary().set(&MY_I128, &v);
        env.storage().persistent().set(&MY_I128, &v);
        log!(&env, "myi128: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_i128(env: Env) -> i128 {
        env.storage().instance().get(&MY_I128).unwrap_or(0)
    }

    pub fn set_sym(env: Env, v: Symbol) -> Symbol {
        let old: Symbol = env
            .storage()
            .instance()
            .get(&MY_SYM)
            .unwrap_or(symbol_short!("NONE"));
        env.storage().instance().set(&MY_SYM, &v);
        env.storage().temporary().set(&MY_SYM, &v);
        env.storage().persistent().set(&MY_SYM, &v);
        log!(&env, "mySym: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
        // return the old value to the caller
        old
    }

    pub fn get_sym(env: Env) -> Symbol {
        env.storage()
            .instance()
            .get(&MY_SYM)
            .unwrap_or(symbol_short!("NONE"))
    }

    pub fn set_bytes(env: Env, v: Bytes) -> () {
        env.storage().instance().set(&MY_BYTES, &v);
        env.storage().temporary().set(&MY_BYTES, &v);
        env.storage().persistent().set(&MY_BYTES, &v);
        log!(&env, "myBytes: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    pub fn get_bytes(env: Env) -> Bytes {
        env.storage()
            .instance()
            .get(&MY_BYTES)
            .unwrap_or(Bytes::new(&env))
    }

    pub fn set_bytes32(env: Env, v: BytesN<32>) -> () {
        env.storage().instance().set(&MY_BYTES32, &v);
        env.storage().temporary().set(&MY_BYTES32, &v);
        env.storage().persistent().set(&MY_BYTES32, &v);
        log!(&env, "myBytes32: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    pub fn get_bytes32(env: Env) -> BytesN<32> {
        env.storage()
            .instance()
            .get(&MY_BYTES32)
            .unwrap_or(BytesN::from_array(&env, &[0u8; 32]))
    }

    pub fn set_vec(env: Env, v: Vec<i32>) -> () {
        env.storage().instance().set(&MY_VEC, &v);
        env.storage().temporary().set(&MY_VEC, &v);
        env.storage().persistent().set(&MY_VEC, &v);
        log!(&env, "myVec: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    fn get_vec_internal(env: &Env) -> Vec<i32> {
        env.storage().instance().get(&MY_VEC).unwrap_or(vec![&env])
    }

    pub fn get_vec(env: Env) -> Vec<i32> {
        Self::get_vec_internal(&env)
    }

    pub fn vec_push(env: Env, i: i32) {
        let mut vs = Self::get_vec_internal(&env);
        vs.push_back(i);
        env.storage().instance().set(&MY_VEC, &vs);
        env.storage().temporary().set(&MY_VEC, &vs);
        env.storage().persistent().set(&MY_VEC, &vs);
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    pub fn set_map(env: Env, v: Map<u32, i32>) -> () {
        env.storage().instance().set(&MY_MAP, &v);
        env.storage().temporary().set(&MY_MAP, &v);
        env.storage().persistent().set(&MY_MAP, &v);
        log!(&env, "myMap: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    fn get_map_internal(env: &Env) -> Map<u32, i32> {
        env.storage()
            .instance()
            .get(&MY_MAP)
            .unwrap_or(Map::from_array(&env, [(0, 0); 0]))
    }

    pub fn get_map(env: Env) -> Map<u32, i32> {
        Self::get_map_internal(&env)
    }

    pub fn map_set(env: Env, key: u32, value: i32) {
        let mut map = Self::get_map_internal(&env);
        map.set(key, value);
        env.storage().instance().set(&MY_MAP, &map);
        env.storage().temporary().set(&MY_MAP, &map);
        env.storage().persistent().set(&MY_MAP, &map);
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    pub fn map_get(env: Env, key: u32) -> i32 {
        Self::get_map_internal(&env).get(key).unwrap_or(0i32)
    }

    pub fn set_address(env: Env, v: Address) -> () {
        env.storage().instance().set(&MY_ADDR, &v);
        env.storage().temporary().set(&MY_ADDR, &v);
        env.storage().persistent().set(&MY_ADDR, &v);
        log!(&env, "myAddress: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    pub fn get_address(env: Env) -> Option<Address> {
        env.storage().instance().get(&MY_ADDR)
    }

    pub fn set_struct(env: Env, v: MyStruct) -> () {
        env.storage().instance().set(&MY_STRUCT, &v);
        env.storage().temporary().set(&MY_STRUCT, &v);
        env.storage().persistent().set(&MY_STRUCT, &v);
        log!(&env, "myStruct: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    pub fn get_struct(env: Env) -> MyStruct {
        env.storage()
            .instance()
            .get(&MY_STRUCT)
            .unwrap_or(MyStruct { a: 0u32, b: 0i128 })
    }

    pub fn set_enum(env: Env, v: MyEnum) -> () {
        env.storage().instance().set(&MY_ENUM, &v);
        env.storage().temporary().set(&MY_ENUM, &v);
        env.storage().persistent().set(&MY_ENUM, &v);
        log!(&env, "myEnum: {}", v);
        // bump the lifetime
        env.storage()
            .instance()
            .extend_ttl(env.storage().max_ttl() - 100, env.storage().max_ttl());
    }

    pub fn get_enum(env: Env) -> MyEnum {
        env.storage()
            .instance()
            .get(&MY_ENUM)
            .unwrap_or(MyEnum::A(0u32))
    }
}

mod test;
