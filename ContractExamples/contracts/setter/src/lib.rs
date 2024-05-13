#![no_std]
use soroban_sdk::{contract, contractimpl, log, symbol_short, Env, Symbol};

const MY_BOOL: Symbol = symbol_short!("MY_BOOL");

#[contract]
pub struct SetterContract;

#[contractimpl]
impl SetterContract {
    pub fn set_bool(env: Env, v: bool) -> bool {
        let old: bool = env.storage().instance().get(&MY_BOOL).unwrap_or(false);
        env.storage().instance().set(&MY_BOOL, &v);
        log!(&env, "myBool: {}", v);
        // bump the lifetime
        env.storage().instance().extend_ttl(50, 100);
        // return the old value to the caller
        old
    }

    pub fn get_bool(env: Env) -> bool {
        return env.storage().instance().get(&MY_BOOL).unwrap_or(false);
    }
}

mod test;
