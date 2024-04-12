#![no_std]
use soroban_sdk::{contract, contractimpl, log, symbol_short, Env, Symbol, Vec, Map, Address};

const VAL: Symbol = symbol_short!("VAL");

// For each value of VAL, stores a vector of addresses, for which that
// value was generated by `next_val_and_save_addr`
const ADDRS: Symbol = symbol_short!("ADDRS");

#[contract]
pub struct MegaContract;

type AddrMap = Map<u32, Vec<Address>>;

#[contractimpl]
impl MegaContract {
    // Moves to the next value of `VAL` looping 1, 2, 4, 8, 1, 2, ...
    // after updating `VAL`, adds `addr` to `ADDRS[VAL]`.
    pub fn next_val_and_save_addr(env: Env, addr: Address) -> u32 {
        // Get the current val.
        let mut val: u32 = env.storage().instance().get(&VAL).unwrap_or(1); // If no value set, assume 1.
        log!(&env, "val: {}", val);

        // If val < 5, double, else set to 1
        val = if val < 5 { 2 * val } else { 1 };

        // Save val.
        env.storage().instance().set(&VAL, &val);

        // Save the caller, for the current counter value
        let mut addrs: AddrMap = env.storage().instance().get(&ADDRS).unwrap_or(AddrMap::new(&env));

        let mut new_vec = addrs.get(val).unwrap_or(Vec::new(&env));
        new_vec.push_back(addr);

        addrs.set(val, new_vec);

        // Save addrs.
        env.storage().instance().set(&ADDRS, &addrs);

        // The contract instance will be bumped to have a lifetime of at least 100 ledgers if the current expiration lifetime at most 50.
        // If the lifetime is already more than 100 ledgers, this is a no-op. Otherwise,
        // the lifetime is extended to 100 ledgers. This lifetime bump includes the contract
        // instance itself and all entries in storage().instance(), i.e, COUNTER.
        env.storage().instance().extend_ttl(50, 100);

        // Return val to the caller.
        val
    }

    pub fn get_addrs(env: Env) -> AddrMap {
        return env.storage().instance().get(&ADDRS).unwrap_or(AddrMap::new(&env));
    }
}

mod test;
