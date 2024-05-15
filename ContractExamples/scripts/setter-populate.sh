#!/usr/bin/env bash
#
# Deploy the setter contract and populate its state with data.
#
# Igor Konnov, 2024
#
# @license
# [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)


set -e

dir=$(cd `dirname $0`; pwd -P)

cd ${dir}/..

set -x

soroban contract build
soroban contract deploy --wasm target/wasm32-unknown-unknown/release/setter.wasm \
      --source alice --network testnet | tee >.setter.id

soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_bool --v true
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_u32 --v 42
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_i32 --v -42
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_u64 --v 42
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_i64 --v -42
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_u128 --v 42
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_i128 --v -42
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_sym --v hello
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_bytes --v beef
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_bytes32 --v beef0123456789beef0123456789beef0123456789ab
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_vec --v '[ 1, -2, 3 ]'
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_map --v '{ "2": 3, "4": 5 }'
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_address --v GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_my_struct --v '{ "a": 1, "b": "-100" }'
soroban contract invoke --id $(cat .setter.id) --source alice --network testnet \
      -- set_my_enum --v A