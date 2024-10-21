#!/usr/bin/env bash
#
# Deploy the Xycloans contracts and populate their state with data.
#
# Thomas Pani, 2024
#
# @license
# [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)


set -e

dir=$(cd `dirname $0`; pwd -P)

cd ${dir}/../xycloans

NET=testnet
(soroban network ls | grep -q $NET) || (echo "add testnet via soroban network"; exit 1)

ADMIN=admin
soroban keys address $ADMIN || (echo "add the account $ADMIN via soroban keys generate"; exit 1)

ACCOUNT=alice
soroban keys address $ACCOUNT || (echo "add the account $ACCOUNT via soroban keys generate"; exit 1)

ACCOUNT2=bob
soroban keys address $ACCOUNT2 || (echo "add the account $ACCOUNT2 via soroban keys generate"; exit 1)

XLM_ADDRESS=CDLZFC3SYJYDZT7K67VZ75HPJVIEUVNIXF47ZG2FB2RMQQVU2HHGCYSC
BORROW_AMOUNT=1000

set -x

soroban contract build

soroban contract deploy --wasm target/wasm32-unknown-unknown/release/xycloans_factory.wasm \
      --source $ADMIN --network $NET | tee >.xycloans_factory.id
soroban contract deploy --wasm target/wasm32-unknown-unknown/release/simple.wasm \
      --source $ADMIN --network $NET | tee >.xycloans_simple.id
soroban contract install --wasm target/wasm32-unknown-unknown/release/xycloans_pool.wasm \
      --source $ADMIN --network $NET | tee >.xycloans_pool.wasmhash

# initialize the factory contract and deploy a pool
soroban contract invoke --id $(cat .xycloans_factory.id) --source $ADMIN --network $NET \
      -- initialize --pool_hash $(cat .xycloans_pool.wasmhash) --admin $ADMIN
soroban contract invoke --id $(cat .xycloans_factory.id) --source $ADMIN --network $NET \
      -- deploy_pool --token_address $XLM_ADDRESS --salt efefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefef | tr -d '"' | tee >.xycloans_pool.id

# initialize the simple receiver contract and transfer it some tokens so it can pay fees
soroban contract invoke --id $(cat .xycloans_simple.id) --source $ADMIN --network $NET \
      -- init --token_id $XLM_ADDRESS --fl_address $(cat .xycloans_pool.id) --amount $BORROW_AMOUNT
soroban contract invoke --id $XLM_ADDRESS --source $ADMIN --network $NET \
      -- transfer --from $ADMIN --to $(cat .xycloans_simple.id) --amount 10000

# deposit some tokens into the pool
soroban contract invoke --id $(cat .xycloans_pool.id) --source $ACCOUNT --network $NET \
      -- deposit --from $ACCOUNT --amount 1000
soroban contract invoke --id $(cat .xycloans_pool.id) --source $ACCOUNT2 --network $NET \
      -- deposit --from $ACCOUNT2 --amount 1

# borrow some tokens from the pool
soroban contract invoke --id $(cat .xycloans_pool.id) --source $ADMIN --network $NET \
      -- borrow --receiver_id $(cat .xycloans_simple.id) --amount $BORROW_AMOUNT

# update the fee rewards and withdraw the matured rewards
soroban contract invoke --id $(cat .xycloans_pool.id) --source $ACCOUNT2 --network $NET \
      -- update_fee_rewards --addr $ACCOUNT2
soroban contract invoke --id $(cat .xycloans_pool.id) --source $ACCOUNT2 --network $NET \
      -- withdraw_matured --addr $ACCOUNT2

cd ${dir}
