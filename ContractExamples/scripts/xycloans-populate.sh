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
(stellar network ls | grep -q $NET) || (echo "add testnet via stellar network"; exit 1)

ADMIN=admin
stellar keys address $ADMIN || (echo "add the account $ADMIN via stellar keys generate"; exit 1)

ALICE=alice
stellar keys address $ALICE || (echo "add the account $ALICE via stellar keys generate"; exit 1)

BOB=bob
stellar keys address $BOB || (echo "add the account $BOB via stellar keys generate"; exit 1)

XLM_ADDRESS=CDLZFC3SYJYDZT7K67VZ75HPJVIEUVNIXF47ZG2FB2RMQQVU2HHGCYSC
BORROW_AMOUNT=1000

set -x

stellar contract build

stellar contract deploy --wasm target/wasm32-unknown-unknown/release/xycloans_factory.wasm \
      --source $ADMIN --network $NET | tee >.xycloans_factory.id
stellar contract deploy --wasm target/wasm32-unknown-unknown/release/simple.wasm \
      --source $ADMIN --network $NET | tee >.xycloans_simple.id
stellar contract install --wasm target/wasm32-unknown-unknown/release/xycloans_pool.wasm \
      --source $ADMIN --network $NET | tee >.xycloans_pool.wasmhash

# initialize the factory contract and deploy a pool
stellar contract invoke --id $(cat .xycloans_factory.id) --source $ADMIN --network $NET \
      -- initialize --pool_hash $(cat .xycloans_pool.wasmhash) --admin $ADMIN
stellar contract invoke --id $(cat .xycloans_factory.id) --source $ADMIN --network $NET \
      -- deploy_pool --token_address $XLM_ADDRESS --salt efefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefef | tr -d '"' | tee >.xycloans_pool.id

# initialize the simple receiver contract and transfer it some tokens so it can pay fees
stellar contract invoke --id $(cat .xycloans_simple.id) --source $ADMIN --network $NET \
      -- init --token_id $XLM_ADDRESS --fl_address $(cat .xycloans_pool.id) --amount $BORROW_AMOUNT
stellar contract invoke --id $XLM_ADDRESS --source $ADMIN --network $NET \
      -- transfer --from $ADMIN --to $(cat .xycloans_simple.id) --amount 10000

# deposit some tokens into the pool
stellar contract invoke --id $(cat .xycloans_pool.id) --source $ALICE --network $NET \
      -- deposit --from $ALICE --amount 1000
stellar contract invoke --id $(cat .xycloans_pool.id) --source $BOB --network $NET \
      -- deposit --from $BOB --amount 1

# borrow some tokens from the pool
stellar contract invoke --id $(cat .xycloans_pool.id) --source $ADMIN --network $NET \
      -- borrow --receiver_id $(cat .xycloans_simple.id) --amount $BORROW_AMOUNT

# update the fee rewards and withdraw the matured rewards
stellar contract invoke --id $(cat .xycloans_pool.id) --source $BOB --network $NET \
      -- update_fee_rewards --addr $BOB
stellar contract invoke --id $(cat .xycloans_pool.id) --source $BOB --network $NET \
      -- withdraw_matured --addr $BOB

cd ${dir}
