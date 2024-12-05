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

NET=testnet
(stellar network ls | grep -q $NET) || (echo "add testnet via stellar network"; exit 1)

ACCOUNT=alice
stellar keys address $ACCOUNT || (echo "add the account $ACCOUNT via stellar keys generate"; exit 1)

ACCOUNT2=bob
stellar keys address $ACCOUNT2 || (echo "add the account $ACCOUNT2 via stellar keys generate"; exit 1)

set -x

./scripts/build.sh

stellar contract deploy --wasm target/wasm32-unknown-unknown/release/setter.wasm \
      --source $ACCOUNT --network $NET | tee >.setter.id

stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_bool --v true
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_u32 --v 42
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_i32 --v '-42'
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_u64 --v 42
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_i64 --v '-42'
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_u128 --v 42
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_i128 --v '-42'
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_sym --v hello
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_bytes --v beef
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_bytes32 --v beef0123456789beef0123456789beef0123456789ab
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_vec --v '[ 1, -2, 3 ]'
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_map --v '{ "2": 3, "4": 5 }'
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_address --v GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_struct --v '{ "a": 1, "b": "-100" }'
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- set_enum --v '{ "B": "-200" }'
stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET \
      -- remove_bool

# NOTE: we do not do that in the CI script
# we can provoke a failed transaction by submitting 2 transactions in parallel from different accounts
#stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT --network $NET -- set_bool_if_notset &
#stellar contract invoke --id $(cat .setter.id) --source $ACCOUNT2 --network $NET -- set_bool_if_notset
