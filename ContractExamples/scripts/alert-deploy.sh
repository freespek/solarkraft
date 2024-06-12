#!/usr/bin/env bash
#
# Deploy the alert contract
#
# Jure Kukovec, 2024
#
# @license
# [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)


set -e

dir=$(cd `dirname $0`; pwd -P)

cd ${dir}/..

NET=testnet
(soroban network ls | grep -q $NET) || (echo "add testnet via soroban network"; exit 1)

ACCOUNT=alice
soroban keys address $ACCOUNT || (echo "add the account $ACCOUNT via soroban keys generate"; exit 1)


set -x

soroban contract build
soroban contract deploy --wasm target/wasm32-unknown-unknown/release/alert.wasm \
      --source $ACCOUNT --network $NET