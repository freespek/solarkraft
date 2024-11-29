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
(stellar network ls | grep -q $NET) || (echo "add testnet via stellar network"; exit 1)

ACCOUNT=alice
stellar keys address $ACCOUNT || (echo "add the account $ACCOUNT via stellar keys generate"; exit 1)


set -x

stellar contract build
stellar contract deploy --wasm target/wasm32-unknown-unknown/release/alert.wasm \
      --source $ACCOUNT --network $NET