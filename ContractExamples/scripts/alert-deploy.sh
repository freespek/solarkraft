#!/usr/bin/env bash
#
# Deploy the alert contract
#
# Jure Kukovec, 2024
#
# @license
# [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)


set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

ACCOUNT=alice
soroban keys address $ACCOUNT || (echo "add the account $ACCOUNT via soroban keys generate"; exit 1)

set -x

ALERT=$(soroban contract deploy \
    --wasm $SCRIPT_DIR/../target/wasm32-unknown-unknown/release/alert.wasm \
    --source $ACCOUNT \
    --network testnet)

echo "Alert contract ID: $ALERT"