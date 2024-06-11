#!/usr/bin/env bash
#
# Deploys a token contract, initializes it and mints tokens, then deploys a timelock contract and deposits
#
# Jure Kukovec, 2024
#
# @license
# [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)

set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

ALICE=alice
soroban keys address $ALICE || (echo "add the account $ALICE via soroban keys generate"; exit 1)
BOB=bob
soroban keys address $BOB || (echo "add the account $BOB via soroban keys generate"; exit 1)

set -x

TOKEN=$(
    soroban contract deploy \
    --source-account alice \
    --network testnet \
    --wasm $SCRIPT_DIR/../contracts/token/target/wasm32-unknown-unknown/release/soroban_token_contract.wasm
)

echo "Token contract ID: $TOKEN";

soroban contract invoke \
    --id $TOKEN \
    --source alice \
    --network testnet \
    -- \
    initialize \
    --admin alice \
    --decimal 18 \
    --name '"TOK"' \
    --symbol '"TOK"';

soroban contract invoke \
    --id $TOKEN \
    --source alice \
    --network testnet \
    -- \
    mint \
    --to alice \
    --amount 100;

TIMELOCK=$(soroban contract deploy \
    --wasm $SCRIPT_DIR/../contracts/timelock/target/wasm32-unknown-unknown/release/soroban_timelock_contract.wasm \
    --source alice \
    --network testnet);

echo "Timelock contract ID: $TIMELOCK"

soroban contract invoke \
    --id $TIMELOCK \
    --source alice \
    --network testnet \
    -- \
    deposit \
    --from alice \
    --token $TOKEN \
    --amount 1 \
    --claimants "[\"$(soroban keys address bob)\"]"\
    --time_bound '{"kind": "After", "timestamp": 0}'
