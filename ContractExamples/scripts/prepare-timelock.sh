#!/usr/bin/env bash
#
# Deploys a token contract, initializes it and mints tokens, then deploys a timelock contract, deposits and claims
#
# Jure Kukovec, 2024
#
# @license
# [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)

set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

ALICE=alice
stellar keys address $ALICE || (echo "add the account $ALICE via stellar keys generate"; exit 1)
BOB=bob
stellar keys address $BOB || (echo "add the account $BOB via stellar keys generate"; exit 1)

#set -x

stellar contract deploy \
    --salt `date +%s` \
    --source-account alice \
    --network testnet \
    --wasm $SCRIPT_DIR/../target/wasm32-unknown-unknown/release/soroban_token_contract.wasm \
    -- --admin alice --decimal 18 --name TOK --symbol TOK \
    | tee >.token.id

TOKEN=$(cat .token.id)
if [ -z "$TOKEN" ]; then
    echo "Failed to deploy the token contract"
    exit 1
fi

echo "Token contract ID: $TOKEN"

stellar contract invoke \
    --id $TOKEN \
    --source alice \
    --network testnet \
    -- \
    mint \
    --to alice \
    --amount 100

stellar contract deploy \
    --wasm $SCRIPT_DIR/../target/wasm32-unknown-unknown/release/soroban_timelock_contract.wasm \
    --source alice \
    --network testnet \
    | tee >.timelock.id

TIMELOCK=$(cat .timelock.id)

if [ -z "$TIMELOCK" ]; then
    echo "Failed to deploy the timelock contract"
    exit 1
fi

echo "Timelock contract ID: $TIMELOCK"

stellar contract invoke \
    --id $TIMELOCK \
    --source alice \
    --network testnet \
    -- \
    deposit \
    --from alice \
    --token $TOKEN \
    --amount 1 \
    --claimants "[\"$(stellar keys address bob)\"]"\
    --time_bound '{"kind": "After", "timestamp": 0}'

stellar contract invoke \
    --id $TIMELOCK \
    --source bob \
    --network testnet \
    -- \
    claim \
    --claimant bob
