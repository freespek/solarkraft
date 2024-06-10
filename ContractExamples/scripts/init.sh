#!/usr/bin/env bash
#
# Call this script when starting from a fresh configuration
#
# Jure Kukovec, 2024
#
# @license
# [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)

set -x -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
RPC="https://soroban-testnet.stellar.org:443"

soroban network add \
    --rpc-url $RPC \
    --network-passphrase "Test SDF Network ; September 2015"\
    testnet

soroban keys generate alice --network testnet
soroban keys generate bob --network testnet

cd ${SCRIPT_DIR}/..

soroban contract build