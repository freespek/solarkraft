#!/usr/bin/env bash

# see: https://github.com/stellar/rs-soroban-sdk/pull/1353
rustc --version | grep 1.81.0 || (echo "Run: rustup default 1.8210"; exit 1)

dir=$(cd `dirname $0`; pwd -P)
cd ${dir}/..

# build our contracts and soroban-examples
stellar contract build

# When using rust over 1.81.0:
#RUSTFLAGS="-C target-feature=-reference-types" cargo build --target wasm32-unknown-unknown --release