#!/usr/bin/env bash

# NOTE: we should use the standard command, but it does not seem to use the right flags
# stellar contract build

RUSTFLAGS="-C target-feature=-reference-types" cargo build --target wasm32-unknown-unknown --release