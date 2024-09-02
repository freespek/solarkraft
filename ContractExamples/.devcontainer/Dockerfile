FROM mcr.microsoft.com/devcontainers/rust:dev-bookworm

USER vscode

# This will eat ~13.5GB of memory!
RUN cargo install --locked stellar-cli --features opt

RUN rustup target add wasm32-unknown-unknown

# The following should be run at a project level:
# soroban network add --rpc-url https://soroban-testnet.stellar.org:443 --network-passphrase "Test SDF Network ; September 2015" testnet
# soroban keys generate alice --network testnet