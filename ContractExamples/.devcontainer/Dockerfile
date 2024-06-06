FROM mcr.microsoft.com/devcontainers/rust:latest

USER vscode
RUN cargo install --locked soroban-cli@=21.0.0-rc.1
RUN rustup target add wasm32-unknown-unknown

# The following should be run at a project level:
# soroban network add --rpc-url https://soroban-testnet.stellar.org:443 --network-passphrase "Test SDF Network ; September 2015" testnet
# soroban keys generate alice --network testnet