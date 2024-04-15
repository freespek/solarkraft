FROM mcr.microsoft.com/devcontainers/rust:latest

USER vscode
RUN cargo install --locked soroban-cli
RUN rustup target add wasm32-unknown-unknown

# The following should be run at a project level:
# soroban config network add testnet --rpc-url "http://host.docker.internal:8000/soroban/rpc" --network-passphrase "Test SDF Network ; September 2015"
# soroban keys generate alice --network testnet