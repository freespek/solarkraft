FROM mcr.microsoft.com/devcontainers/rust:dev-bookworm

USER vscode

# This will eat ~13.5GB of memory!
RUN cargo install --locked stellar-cli --features opt

RUN rustup target add wasm32-unknown-unknown

RUN stellar keys generate --global alice --network testnet
RUN stellar keys generate --global bob --network testnet
