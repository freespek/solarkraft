# Force platform to linux/amd64; there is no Z3 release for linux/arm64:
# https://github.com/Z3Prover/z3/issues/7201
FROM --platform=linux/amd64 mcr.microsoft.com/devcontainers/typescript-node:20-bookworm
ENV PATH="/opt/apalache/bin/:${PATH}"