# HOWTO: Set Up a Testnet and Deploy Custom Contracts

## Goals 
This HOWTO details the steps required to set up a local Stellar network, deploy a custom Soroban contract, and invoke the contract via CLI. It complements the [official guide][guide].

## Process

Prerequisites:
- Make `cargo`, `rustup`, and `go` available. You will need a`rustc` version that is at least 1.74.
- Make sure you have enough allocated space. If you're using the NixOS VM, you might need to add `services.logind.extraConfig = "RuntimeDirectorySize=2G";` to your configuration, rebuild and reboot the VM.
- you probably want to add `~/.cargo/bin` to your PATH

### Local Stellar Network
Instead of building from source, Stellar provides a quickstart Docker image. You can call the below command from anywhere, and Docker will fetch the image.
```sh
docker run --rm -d \
    -p 8000:8000 \
    --name stellar \
    stellar/quickstart:testing \
    --testnet \
    --enable-soroban-rpc
```
Note here that the [official guide][guide] would have you run this in interactive mode (`run ... -it ...`), but for just the network having it run in the background (`-d`) is less noisy and doesn't hijack the terminal.

The above snippet deploys a testnet (`--testnet`), if you want a standalone network, replace that flag with `--standalone`.

### Soroban CLI
In order to interact with your docker image, you will need the [Soroban CLI][cli]. With `cargo`, all you need is:
```sh
cargo install --locked soroban-cli --features opt
```

note that this gets placed in `~/.cargo/bin`, which is why you want that as part of your `PATH`.

### Custom Soroban Contracts

<!--- TODO: Make a megacontract and link it here-->

You can use the Soroban CLI to set up a blank project, and add your own contract code to it (you may also optionally include any of their example contracts).

To set up a new _project_ (not contract!), type:
```sh
soroban contract init <DIR>
```
This will populate `<DIR>` (e.g. `.`) with some basic files, most notably a `Cargo.toml` config. Your custom contract should be added in `<DIR>/contracts/<CONTRACT>`.
For example, for a contract `Foo`, you'd create:
```
<DIR>
├── Cargo.toml
└── contracts
    └── Foo
        ├── Cargo.toml
        └── src
            ├── lib.rs
            └── test.rs
```

Note that `Cargo.toml` in `Foo` is _not_ the same `Cargo.toml` in `<DIR>`! The latter gets created automagically with `soroban contract init`, the former you have to add yourself. Here's an example of `Cargo.toml` in the contract folder:
```
dev_dependencies = { soroban-sdk = { workspace = true } }
[package]
name = "foo"
version = "0.0.0"
edition = "2021"
publish = false

[lib]
crate-type = ["cdylib"]
doctest = false

[dependencies]
soroban-sdk = { workspace = true }

[dev-dependencies]
soroban-sdk = { version = "20.3.2", features = ["testutils"] }
```

Write your contract code in `lib.rs`, and tests in `test.rs`.
Make sure all your tests work before deploying (with print outputs):
```sh
cargo test -- --nocapture
```
Once they do, running
```sh
soroban contract build
```
will create a `.wasm` file from your Rust code in 
```
<DIR>/target/wasm32-unknown-unknown/release/<CONTRACT>.wasm
```
This is the file you will need to deploy to the network.

### Connecting the Pieces
We first need to make the Soroban CLI aware of the network running in Docker, by configuring
```sh
soroban config network add <NETWORK> \
    --rpc-url "http://localhost:8000/soroban/rpc" \
    --network-passphrase <PASSPHRASE>
```
where `<NETWORK>` is the alias you want to use (e.g. `net`/`testnet`/`standalone`/etc.) and `<PASSPHRASE>` is any string passphrase (e.g. the docs use `"Standalone Network ; February 2017"` or `"Test SDF Network ; September 2015"`, but it can be anything).

Next, we create agents within this network. To do this, run
```sh
soroban keys generate <AGENT> --network <NETWORK>
```
followed by
```sh
soroban config identity fund <AGENT> --network <NETWORK>
```
The latter will show a warning, saying that `<AGENT>` already exists, but if you call this command before the previous one it fails to execute, and if you don't call it at all the next command fails, so just ignore the warning.

Having defined an agent, you can have them deploy the contract with:
```sh
soroban contract deploy --wasm <CONTRACT>.wasm --source <AGENT> --network <NETWORK>
```
This will return a _contract ID_ (`<CID>`), which is how you can refer to the contract (see [HOWTO1](./howto_readState.md) for how this ID is also relevant in the SDK).

You can now invoke the contract using
```sh
soroban contract invoke --id <CID> --source <AGENT> --network <NETWORK> -- <METHOD> [--<ARG1> <VAL1> --<ARG2> <VAL2> ...]

```
for example, if your contract defines
```rust
pub fn bar(env: Env, addr: Address) -> u32 {...}
```
You can have `alice` call it with her own address as an argument:
```
soroban contract invoke --id <CID> --source alice --network <NETWORK> -- bar --addr alice
```

Observe that the first argument of any contract method should be an `Env`, which gets supplied automatically, and does not need to be referenced in the invocation.


[cli]:
https://github.com/stellar/soroban-cli

[guide]: https://developers.stellar.org/network/soroban-rpc/admin-guide

[build]:
https://developers.stellar.org/docs/smart-contracts/getting-started/storing-data#build-the-contract



