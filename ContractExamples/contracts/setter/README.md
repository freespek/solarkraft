`Setter` is a simple Soroban contract that contains setters and getters for the
built-in [Soroban types][]. We are using this contract to debug the transaction
fetcher.

## How to use

 1. Make sure that you have installed Soroban by following the [Getting Started]
 guide.

 1. Deploy the setter contract:

    ```sh
    $ cd ContractExamples
    $ soroban build
    $ soroban contract deploy --wasm target/wasm32-unknown-unknown/release/setter.wasm \
      --source alice --network testnet | tee >setter.id
    ```

 1. Invoke a setter function. For example:

    ```sh
    $ soroban contract invoke --id $(cat setter.id) --source alice --network testnet \
      -- set_i32 --v 42
    0
    ```

 1. Invoke a getter function. For example:

    ```sh
    $ soroban contract invoke --id $(cat setter.id) --source alice --network testnet \
      -- get_i32
    42
    ```
 
 
[Soroban types]: https://developers.stellar.org/docs/learn/smart-contract-internals/types/built-in-types
[Getting Started]: https://developers.stellar.org/docs/smart-contracts/getting-started/setup
