# Solarkraft

Solarkraft is a runtime monitoring tool for [Soroban][], powered by [TLA+][] and [Apalache][].

The project is in the boostrapping phase now. Preparing for Warp 5.

We are grateful to the [Stellar Community Fund][] for supporting our project via
the Activation Award. Check our [3-minute pitch][], and the [project details](#project-details) below.

![activation award](./assets/solarkraft-stellar-activation.png)

### Project Details

Solarkraft is a tool for runtime monitoring of [Soroban smart contracts][Soroban]. It tests whether a smart contract conforms to its specification during contract development, testing, and after contract deployment on the [Stellar blockchain][Stellar]. The contract specification is written as an ensemble of [TLA+][] specifications, each capturing a property of the contract’s expected behavior.

Solarkraft inspects invocations of the timelock contract’s methods in the history of Stellar transactions. Whenever Solarkraft finds a deviation from the expected behavior (as prescribed by the monitor specifications) it reports a monitoring alert. Importantly, monitors are small snippets of code, not an entire specification. This makes them more accessible formal artifacts than usual.

[Stellar]: https://stellar.org/
[Soroban]: https://developers.stellar.org/docs/smart-contracts/getting-started/setup
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html
[Apalache]: https://github.com/informalsystems/apalache
[Stellar Community Fund]: https://communityfund.stellar.org/
[3-minute pitch]: https://www.youtube.com/watch?v=Ogdy4AHfMRA
[timelock contract]: https://github.com/stellar/soroban-examples/tree/main/timelock


## License

[Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
