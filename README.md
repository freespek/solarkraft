# Solarkraft

Solarkraft is a runtime monitoring tool for [Soroban][], powered by [TLA+][] and [Apalache][].

We have finished the activation phase and developed an MVP.  
🎥 Watch the [10-minute demo video](https://youtu.be/E99TNzTHLXI) by Jure Kukovec.

For more explanation, read our series of blog posts:

 - Part 1: [A New Hope – Why Smart Contract Bugs Matter and How Runtime Monitoring Saves the Day][new hope]
 - Part 2: [Guardians of the Blockchain: Small and Modular Runtime Monitors in TLA+ for Soroban Smart Contracts][guardians]
 - Part 3: [How to Run Solarkraft][howto]
 - Part 4: [The Force Awakens: Hybrid Blockchain Runtime Monitors][part4]
 - Part 5: [The Rise of Model Checker: Verifying Blockchain Monitors In and Near Realtime][part5]

### Project Details

Solarkraft is a tool for runtime monitoring of [Soroban smart contracts][Soroban]. It tests whether a smart contract conforms to its specification during contract development, testing, and after contract deployment on the [Stellar blockchain][Stellar]. The contract specification is written as an ensemble of [TLA+][] specifications, each capturing a property of the contract’s expected behavior.

Solarkraft inspects invocations of the timelock contract’s methods in the history of Stellar transactions. Whenever Solarkraft finds a deviation from the expected behavior (as prescribed by the monitor specifications) it reports a monitoring alert. Importantly, monitors are small snippets of code, not an entire specification. This makes them more accessible formal artifacts than usual.

### SCF Activation Award

We are grateful to the [Stellar Community Fund][] for supporting our project via an Activation Award.  
Check our [latest pitch][] for our Community Award submission.

![activation award](./assets/solarkraft-stellar-activation.png)

[Stellar]: https://stellar.org/
[Soroban]: https://developers.stellar.org/docs/smart-contracts/getting-started/setup
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html
[Apalache]: https://github.com/informalsystems/apalache
[Stellar Community Fund]: https://communityfund.stellar.org/
[latest pitch]: https://youtu.be/shVFqoUl-5A
[timelock contract]: https://github.com/stellar/soroban-examples/tree/main/timelock
[new hope]: https://thpani.net/2024/06/why-smart-contract-bugs-matter-and-how-runtime-monitoring-saves-the-day-solarkraft-1/
[guardians]: https://thpani.net/2024/06/small-and-modular-runtime-monitors-in-tla-for-soroban-smart-contracts-solarkraft-2/
[howto]: https://protocols-made-fun.com/solarkraft/2024/06/19/solarkraft-part3.html
[part4]: https://systems-made-simple.dev/solarkraft/2024/06/24/solarkraft-hybrid-monitors.html
[part5]: https://systems-made-simple.dev/solarkraft/2024/07/04/solarkraft-monitor-verification.html

## License

[Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
