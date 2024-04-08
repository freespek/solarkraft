# HOWTO: Read State from the RPC

## Goals 
In [ADR1](../ADR/ADR_001.md) we described how we wanted to use an intermediate representation of State, to work with within Solarkraft. 

This HOWTO breaks down the various steps required to programmatically extract State in Javascript/Typescript, by using Soroban RPC calls.

## Process

We will be using [this contract][contract] in our example. Its internal state is composed of a single `COUNTER` of type `u32`.

To start with, we will need the deployed contract's ID. To quote from [this guide][guide]:

> When you deploy a contract, first the code is "installed" (i.e., it is uploaded onto the blockchain). This creates a LedgerEntry containing the Wasm byte-code, which is uniquely identified by its hash (that is, the hash of the uploaded code itself). 

Next, we need to identify the value, or set of values, we wish to read. In our case, this is a single field, named `CONTRACT`. 

For each of these values, we first need to determine under which key they are stored in the ledger. This involves computing an XDR representation.

The following snippet shows a function, which can be used to compute this for any contract ID and any field name (using the `stellar-sdk`):
```js
const getLedgerKeySymbol = (contractId, symbolText) => {
  const ledgerKey = xdr.LedgerKey.contractData(
    new xdr.LedgerKeyContractData({
      contract: new Address(contractId).toScAddress(),
      key: xdr.ScVal.scvSymbol(symbolText),
      durability: xdr.ContractDataDurability.persistent(),
    }),
  );
  return ledgerKey.toXDR("base64");
};
```

We need to call `getLedgerKeySymbol(contractID, "COUNTER")`. If we had a contract with multiple fields, we would call this method for each of them:
```
k = getLedgerKeySymbol(contractID, "COUNTER")
k_foo = getLedgerKeySymbol(contractID, "FOO")
k_bar = getLedgerKeySymbol(contractID, "BAR")
```

With the key, or set of keys, in hand, we now invoke the RPC, to querry the current values of the fields these keys represent.

In Javascript, querying the RPC is done as follows:
```js
let res = await fetch(NET, {
  method: 'POST',
  headers: {
    'Content-Type': 'application/json',
  },
  body: JSON.stringify(requestBody),
})
let json = await res.json()
```
where `NET` is the Soroban network being queried, for example 
`'https://soroban-testnet.stellar.org'`, and `requestBody` is the specific request we're making of the network.

Since we aim to read a ledger entry, our request will use the `getLedgerEntries` method, and `requestBody` will look like this:
```js
let requestBody = {
  "jsonrpc": "2.0",
  "id": ...,
  "method": "getLedgerEntries",
  "params": {
    "keys": [
      k
    ]
  }
}
```

Here, if we had multiple fields to read, we would simply use
```js
...
"keys": [
      k, k_foo, k_bar
    ]
```

Our result would look like this:
```js
{
  "jsonrpc": "2.0",
  "id": ...,
  "result": {
    "entries": [
      {
        "key": ...,
        "xdr": XDR,
        "lastModifiedLedgerSeq": ...
      }
    ],
    "latestLedger": ...
  }
}
```

where the value of the field that we seek is contained within `XDR`. With multiple keys, the difference would simply be
```js
...
"entries": [
      {
        "key": ...,
        "xdr": XDR,
        "lastModifiedLedgerSeq": ...
      },
      {
        "key": ...,
        "xdr": XDR_FOO,
        "lastModifiedLedgerSeq": ...
      }
      {
        "key": ...,
        "xdr": XDR_BAR,
        "lastModifiedLedgerSeq": ...
      }
    ],
```

The final step is unpacking the obtained XDR, from which we  read the value associated with our key. This [functionality][sdk] is available from the `stellar-sdk` (`LedgerEntryData.from_xdr`), as well as [online][lab] for quick experimentation.

Reading the `XDR` value, we should end up with the following shape:
```
LedgerEntryData: [contractData]
    contractData
        ext: [undefined]
        contract: [scAddressTypeContract]
            contractId: ...
        key: [scvVec]
            vec: Array[2]
                [0]: [scvSymbol]
                    sym: Counter
                [1]: [scvAddress]
                    address: ...
        durability: {"name":"persistent","value":1}
        val: [scvU32]
            u32: VAL
```
Where `VAL` is the value we need to read for `COUNTER`.
If the field we're interested in was some other type, say a map, it would look like this:
```
...
val: [scvMap]
    map: { "foo": 100, "bar": true, ...}
```

To summarize, these are the steps required to create a State:
0. Obtain a `contractId`.
1. Identify a collection of field identifiers (`"FOO", "BAR", "BAZ", ...`) that will make up the State
2. For each identifier `i`, compute `ki = getLedgerKeySymbol(contractID, i)`
3. Submit an RPC request with `"keys": [k1, k2, ...]`
4. In the result, for each XDR field, call `from_xdr`, and read the `contractData.val` field 


[contract]:
https://github.com/stellar/soroban-examples/blob/v20.2.0/increment/src/lib.rs

[guide]: https://developers.stellar.org/docs/smart-contracts/guides/rpc/retrieve-contract-code-js

[lab]:
https://laboratory.stellar.org/#xdr-viewer?type=TransactionEnvelope&network=test

[sdk]: https://stellar.github.io/js-stellar-sdk/SorobanDataBuilder.html#.fromXDR



