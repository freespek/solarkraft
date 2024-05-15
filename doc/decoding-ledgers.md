# Decoding Ledgers

This document summarizes our knowledge on decoding Stellar/Soroban ledger data.

The easiest way to check transactions manually is by visiting the [Stellar
Expert][] block explorer.

To retrieve transactions we are using [Horizon Testnet][], which provides us
with a REST API. For example, to retrieve ledger data for the block number
1622111 (called a ledger in Stellar), we make the following HTTPS request:

```sh
$ curl https://horizon-testnet.stellar.org/ledgers/1622111

{
  "_links": {
    "self": {
      "href": "https://horizon-testnet.stellar.org/ledgers/1622111"
    },
    "transactions": {
      "href": "https://horizon-testnet.stellar.org/ledgers/1622111/transactions{?cursor,limit,order}",
      "templated": true
    },
    "operations": {
      "href": "https://horizon-testnet.stellar.org/ledgers/1622111/operations{?cursor,limit,order}",
      "templated": true
    },
    "payments": {
      "href": "https://horizon-testnet.stellar.org/ledgers/1622111/payments{?cursor,limit,order}",
      "templated": true
    },
    "effects": {
      "href": "https://horizon-testnet.stellar.org/ledgers/1622111/effects{?cursor,limit,order}",
      "templated": true
    }
  },
  "id": "4c01811fbded17b7ca915a73a6f25c1949ee0dcca31b070b1dcc139ae7aaf73a",
  "paging_token": "6966913695481856",
  "hash": "4c01811fbded17b7ca915a73a6f25c1949ee0dcca31b070b1dcc139ae7aaf73a",
  "prev_hash": "e988c18c14006fb0a6c053c4093a19b1d64d131f2944b15e6059e8ca01a3a3ff",
  "sequence": 1622111,
  "successful_transaction_count": 7,
  "failed_transaction_count": 7,
  "operation_count": 7,
  "tx_set_operation_count": 19,
  "closed_at": "2024-05-15T09:35:22Z",
  "total_coins": "100000000000.0000000",
  "fee_pool": "160191.7967741",
  "base_fee_in_stroops": 100,
  "base_reserve_in_stroops": 5000000,
  "max_tx_set_size": 200,
  "protocol_version": 21,
  "header_xdr": "AAAAFemIwYwUAG+wpsBTxAk6GbHWTRMfKUSxXmBZ6MoBo6P/Uc2qpfCHBd+YQCtXT4yV58aucix0YC9+Q+cuOEKJ0xEAAAAAZkSB2gAAAAAAAAABAAAAALVdELK7fShO1cA6R6XhtZDJD1eDVUccxFB7voIE0jyLAAAAQFPmQ5XY3XnDI0YlG+sTPtPycIL/m739HKwRbY2kYcemUmjhqDRU7vGGCNWQQbUzZXNbLdSFp/jfBosL3FotHwAwYp1ijD04meqWTSvSAJEZBJyTckewEV33/Kbo/MmkPsVEH8o9aGELcC9uuuU1MkQr8PYE/3Sqdo+TzOrL2mrbABjAXw3gtrOnZAAAAAABdPnAXX0AAAAAAAAAAAAAy0UAAABkAExLQAAAAMjNr0CX/lXFoTlIoG450pNnIOGZFR5HHdNJ6GZHoR5O0foyTwXI8TvlFUA9RDM7Ao608Z3XjJCg9Af5xaF5BwDsH8nY0n/tR7VTs7RX1YG2BWy/Oibkds/T8FM6LM/w6km+6gNenV6MJ5ODWUlX5RYu+y6PSOycRLwHB5WIYWJOmgAAAAA="
}
```

By looking at the returned JSON, we can immediately observe that some of the
fields are encoded in [XDR][], e.g., look at the field `header_xdr`. To manually
decode these fields, we can use the XDR Viewer by [Stellar Laboratory][].
Sometimes, it is hard to figure the right combination of types with the XDR
Viewer, so it is easier to use Stellar SDK directly.

To decode transactions programmatically, we need [Stellar SDK][]:

```sh
$ npm install --save @stellar/stellar-sdk@12.0.0-rc.2
```

To deserialize an XDR field programmatically, we have to inspect [Stellar SDK
API][], guess the right type and decode it from XDR. This can be also done in
NodeJS REPL:

```js
$ node
const sdk = require("@stellar/stellar-sdk")
// find all XDR types that contain 'Header'
Object.keys(sdk.xdr).sort().filter(name => name.includes('Header'))
// deserialize from XDR to a JavaScript object
sdk.xdr.LedgerHeader.fromXDR('AAAAFemIwYwUAG+wpsBTxAk6GbHWTRMfKUSxXmBZ6MoBo6P/Uc2qpfCHBd+YQCtXT4yV58aucix0YC9+Q+cuOEKJ0xEAAAAAZkSB2gAAAAAAAAABAAAAALVdELK7fShO1cA6R6XhtZDJD1eDVUccxFB7voIE0jyLAAAAQFPmQ5XY3XnDI0YlG+sTPtPycIL/m739HKwRbY2kYcemUmjhqDRU7vGGCNWQQbUzZXNbLdSFp/jfBosL3FotHwAwYp1ijD04meqWTSvSAJEZBJyTckewEV33/Kbo/MmkPsVEH8o9aGELcC9uuuU1MkQr8PYE/3Sqdo+TzOrL2mrbABjAXw3gtrOnZAAAAAABdPnAXX0AAAAAAAAAAAAAy0UAAABkAExLQAAAAMjNr0CX/lXFoTlIoG450pNnIOGZFR5HHdNJ6GZHoR5O0foyTwXI8TvlFUA9RDM7Ao608Z3XjJCg9Af5xaF5BwDsH8nY0n/tR7VTs7RX1YG2BWy/Oibkds/T8FM6LM/w6km+6gNenV6MJ5ODWUlX5RYu+y6PSOycRLwHB5WIYWJOmgAAAAA=', 'base64')
ChildStruct {
  _attributes: {
    ledgerVersion: 21,
  ...
}  
```

Of course, the resulting object contains fields in XDR too, so we have to repeat
deserialization for those fields.

On top of that, the ledger entry itself does not give us all the data. For instance, to retrieve
the transactions, we have to do another HTTPS query:

```js
$ curl https://horizon-testnet.stellar.org/ledgers/1622111/transactions
{
  "_links": {
  ...
}  
```

These interactions are getting annoying very quickly. To our luck, Stellar SDK gives us a nicer
API for interacting with Horizon. For instance:

```js
const server = new sdk.Horizon.Server('https://horizon-testnet.stellar.org')
// get the ledger entry as a JS object
await server.ledgers().ledger(1622111).call()
// get an array of the transactions for a specific ledger (block number)
await server.transactions().forLedger(1622111).call()
```




[Stellar Expert]: https://stellar.expert/
[Horizon Testnet]: https://horizon-testnet.stellar.org/
[Stellar SDK]: https://github.com/stellar/js-stellar-sdk/
[XDR]: https://en.wikipedia.org/wiki/External_Data_Representation
[Stellar Laboratory]: https://laboratory.stellar.org/
[Stellar SDK API]: https://stellar.github.io/js-stellar-sdk