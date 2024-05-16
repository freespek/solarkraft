# ADR002: Storage Layout

**Author:** Igor Konnov, 2024

This ADR discusses the simple layout of the Soroban transactions that are
fetched from a Stellar network.

Our goals are:

 - Store contract calls retrieved from the Horizon API, see [storage.ts][].
 - Access calls indendently for verification.
 - Tag calls as `stored`, `verified`, `failed`, etc.

To keep things simple in the activation stage, we are simply using the
filesystem instead of a fully-featured database. This is sufficient to
demonstrate our idea.  When the users expect a storage that its durable,
consistent, fail-free, etc., we would have to implement the storage with a solid
database library.

In the rest of this document, we refer to the root of the storage directory as
`${STOR}`. We expect the user to provide the Solarkraft commands with the
root directory. By default, `${STOR}` would point to
`$HOME/.solarkraft/.stor`.

## 1. Storing extracted calls

We have the following requirements to the storage:

 - It should support contract calls (from transactions) that are extracted for
   different contracts.
 
 - It should be relatively easy to order these transactions, e.g., by ledger height.

 - Transactions that happen in the same block should not collide.


Given all these requirements, we store every contract call in its own file called:

```
${STOR}/${contractId}/${height}/entry-${txHash}.json
```

The values `${contractId}`, `${height}`, `${txHash}` are the values of the
fields that are defined in [storage.ts][].

The file is a JSON serialization of [ContractCallEntry][]. Some care is required
to serialize big integers, we use [json-bigint][]. Additionally, we serialized
`OrderedMap` as an array.

## 2. Storing verification results

The verification results are to be stored in a file called:

```
${STOR}/${contractId}/${height}/verification-${txHash}.json
```

The exact format of this file is to be defined later.



[storage.ts]: https://github.com/freespek/solarkraft/blob/main/solarkraft/src/fetcher/storage.ts
[ContractCallEntry]: https://github.com/freespek/solarkraft/blob/38d57fd51082feab9215a77c555bdccdc961aa26/solarkraft/src/fetcher/storage.ts#L23
[json-bigint]: https://www.npmjs.com/package/@types/json-bigint