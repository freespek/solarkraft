/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Extract Stellar operations that correspond to Soroban contract calls.
 *
 * @author Igor Konnov, 2024
 * @author Thomas Pani, 2024
 * @license [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

import sdk, { Address, Horizon } from '@stellar/stellar-sdk'
import {
    ContractCallEntry,
    emptyContractStorage,
    emptyFieldsMap,
    emptyMultiContractStorage,
    MultiContractStorage,
} from './storage.js'
import { Maybe, just, none } from '@sweet-monads/maybe'

/**
 * Decode a contract call from a Horizon operation.
 * @param op an operation
 * @param matcher a quick matcher over the contractId to avoid expensive deserialization
 */
export async function extractContractCall(
    op: Horizon.ServerApi.InvokeHostFunctionOperationRecord,
    matcher: (contractId: string) => boolean,
    typemapJson: any = {}
): Promise<Maybe<ContractCallEntry>> {
    // `op.function` can be one of HostFunctionTypeHostFunctionTypeInvokeContract, HostFunctionTypeHostFunctionTypeCreateContract, or HostFunctionTypeHostFunctionTypeUploadContractWasm.
    // https://developers.stellar.org/network/horizon/api-reference/resources/operations/object/invoke-host-function
    if (op.function !== 'HostFunctionTypeHostFunctionTypeInvokeContract') {
        return none()
    }

    // This operation represents a smart contract call.
    // In particular, it contains: the callee contract, the method, and its parameters.
    //
    // https://developers.stellar.org/network/horizon/api-reference/resources/operations/object
    // https://developers.stellar.org/network/horizon/api-reference/resources/operations/object/invoke-host-function

    // Extract the call data: time, transaction hash, parameters

    // In Soroban, `env.ledger().timestamp()` "[r]eturns a unix timestamp for when the ledger was closed":
    // https://docs.rs/soroban-sdk/latest/soroban_sdk/ledger/struct.Ledger.html#method.timestamp
    // According to [this](https://stellar.stackexchange.com/questions/1852/transaction-created-at-and-ledger-close-time),
    // the transaction object's `created_at` equals the ledger's `closed_at`.
    // `created_at` and `env.ledger().timestamp()` have seconds-precision. We divide by 1000 here since `Date` internally
    // represents the timestamp as milliseconds.
    const timestamp = new Date(op.created_at).getTime() / 1000
    const txHash = op.transaction_hash
    // decode the call parameters from XDR to native JS values
    const params = op.parameters.map((p) => {
        return sdk.scValToNative(sdk.xdr.ScVal.fromXDR(p.value, 'base64'))
    })
    const contractId = params[0]
    if (!matcher(contractId)) {
        // return quickly to avoid additional calls and deserialization
        return none()
    }

    // continue with extracting transaction data and ledger updates
    const method = params[1]
    const methodArgs = params.slice(2)

    // Now we look into the typemap file, to see if we're given type hints. This is effectively required
    // for vector-like arguments, which could be encodings of enums:
    // https://developers.stellar.org/docs/learn/smart-contract-internals/types/custom-types#enum-unit-and-tuple-variants
    // Could be undefined, in which case we should fail on ambiguous input
    const typeHints = {
        methods: typemapJson['methods'] ?? {},
        variables: typemapJson['variables'] ?? {},
    }

    const tx = await op.transaction()
    // Get the containing ledger number:
    // https://developers.stellar.org/network/horizon/api-reference/resources/transactions/object
    const height = tx.ledger_attr

    // The operation itself does not give us the ledger updates.
    // Deserialize tx.result_meta_xdr.
    const meta = sdk.xdr.TransactionMeta.fromXDR(tx.result_meta_xdr, 'base64')
    // extract transaction metadata for version 3
    if (meta.switch() !== 3) {
        // Is it possible to have older transaction metadata with Soroban?
        // TODO: make it future-proof
        console.error(
            `Expected TransactionMetaV3, found ${meta.switch()}: txHash = ${txHash}`
        )
        return none()
    }

    const meta3 = meta.value() as sdk.xdr.TransactionMetaV3

    const [oldStorage, storage]: [MultiContractStorage, MultiContractStorage] =
        meta3
            .operations()
            .reduce(
                ([oldStorage, storage], op) =>
                    op
                        .changes()
                        .reduce(
                            ([oldStorage, storage], change) =>
                                applyLedgerEntryChange(
                                    oldStorage,
                                    storage,
                                    change
                                ),
                            [oldStorage, storage]
                        ),
                [emptyMultiContractStorage(), emptyMultiContractStorage()]
            )

    // decode return value
    const returnValue = sdk.scValToNative(meta3.sorobanMeta().returnValue())

    return just({
        height,
        timestamp,
        txHash,
        txSuccess: op.transaction_successful,
        contractId,
        method,
        methodArgs,
        returnValue,
        oldFields: oldStorage.get(contractId, emptyContractStorage()).instance,
        fields: storage.get(contractId, emptyContractStorage()).instance,
        oldStorage,
        storage,
        typeHints,
    })
}

// Return storage mutated to reflect the ledger state before and after the ledger entry change
function applyLedgerEntryChange(
    oldStorage: MultiContractStorage,
    storage: MultiContractStorage,
    change: sdk.xdr.LedgerEntryChange
): [MultiContractStorage, MultiContractStorage] {
    switch (change.switch().name) {
        case 'ledgerEntryCreated':
            return [oldStorage, contractData(change.created().data(), storage)]

        case 'ledgerEntryUpdated':
            return [oldStorage, contractData(change.updated().data(), storage)]

        case 'ledgerEntryState':
            return [contractData(change.state().data(), oldStorage), storage]

        case 'ledgerEntryRemoved':
            // this is triggered if a persistent or temporary entry is removed via env.storage()._().remove(key)
            // it will be present in `oldStorage` via `ledgerEntryState`, and should not be added to `storage`; thus this is just a no-op
            return [oldStorage, storage]
    }
}

// return `storage`, mutated by the contract data change
function contractData(
    data: sdk.xdr.LedgerEntryData,
    storage: MultiContractStorage
): MultiContractStorage {
    if (data.switch().name !== 'contractData') {
        return storage
    }

    const contract = Address.fromScAddress(
        data.contractData().contract()
    ).toString()
    const contractDataVal = data.contractData().val()

    // All instance storage fields are stored together with the contract code in the singleton "instance" ledger e ntry.
    // For temporary and persistent entries, each field is stored in a separate ledger entry.
    if (contractDataVal.switch().name === 'scvContractInstance') {
        // the contract instance chanaged

        const instanceStorage = contractDataVal.instance().storage()
        if (instanceStorage === undefined) {
            // instance storage may be empty

            // console.log(`instance storage of ${contract}: empty`)

            const contractStorage = storage.get(
                contract,
                emptyContractStorage()
            )
            return storage.set(contract, {
                ...contractStorage,
                instance: emptyFieldsMap(),
            })
        } else {
            const contractStorage = storage.get(
                contract,
                emptyContractStorage()
            )
            const fields = instanceStorage.reduce((map, entry) => {
                const key = sdk.scValToNative(entry.key()).toString()
                const val = sdk.scValToNative(entry.val())
                // console.log(`instance storage of ${contract} changed: ${key} -> ${util.inspect(val)}`)
                return map.set(key, val)
            }, contractStorage.instance)
            return storage.set(contract, {
                ...contractStorage,
                instance: fields,
            })
        }
    } else {
        // a temporary or persistent entry changed
        const durability = data.contractData().durability().name
        const key = sdk.scValToNative(data.contractData().key()).toString()
        const val = sdk.scValToNative(contractDataVal)

        // console.log(`${durability} storage of ${contract} changed: ${key} -> ${util.inspect(val)}`)

        const contractStorage = storage.get(contract, emptyContractStorage())
        const durabilityStorage = (
            durability === 'temporary'
                ? contractStorage.temporary
                : contractStorage.persistent
        ).set(key, val)
        return storage.set(contract, {
            ...contractStorage,
            [durability]: durabilityStorage,
        })
    }
}
