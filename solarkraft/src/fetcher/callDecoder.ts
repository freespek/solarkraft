/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

/**
 * The code to extract Stellar operations that correspond to Soroban contract calls.
 *
 * Igor Konnov, 2024.
 */

import sdk, { Address } from '@stellar/stellar-sdk'
import { ContractCallEntry, FieldsMap } from './storage.js'
import { Maybe, just, none } from '@sweet-monads/maybe'
import { OrderedMap } from 'immutable'

/**
 * Decode a contract call from a Horizon operation.
 * @param op an operation
 * @param matcher a quick matcher over the contractId to avoid expensive deserialization
 */
export async function extractContractCall(
    op: any,
    matcher: (contractId: string) => boolean
): Promise<Maybe<ContractCallEntry>> {
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
    const fieldsUpdates: FieldsMap[] = meta3
        .operations()
        .map((o) =>
            o
                .changes()
                .map(ledgerEntry(contractId))
                .filter((c) => c.isJust())
                .map((c) => c.value)
        )
        .flat()

    if (fieldsUpdates.length > 2) {
        console.error(`Transaction ${txHash} has over two contract states`)
    }

    // contract storage after the operations were applied
    const fields =
        fieldsUpdates.length >= 1
            ? fieldsUpdates.pop()
            : OrderedMap<string, any>()
    // contract storage before the operations were applied
    const oldFields =
        fieldsUpdates.length >= 1
            ? fieldsUpdates.pop()
            : OrderedMap<string, any>()

    // decode return value
    const returnValue = sdk.scValToNative(meta3.sorobanMeta().returnValue())

    return just({
        height,
        timestamp,
        txHash,
        contractId,
        method,
        methodArgs,
        returnValue,
        fields,
        oldFields,
    })
}

// decode a contract entry that is changed by a contract call
function ledgerEntry(
    contractId: string
): (entry: sdk.xdr.LedgerEntryChange) => Maybe<FieldsMap> {
    return (entry: sdk.xdr.LedgerEntryChange) => {
        switch (entry.switch().name) {
            case 'ledgerEntryCreated':
                return contractData(contractId, entry.created().data())

            case 'ledgerEntryUpdated':
                return contractData(contractId, entry.updated().data())

            case 'ledgerEntryState':
                return contractData(contractId, entry.state().data())

            case 'ledgerEntryRemoved':
                // TODO: is it ever triggered by a Soroban contract?
                return none()
        }
    }
}

// extract contract storage from ledger entry data, if it's there
function contractData(
    contractId: string,
    data: sdk.xdr.LedgerEntryData
): Maybe<FieldsMap> {
    if (data.switch().name !== 'contractData') {
        return none()
    } else {
        const contractDataVal = data.contractData().val()
        if (
            Address.fromScAddress(data.contractData().contract()).toString() !==
            contractId
        ) {
            // this update does not apply to the target contract
            return none()
        }
        if (contractDataVal.switch().name === 'scvContractInstance') {
            // the contract instance gives us the storage
            const instance = contractDataVal.instance()

            if (instance.storage() === undefined) {
                // the previous state, which is undefined when no storage was ever created
                return just(OrderedMap<string, any>())
            } else {
                const fields: FieldsMap = instance
                    .storage()
                    .reduce((map, entry) => {
                        const key = sdk.scValToNative(entry.key()).toString()
                        const val = sdk.scValToNative(entry.val())
                        return map.set(key, val)
                    }, OrderedMap<string, any>())

                return just(fields)
            }
        }

        return none()
    }
}
