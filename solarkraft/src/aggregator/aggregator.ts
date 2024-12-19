/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
// State aggregator. We do not expect this aggregator to be efficient.
// It is a proof of concept that is needed to implement input generation.
//
// See: https://github.com/freespek/solarkraft/issues/153
//
// Igor Konnov, 2024

import {
    ContractCallEntry,
    emptyContractStorage,
    FieldsMap,
    FullState,
    MultiContractStorage,
} from '../fetcher/storage.js'

/**
 * Apply the updates from a contract call to the state.
 * @param state the state to update
 * @param callEntry the call entry to apply
 * @returns the updated state
 */
export function applyCallToState(
    state: FullState,
    callEntry: ContractCallEntry
): FullState {
    if (callEntry.txSuccess !== true) {
        console.warn(
            `Skipping failed transaction ${callEntry.txHash}`
        )
        return state
    }

    return {
        contractId: callEntry.contractId,
        timestamp: callEntry.timestamp,
        height: callEntry.height,
        latestTxHash: callEntry.txHash,
        storage: updateContractStorage(
            state.storage,
            callEntry.oldStorage,
            callEntry.storage
        ),
    }
}

function updateContractStorage(
    fullStorage: MultiContractStorage,
    oldStorage: MultiContractStorage,
    storage: MultiContractStorage
): MultiContractStorage {
    let updatedStorage = fullStorage
    for (const [contractId, contractStorage] of storage) {
        const contractFullStorage =
            fullStorage.get(contractId) ?? emptyContractStorage()
        const contractOldStorage =
            oldStorage.get(contractId) ?? emptyContractStorage()
        updatedStorage = updatedStorage.set(contractId, {
            instance: updateFieldsMap(
                contractFullStorage.instance,
                contractOldStorage.instance,
                contractStorage.instance
            ),
            persistent: updateFieldsMap(
                contractFullStorage.persistent,
                contractOldStorage.persistent,
                contractStorage.persistent
            ),
            temporary: updateFieldsMap(
                contractFullStorage.temporary,
                contractOldStorage.temporary,
                contractStorage.temporary
            ),
        })
    }
    return updatedStorage
}

function updateFieldsMap(
    fullStorageFields: FieldsMap,
    oldFieldsInCall: FieldsMap,
    fieldsInCall: FieldsMap
): FieldsMap {
    let updatedFields = fullStorageFields
    // note that storage entries in ContractCallEntry are small subsets of the full storage
    for (const key of oldFieldsInCall.keys()) {
        if (!fieldsInCall.has(key)) {
            updatedFields = updatedFields.delete(key)
        }
    }
    for (const [key, value] of fieldsInCall) {
        updatedFields = updatedFields.set(key, value)
    }
    return updatedFields
}
