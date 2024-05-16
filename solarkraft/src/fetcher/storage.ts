/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

/**
 * Storage data for contract invocations.
 *
 * Igor Konnov, 2024.
 */

import JSONbigint from 'json-bigint'
import { OrderedMap } from 'immutable'
import { join } from 'node:path/posix'
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs'

const JSONbig = JSONbigint({ useNativeBigInt: true })

/**
 * Ordered mapping from field names to their native values (JS),
 * as produced by Stellar SDK.
 */
export type FieldsMap = OrderedMap<string, any>

/**
 * A storage entry for a performed contract call.
 */
export interface ContractCallEntry {
    /**
     * The ledger number, which is also called the height or the block number in other systems.
     */
    height: number
    /**
     * Transaction hash.
     */
    txHash: string
    /**
     * The address of the contract being called.
     */
    contractId: string
    /**
     * The name of the method.
     */
    method: string
    /**
     * The arguments passed to the method, in native JS.
     */
    methodArgs: any[]
    /**
     * The return value in native JS.
     */
    returnValue: any
    /**
     * Ordered mapping from field names to their native values (JS).
     * This mapping contains values only for the fields that have been created
     * or updated by a transaction in the past. It may happen that `fields` contains
     * fewer fields than `oldFields`, when the contract deletes some fields
     * from the storage. Also, `fields` may become empty when the storage
     * goes over TTL.
     */
    fields: FieldsMap
    /**
     * Ordered mapping from field names to their native values (JS).
     * This mapping contains values only for the fields that were set
     * before the call took place. The map `oldFields` may become empty
     * when the storage goes over TTL.
     */
    oldFields: FieldsMap
}

/**
 * Store a contract call entry in the file storage.
 * @param root the storage root directory
 * @param entry a call entry
 */
export function saveContractCallEntry(root: string, entry: ContractCallEntry) {
    const filename = getEntryFilename(root, entry)
    // convert OrderedMaps to arrays
    const simplified = {
        ...entry,
        fields: entry.fields.toArray(),
        oldFields: entry.oldFields.toArray(),
    }
    const contents = JSONbig.stringify(simplified)
    writeFileSync(filename, contents)
    return filename
}

/**
 * Load a contract call entry in the file storage.
 * @param root the storage root directory
 * @param entry a call entry
 * @returns the loaded call entry
 */
export function loadContractCallEntry(filename: string): ContractCallEntry {
    const contents = readFileSync(filename)
    const loaded = JSONbig.parse(contents)
    return {
        height: loaded.height as number,
        contractId: loaded.contractId as string,
        txHash: loaded.txHash as string,
        method: loaded.method as string,
        methodArgs: loaded.methodArgs as any[],
        returnValue: loaded.returnValue,
        fields: OrderedMap<string, any>(loaded.fields),
        oldFields: OrderedMap<string, any>(loaded.oldFields),
    }
}

/**
 * Get the filename for a contract call entry. Create the parent directory, if required.
 *
 * @param root storage root
 * @param entry call entry
 * @returns the filename
 */
function getEntryFilename(root: string, entry: ContractCallEntry) {
    const dir = getOrCreateDirectory(root, entry)
    return join(dir, `entry-${entry.txHash}.json`)
}

/**
 * Return the parent directory for an entry.
 * If this directory does not exist, create it recursively.
 *
 * @param root storage root
 * @param entry call entry
 * @returns the directory name
 */
function getOrCreateDirectory(root: string, entry: ContractCallEntry) {
    const directory = join(root, entry.contractId, entry.height.toString())
    mkdirSync(directory, { recursive: true })
    return directory
}
