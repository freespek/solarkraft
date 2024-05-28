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
import {
    existsSync,
    mkdirSync,
    readFileSync,
    readdirSync,
    writeFileSync,
} from 'node:fs'

const JSONbig = JSONbigint({ useNativeBigInt: true })

/**
 * Ordered mapping from field names to their native values (JS),
 * as produced by Stellar SDK.
 */
export type FieldsMap = OrderedMap<string, any>

export type VerificationStatus = 'ok' | 'fail' | 'unverified'
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

    /**
     * Flag which tracks whether this particular entry has already been verified, and, if it has been, the verification result.
     */
    verificationStatus?: VerificationStatus
}

/**
 * A listing entry.
 */
export interface ListEntry {
    contractId: string
    height: number
    txHash: string
    verificationStatus: VerificationStatus
}

/**
 * Serializable fetcher state.
 */
export interface FetcherState {
    /**
     * For every contract id, store the ledger height,
     * up to which the transactions were fetched.
     * Similar to Stellar SDK, we are using number instead of bigint.
     */
    heights: OrderedMap<string, number>
}

/**
 * Given the solarkraft home, construct the path to store the transactions.
 * @param solarkraftHome path to solarkraft home (or project directory)
 * @returns path to the transactions storage
 */
export function storagePath(solarkraftHome: string): string {
    return join(solarkraftHome, '.stor')
}

/**
 * Store a contract call entry in the file storage.
 * @param home the storage root directory
 * @param entry a call entry
 */
export function saveContractCallEntry(home: string, entry: ContractCallEntry) {
    const filename = getEntryFilename(storagePath(home), entry)
    const verificationStatus: VerificationStatus =
        entry.verificationStatus ?? 'unverified'
    // convert OrderedMaps to arrays
    const simplified = {
        ...entry,
        fields: entry.fields.toArray(),
        oldFields: entry.oldFields.toArray(),
        verificationStatus: verificationStatus,
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
        verificationStatus: loaded.verificationStatus ?? 'unverified',
    }
}

/**
 * Generate storage entries for a given contract id in a path.
 * @param contractId contract identifier (address)
 * @param path the path to the contract storage
 */
export function* yieldListEntriesForContract(
    contractId: string,
    path: string
): Generator<ListEntry> {
    for (const dirent of readdirSync(path, { withFileTypes: true })) {
        // match ledger heights, which are positive integers
        if (dirent.isDirectory() && /^[0-9]+$/.exec(dirent.name)) {
            // This directory may contain several transactions for the same height.
            const height = Number.parseInt(dirent.name)
            for (const ledgerDirent of readdirSync(join(path, dirent.name), {
                withFileTypes: true,
            })) {
                // match all storage entries, which may be reported in different cases
                const matcher = /^entry-([0-9a-fA-F]+)\.json$/.exec(
                    ledgerDirent.name
                )
                if (ledgerDirent.isFile() && matcher) {
                    const txHash = matcher[1]
                    const filename = join(
                        ledgerDirent.path,
                        `entry-${txHash}.json`
                    )
                    const contents = JSONbig.parse(
                        readFileSync(filename, 'utf-8')
                    )
                    const status =
                        contents['verificationStatus'] ?? 'unverified'
                    yield {
                        contractId,
                        height,
                        txHash,
                        verificationStatus: status,
                    }
                }
            }
        }
    }
}

/**
 * Load fetcher state from the storage.
 * @param root the storage root directory
 * @returns the loaded state
 */
export function loadFetcherState(home: string): FetcherState {
    const filename = getFetcherStateFilename(home)
    if (!existsSync(filename)) {
        // just return an empty map
        return {
            heights: OrderedMap<string, number>(),
        }
    } else {
        const contents = readFileSync(filename)
        const loaded = JSONbig.parse(contents)
        return {
            heights: OrderedMap<string, number>(loaded.heights),
        }
    }
}

/**
 * Store the fetcher config.
 * @param home the storage root directory
 * @param state fetcher state
 */
export function saveFetcherState(home: string, state: FetcherState): string {
    const filename = getFetcherStateFilename(home)
    mkdirSync(home, { recursive: true })
    const simplified = {
        heights: state.heights.toArray(),
    }
    const contents = JSONbig.stringify(simplified)
    writeFileSync(filename, contents)
    return filename
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
 * Get the filename for the fetcher state.
 *
 * @param root storage root
 * @param entry call entry
 * @returns the filename
 */
function getFetcherStateFilename(root: string) {
    return join(root, 'fetcher-state.json')
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
