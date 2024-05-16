/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Storage data for contract invocations.
 *
 * Igor Konnov, 2024.
 */

import { OrderedMap } from 'immutable'

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
     * This mapping contains values only for the fields that have been set
     * by transactions.
     */
    fields: FieldsMap
    /**
     * Ordered mapping from field names to their native values (JS).
     * This mapping contains values only for the fields that were set
     * before the call took place.
     */
    oldFields: FieldsMap
}
