/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * A command to aggregate the full contract state from the collected transactions.
 * This command is potentially expensive. In the long run, it makes sense to
 * collect the states from the archival nodes. For the time being, we aggregate
 * the states from the transactions directly, in order to evaluate the approach.
 *
 * We need this feature primarily for input generation. This is an experimental
 * feature in Phase 1. We always aggregate the state, starting with the minimal
 * available height. Obviously, there is a lot of room for improvement here.
 *
 * Although it is tempting to aggregate transactions directly in fetch.ts,
 * this is the wrong approach. Horizon may give us transactions out of order,
 * so we need to sort them by height before state aggregation.
 *
 * Igor Konnov, 2024
 */

import { existsSync, writeFileSync } from 'fs'
import { join } from 'path'
import { JSONbig } from './globals.js'
import {
    emptyFullState,
    loadContractCallEntry,
    storagePath,
    yieldListEntriesForContract,
} from './fetcher/storage.js'
import { applyCallToState } from './aggregator/aggregator.js'

/**
 * Aggregate the fetched transactions to compute the full contract state.
 * @param args the aggregator arguments
 */
export async function aggregate(args: any) {
    const storageRoot = storagePath(args.home)
    if (!existsSync(storageRoot)) {
        console.error(`The storage is empty. Run 'solarkraft fetch'`)
        return
    }

    const contractId = args.id

    // We have to sort the entries by height. Hence, we read them first and then sort.
    let lastEntry = undefined
    const entries = []
    for (const e of yieldListEntriesForContract(
        contractId,
        join(storageRoot, contractId)
    )) {
        if (e.height <= args.heightTo) {
            entries.push(e)
        }
        if (lastEntry && lastEntry.height === e.height) {
            // this should not happen on the testnet, as there is only one transaction per height
            console.warn(
                `Height ${e.height}: transactions ${e.txHash} and ${lastEntry.txHash} may be out of order`
            )
        }
        lastEntry = e
    }
    // sort the entries
    entries.sort((a, b) => a.height - b.height)

    // now we can aggregate the state
    let nentries = 0
    let state = emptyFullState()
    for (const entry of entries) {
        nentries++
        const txEntry = loadContractCallEntry(args.home, entry.txHash)
        if (txEntry.isRight()) {
            if (args.verbose) {
                console.log(`Height ${entry.height}: applied ${entry.txHash}`)
            }
            state = applyCallToState(state, txEntry.value)
        } else {
            console.error(
                `Failed to load the transaction ${entry.txHash}: ${txEntry.value}`
            )
            return
        }
    }

    // save the aggregated state
    const contents = JSONbig.stringify(state)
    writeFileSync(args.out, contents)
    if (args.verbose) {
        console.log(`Aggregated ${nentries} transactions into ${args.out}`)
    }
}
