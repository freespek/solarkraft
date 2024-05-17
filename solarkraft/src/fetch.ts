/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

/**
 * A fetcher of contract calls.
 *
 * Igor Konnov, 2024
 */

import { Horizon } from '@stellar/stellar-sdk'
import { extractContractCall } from './fetcher/callDecoder.js'
import {
    loadFetcherState,
    saveContractCallEntry,
    saveFetcherState,
} from './fetcher/storage.js'

// how often to query for the latest synchronized height
const HEIGHT_FETCHING_PERIOD = 100

/**
 * Fetch transactions from the ledger
 * @param args the arguments parsed by yargs
 */
export async function fetch(args: any) {
    const server = new Horizon.Server(args.rpc)

    const contractId = args.id
    console.log(`Target contract: ${contractId}...`)
    let fetcherState = loadFetcherState(args.home)
    const cachedHeight = fetcherState.heights.get(contractId, 1)
    let lastHeight = args.height
    console.log(`Last cached height: ${cachedHeight}`)
    if (args.height < 0) {
        // how to fetch the latest height?
        console.log(`not implemented yet, starting with ${cachedHeight}`)
        lastHeight = cachedHeight
    } else if (args.height === 0) {
        lastHeight = cachedHeight
    } else {
        lastHeight = args.height
    }

    console.log(`Fetching fresh transactions from: ${args.rpc}...`)

    console.log(`Fetching the ledger for ${lastHeight}`)
    const response = await server.ledgers().ledger(lastHeight).call()
    const startCursor = (response as any).paging_token
    // timeout id, if a timeout is set below
    let timeout

    const done = (err) => {
        // Closing handler:
        // https://github.com/stellar/js-stellar-sdk/blob/master/test/integration/streaming_test.js
        clearTimeout(timeout)
        closeHandler()
        console.error(err)
    }

    // the number of received events
    let nEvents = 0

    // initiate the streaming loop
    const closeHandler = server
        .operations()
        .cursor(startCursor)
        .stream({
            onmessage: async (msg: any) => {
                if (msg.transaction_successful) {
                    const callEntryMaybe = await extractContractCall(
                        msg,
                        (id) => contractId === id
                    )
                    if (callEntryMaybe.isJust()) {
                        const entry = callEntryMaybe.value
                        console.log(`+ save: ${entry.height}`)
                        saveContractCallEntry(args.home, entry)
                    }
                } // else: shall we also store reverted transactions?

                nEvents++
                if (nEvents % HEIGHT_FETCHING_PERIOD === 0) {
                    // Fetch the height of the current message and persist it for the future runs.
                    // Note that messages may come slightly out of order, so the heights are not precise.
                    const tx = await msg.transaction()
                    lastHeight = Math.max(lastHeight, tx.ledger_attr)
                    console.log(`= at: ${lastHeight}`)
                    // Load and save the state. Other fetchers may work concurrently,
                    // so there is a possibility of overwriting an updated height.
                    // This will result in a fetcher doing additional work on the next run.
                    fetcherState = loadFetcherState(args.home)
                    fetcherState = {
                        ...fetcherState,
                        heights: fetcherState.heights.set(
                            contractId,
                            lastHeight
                        ),
                    }
                    saveFetcherState(args.home, fetcherState)
                }
            },
            onerror: done,
        })

    if (args.timeout > 0) {
        console.log(`Fetching transactions for ${args.timeout} seconds.`)
        timeout = setTimeout(done, args.timeout * 1000)
    } else {
        console.log('Fetching transactions indefinitely. Close with Ctrl-C.')
    }
}
