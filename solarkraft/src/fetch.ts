/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

/**
 * A fetcher of contract calls.
 *
 * Igor Konnov, 2024
 */

/**
 * The fetch command optionally accepts a --typemap argument, which should be a .json file with the following structure:
 *  {
 *   "methods":{
 *       "m1": [[T1_1, ..., T1_N1], R1],
 *        ...
 *       "mK": [[TK_1, ..., TK_NK], RK],
 *      },
 *   "variables": {
 *       "v1": T1
 *       ...
 *       "vM": TM
 *      }
 *  }
 *
 * Where `mi` keys are the names of the methods, `vi` keys the names of variables,
 * `Ti_j` is the type of the `j`-th argument to method `mi`,
 * `Ri` is the return type of method `mi`,
 *  and `Ti` is the type of the variable `vi`.
 *
 * Type syntax uses the following constructors:
 *  - { "vec": elemT } for Vec - typed values
 *  - { "map": [domT, cdmT]} for Map - typed values
 *  - { a1: T1, ..., an: Tn } for Struct - typed values
 *  - ENUM for enums
 * other literal types (e.g. Int) aren't required so they can be any string.
 *
 * Note that typemap types are used as hints, and as such are redundant for any method/variable where the type is unambiguous
 * from the transaction data json structure.
 * Concretely, type hints are only _necessary_ when dealing with nularry Enum values, or Enum values indexed by Symbols/Strings, since
 * those values are indistinguishable from vectors at the transaction data layer.
 */

import { Horizon } from '@stellar/stellar-sdk'
import { extractContractCall } from './fetcher/callDecoder.js'
import {
    loadFetcherState,
    saveContractCallEntry,
    saveFetcherState,
} from './fetcher/storage.js'
import { existsSync, readFileSync } from 'node:fs'

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

    const typemap = args.typemap
    const typemapJson = existsSync(typemap)
        ? JSON.parse(readFileSync(typemap, 'utf8'))
        : ({} as JSON)

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
        if (err) {
            console.error(err)
        }
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
                        (id) => contractId === id,
                        typemapJson
                    )
                    if (callEntryMaybe.isJust()) {
                        const entry = callEntryMaybe.value
                        console.log(`+ save: ${entry.height}`)
                        saveContractCallEntry(args.home, entry)
                    }
                } // TODO(#61): else: shall we also store reverted transactions?

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
