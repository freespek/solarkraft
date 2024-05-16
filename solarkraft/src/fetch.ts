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
import JSONbigint from 'json-bigint'
import { extractContractCall } from './fetcher/callDecoder.js'

/**
 * Fetch transactions from the ledger
 * @param args the arguments parsed by yargs
 */
export async function fetch(args: any) {
    const contractId = args.id
    console.log(`Target contract: ${contractId}...`)
    console.log(`Fetching fresh transactions from: ${args.rpc}...`)
    /*
    // read the latest height cached from the latest invocation of fetch
    const cachedHeight = 0
    // fetch the actual height from the RPC endpoint
    const currentHeight = 12345
    let startHeight =
        args.height < 0 ? currentHeight + args.height : args.height
    startHeight = Math.max(startHeight, cachedHeight)
    console.log(`| ledger | cached | start |`)
    console.log(`| ${currentHeight}  | ${cachedHeight}   | ${startHeight} |\n`)
    */
    const startHeight = args.height

    const DURATION = 30
    const server = new Horizon.Server(args.rpc)
    console.log(`Fetching the ledger for ${startHeight}`)
    const response = await server.ledgers().ledger(startHeight).call()
    //console.log(response)
    const startCursor = (response as any).paging_token

    // See:
    // https://github.com/stellar/js-stellar-sdk/blob/master/test/integration/streaming_test.js
    const finish = (err) => {
        clearTimeout(timeout)
        closeHandler()
        console.error(err)
    }

    // TODO: work in progress
    const closeHandler = server
        .operations()
        .cursor(startCursor)
        .stream({
            onmessage: async (msg: any) => {
                if (msg.transaction_successful === true) {
                    ;(
                        await extractContractCall(
                            msg,
                            (id) => contractId === id
                        )
                    ).map((e) => {
                        console.log(`call => ${JSONbigint.stringify(e)}`)
                    })
                }
            },
            onerror: finish,
        })

    const timeout = setTimeout(finish, DURATION * 1000)
}
