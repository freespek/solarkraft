/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Verify transactions fetched from the ledger
 * @param args the arguments parsed by yargs
 */

import { spawnSync } from 'child_process'
import { existsSync } from 'node:fs'
import path from 'node:path'

// TODO: fix hardcoded path to Apalache
const APALACHE_DIST = '/opt/apalache'
const APALACHE_BIN = path.join(APALACHE_DIST, 'bin', 'apalache-mc')

export function verify(args: any) {
    console.log(
        `*** WARNING: THIS IS A MOCK. NOTHING IS IMPLEMENTED YET. ***\n`
    )
    console.log(`Verifying transaction: ${args.txHash}...`)

    if (!existsSync(args.monitor)) {
        console.log(`The monitor file ${args.monitor} does not exist.`)
        console.log('[Error]')
        return
    }

    console.log(`Running Apalache (check ${args.monitor})...`)
    const child = spawnSync(APALACHE_BIN, ['check', '--length=1', args.monitor])

    switch (child.status) {
        case 0: {
            console.log('[OK]')
            break
        }
        case 12: {
            // Deadlock
            console.log('Monitor is unable to reproduce the transaction')
            console.log('[Fail]')
            break
        }
        default: {
            console.log(
                `Internal error: Apalache failed with error code ${child.status}`
            )
            console.log('[Error]')
            break
        }
    }
}
