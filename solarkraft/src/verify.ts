/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

import { spawnSync } from 'child_process'
import { rmSync } from 'fs'
import { existsSync, readFileSync, writeFileSync } from 'node:fs'
import path from 'node:path'

import { temporaryFile } from 'tempy'

import { instrumentMonitor, stateFromItf } from './instrument.js'

// TODO(#34): fix hardcoded path to Apalache
const APALACHE_DIST = '/opt/apalache'
const APALACHE_BIN = path.join(APALACHE_DIST, 'bin', 'apalache-mc')

/**
 * Verify transactions fetched from the ledger
 * @param args the arguments parsed by yargs
 */
export function verify(args: any) {
    console.log(
        `*** WARNING: THIS IS A MOCK. NOTHING IS IMPLEMENTED YET. ***\n`
    )
    console.log(`Verifying transaction: ${args.txHash}...`)

    // Validate arguments
    if (!existsSync(args.monitor)) {
        console.log(`The monitor file ${args.monitor} does not exist.`)
        console.log('[Error]')
        return
    }
    if (!existsSync(args.state)) {
        console.log(`The ITF state file ${args.state} does not exist.`)
        console.log('[Error]')
        return
    }

    // Use Apalache to parse the monitor TLA+ to JSON IR
    console.log(`Parsing monitor ${args.monitor}`)
    const jsonFile = temporaryFile({ name: 'apalache_parsed.json' })
    const apalacheParse = spawnSync(APALACHE_BIN, [
        'typecheck',
        `--output=${jsonFile}`,
        args.monitor,
    ])

    if (apalacheParse.status != 0) {
        console.error(`Parsing monitor file ${args.monitor} failed:`)
        console.error(apalacheParse.stderr)
        return
    }

    // Read the monitor JSON IR
    let monitor: string
    try {
        monitor = JSON.parse(readFileSync(jsonFile, 'utf8'))
    } catch (err) {
        console.error(`Failed to read Apalache IR: ${err}`)
        return
    }

    // Read the state from ITF
    let itf: any
    try {
        itf = JSON.parse(readFileSync(args.state, 'utf8'))
    } catch (err) {
        console.error(`Failed to read state from ITF: ${err}`)
        return
    }

    // Instrument the monitor
    // TODO(#38): Read `state` and `tx` from fetcher output
    const state = stateFromItf(itf)
    const tx = {
        functionName: 'Claim',
        functionArgs: [{ type: 'TlaStr', value: 'alice' }],
        env: { timestamp: 100 },
        error: 'contract is not initialized',
    }
    const instrumented = instrumentMonitor(monitor, state, tx)

    // Write the instrumented monitor back to JSON
    try {
        writeFileSync(jsonFile, JSON.stringify(instrumented), 'utf8')
    } catch (err) {
        console.error(`Failed to write instrumented Apalache IR: ${err}`)
        return
    }

    // Check the instrumented spec with Apalache
    console.log(`Checking monitor ${args.monitor}`)
    const apalacheCheck = spawnSync(APALACHE_BIN, [
        'check',
        '--length=1',
        jsonFile,
    ])

    rmSync(jsonFile)

    // Report results
    switch (apalacheCheck.status) {
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
            console.error(
                `Internal error: Apalache failed with error code ${apalacheCheck.status}`
            )
            console.error(apalacheCheck.stdout.toString())
            console.error('[Error]')
            break
        }
    }
}
