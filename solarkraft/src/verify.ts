/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * The `solarkraft verify` command.
 *
 * Verifies transactions against a set of Solarkraft monitor specifications.
 *
 * @author Thomas Pani, 2024
 */

import { spawnSync } from 'child_process'
import { rmSync } from 'fs'
import { existsSync, readFileSync, writeFileSync } from 'node:fs'
import path from 'node:path'

import { globSync } from 'glob'
import { temporaryFile } from 'tempy'
import { Either, left, right, mergeInOne } from '@sweet-monads/either'

import { loadContractCallEntry, storagePath } from './fetcher/storage.js'
import { instrumentMonitor } from './instrument.js'

type Result<T> = Either<string, T>
type ApalacheResult = Result<void>

// TODO(#34): fix hardcoded path to Apalache
const APALACHE_DIST = '/opt/apalache'
const APALACHE_BIN = path.join(APALACHE_DIST, 'bin', 'apalache-mc')

/**
 * Parse the TLA+ file at `monitorTlaPath` and return its JSON IR.
 * @param monitorTlaPath Path to the monitor's TLA+ file.
 * @returns Parsing result in Apalache's JSON IR.
 */
function getApalacheJsonIr(monitorTlaPath: string): Result<string> {
    const tempfile = temporaryFile({ name: 'apalache_parsed.json' })

    // Use Apalache to parse the monitor TLA+ to JSON IR
    const apalacheParse = spawnSync(APALACHE_BIN, [
        'typecheck',
        `--output=${tempfile}`,
        monitorTlaPath,
    ])

    // Check for `typecheck` errors
    if (apalacheParse.status != 0) {
        return left(
            `Parsing monitor file ${monitorTlaPath} failed:\n${apalacheParse.stderr}`
        )
    }

    // Read the monitor JSON IR
    try {
        const jsonIr = JSON.parse(readFileSync(tempfile, 'utf8'))
        rmSync(tempfile)
        return right(jsonIr)
    } catch (err) {
        return left(`Failed to read Apalache IR: ${err}`)
    }
}

/**
 * Check the instrumented monitor with Apalache.
 * @param monitor Monitor in JSON IR instrumented with ledger state and transaction.
 * @returns `right(modelCheckingResult)` or `left(errStr)` if some internal error occurred.
 *          `modelCheckingResult` is `right(null)` if the transaction passes the monitor, or
 *          `left(reasonStr)` if the transaction cannot be reproduced (i.e., if Apalache detects a deadlock).
 */
function apalacheCheck(monitor: string): Result<ApalacheResult> {
    const tempfile = temporaryFile({ name: 'instrumented_monitor.json' })

    // Write the instrumented monitor back to JSON
    try {
        writeFileSync(tempfile, JSON.stringify(monitor), 'utf8')
    } catch (err) {
        return left(`Failed to write instrumented Apalache IR: ${err}`)
    }

    // Check the instrumented spec with Apalache
    const child = spawnSync(APALACHE_BIN, ['check', '--length=1', tempfile])

    rmSync(tempfile)

    // Report results
    switch (child.status) {
        case 0:
            return right(right(null))
        case 12:
            return right(left('unable to reproduce the transaction'))
        default:
            return left(
                `Internal error: Apalache failed with error code ${child.status}\n\n${child.stdout}`
            )
    }
}

/**
 * Verify transactions fetched from the ledger
 * @param args the arguments parsed by yargs
 */
export function verify(args: any) {
    console.log(`Verifying transaction: ${args.txHash}\n`)

    // Validate arguments
    if (args.monitor.length < 1) {
        console.log(`No monitor given.`)
        console.log('[Error]')
        return
    }
    for (const monitor of args.monitor) {
        if (!existsSync(monitor)) {
            console.log(`The monitor file ${args.monitor} does not exist.`)
            console.log('[Error]')
            return
        }
    }

    // Resolve fetcher entry in storage from txHash
    const entryPaths = globSync(
        path.join(storagePath(args.home), '**', `entry-${args.txHash}.json`)
    )
    if (entryPaths.length === 0) {
        console.error(
            `No entries found for tx hash ${args.txHash}. Run 'solarkraft fetch' first.`
        )
        console.log('[Error]')
        return
    }
    if (entryPaths.length > 1) {
        console.error(
            `Too many entries (${entryPaths.length}) found for tx hash ${args.txHash}.`
        )
        console.log('[Error]')
        return
    }
    const entryPath = entryPaths[0]

    // Read the state from fetcher output
    const contractCall = loadContractCallEntry(entryPath)

    // Check all monitors
    const resultsPerMonitor: Result<ApalacheResult>[] = args.monitor.map(
        (monitorPath: string) =>
            getApalacheJsonIr(monitorPath)
                .map((jsonIr: any) => instrumentMonitor(jsonIr, contractCall))
                .chain(apalacheCheck)
                // Print the monitor's result
                .map((apalacheResult) => {
                    const errorStringOrOK = apalacheResult.map(() => 'OK').value
                    console.log(
                        `${path.basename(monitorPath)}: ${errorStringOrOK}`
                    )
                    return apalacheResult
                })
                .mapLeft((error) => {
                    console.log(
                        `${path.basename(monitorPath)}: Internal error, see below`
                    )
                    return error
                })
    )

    // Print accumulated result
    mergeInOne(resultsPerMonitor)
        .map((apalacheResults) => {
            mergeInOne(apalacheResults)
                .map(() => console.log('\n[OK]'))
                .mapLeft(() => console.log('\n[Fail]'))
        })
        .mapLeft((error) => {
            console.error(error)
            console.error('\n[Error]')
        })
}
