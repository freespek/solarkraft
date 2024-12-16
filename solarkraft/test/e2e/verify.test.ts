// Integration tests for the `verify` command

import { before, describe, it } from 'mocha'

import { join } from 'node:path'
import { readdir, stat } from 'node:fs/promises'
import { spawn } from 'nexpect'
import { assert } from 'chai'
import { yieldListEntriesForContract } from '../../src/fetcher/storage.js'

import {
    SETTER_CONTRACT_ADDR,
    SETTER_HEIGHT,
} from './generated/setterHardcoded.js'

const solarkraftHome = './test/e2e/tla'

describe('verify on pre-saved storage', () => {
    it('errors on missing monitor', function (done) {
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor doesnotexist'
        )
            .wait('The monitor file doesnotexist does not exist.')
            .expect('[Error]')
            .run(done)
    })

    it('errors on no monitors given', function (done) {
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor'
        )
            .wait('[Error]')
            .run(done)
    })

    it('errors on missing tx hash', function (done) {
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash doesnotexist --monitor test/e2e/tla/timelock_mon1.tla'
        )
            .wait('[Error]')
            .run(done)
    })

    it('reports success on okay monitor1', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor test/e2e/tla/timelock_mon1.tla'
        )
            .wait('[OK]')
            .run(done)
    })

    it('reports success on okay monitor2', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor test/e2e/tla/timelock_mon2.tla'
        )
            .wait('[OK]')
            .run(done)
    })

    it('reports success on okay monitor3', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor test/e2e/tla/timelock_mon3.tla'
        )
            .wait('[OK]')
            .run(done)
    })

    it('reports success on two okay monitors', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor test/e2e/tla/timelock_mon1.tla test/e2e/tla/timelock_mon2.tla'
        )
            .wait('[OK]')
            .run(done)
    })

    it('reports failure on deadlocking monitor', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor test/e2e/tla/timelock_mon1_instrumented_fail.tla'
        )
            .wait('unable to reproduce the transaction')
            .wait('[Fail]')
            .run(done)
    })

    it('reports failure on deadlocking monitor, if another succeeding monitor is present', function (done) {
        this.timeout(50_000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor test/e2e/tla/timelock_mon1_instrumented_fail.tla test/e2e/tla/timelock_mon2.tla'
        )
            .wait('[Fail]')
            .run(done)
    })
})

// we need this test to populate the storage
describe('fetches the setter contract', () => {
    const expectedTransactions = 16
    const contractDir = join(solarkraftHome, '.stor', SETTER_CONTRACT_ADDR)
    const timeout = 120000

    before('fetches and verifies', function (done) {
        // fetch the transactions like in fetch.test.ts
        this.timeout(timeout)
        spawn(
            'solarkraft',
            [
                'fetch',
                `--home=${solarkraftHome}`,
                `--id=${SETTER_CONTRACT_ADDR}`,
                `--height=${SETTER_HEIGHT}`,
                '--timeout=10',
            ],
            { verbose: true }
        )
            .wait(`Target contract: ${SETTER_CONTRACT_ADDR}...`)
            .wait(`Fetching the ledger for ${SETTER_HEIGHT}`)
            // 16 transactions are expected, it's important to wait for all of them!
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .wait(/\+ save: \d+/)
            .run(done)
    })

    async function waitForEntries(waitTimeout) {
        // Wait until the directory is created.
        // In the worst case, the test suite times out.
        let remainingSec = waitTimeout
        while (remainingSec > 0) { 
            try {
                const stats = await stat(contractDir)
                if (stats.isDirectory()) {
                    const fileCount = 
                        (await readdir(contractDir, { withFileTypes: true }))
                            .filter(item => item.isDirectory()).length
                    if (fileCount >= expectedTransactions) {
                        // the directory exists and it contains the required number of files
                        return
                    }
                }
            } catch (error) {
                if (error.code !== 'ENOENT') {
                    // Unexpected error, rethrow
                    throw error
                }
                // ENOENT means the directory does not exist yet, so we continue waiting
            }
            // sleep for 1 sec
            await new Promise(resolve => setTimeout(resolve, 1000))
            remainingSec -= 1000
        }
    }

    // we need this to run the loop below
    it(`fetched ${expectedTransactions} transactions`, async function done () {
        this.timeout(timeout)
        await waitForEntries(timeout)
        // count the entries via yieldListEntriesForContract
        let txCount = 0
        for (const e of yieldListEntriesForContract(SETTER_CONTRACT_ADDR, contractDir)) {
            assert(e.contractId === SETTER_CONTRACT_ADDR,
                `transaction ${e.txHash} has wrong contractId = ${e.contractId}`)
            txCount++
        }
        assert(txCount === expectedTransactions, `expected ${expectedTransactions} transactions`)
        done()
    })

    describe('verifies the setter contract', async () => {
        before('wait for entries', async function () {
            await waitForEntries(timeout)
        })

        // dynamically add a test for each transaction, so they can be run asynchronously
        for (const e of yieldListEntriesForContract(SETTER_CONTRACT_ADDR, contractDir)) {
            it(`verify fetched transaction ${e.txHash}`, function (done) {
                this.timeout(timeout)
                spawn(
                    'solarkraft',
                    [
                        'verify',
                        `--home=${solarkraftHome}`,
                        `--txHash=${e.txHash}`,
                        '--monitor=./test/e2e/tla/setter_mon.tla',
                    ],
                    { verbose: true }
                )
                    .wait('[OK]')
                    .run((err) => {
                        assert(!err, `verification error: ${err}`)
                        done()
                    })
            })
        }
    })
})
