// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { join } from 'node:path'
import { spawn } from 'nexpect'
import { assert } from 'chai'
import { yieldListEntriesForContract } from '../../src/fetcher/storage.js'

import {
    SETTER_CONTRACT_ADDR,
    SETTER_HEIGHT,
} from './generated/setterHardcoded.js'

describe('verify', () => {
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

    it('fetches and verifies', function (done) {
        // fetch the transactions like in fetch.test.ts
        const solarkraftHome = './test/e2e/tla'
        this.timeout(120000)

        // this callback is called after the fetch command has finished
        const fetchCallback = (err) => {
            assert(!err, `fetch failed: ${err}`)
            // verify all of the transactions
            let ncalls = 0
            let nchecked = 0
            for (const e of yieldListEntriesForContract(
                SETTER_CONTRACT_ADDR,
                join(solarkraftHome, '.stor', SETTER_CONTRACT_ADDR)
            )) {
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
                        assert(!err, `verify failed: ${err}`)
                        nchecked++
                        console.log(`checked ${e.txHash} of ${ncalls}`)
                        if (nchecked >= ncalls) {
                            // technically, we may have a race condition
                            // between spawning and finishing verification
                            assert(ncalls > 0, 'no transactions checked')
                            // we have to tell mocha that we are done
                            done()
                        }
                    })
                ncalls++
            }
        }

        spawn(
            'solarkraft',
            [
                'fetch',
                `--home=${solarkraftHome}`,
                `--id=${SETTER_CONTRACT_ADDR}`,
                `--height=${SETTER_HEIGHT}`,
                '--timeout=10',
            ],
            { verbose: false }
        )
            .wait(`Target contract: ${SETTER_CONTRACT_ADDR}...`)
            .wait(`Fetching the ledger for ${SETTER_HEIGHT}`)
            .wait(/\+ save: \d+/)
            .run(fetchCallback)
    })
})
