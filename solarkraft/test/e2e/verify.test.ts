// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

describe('verify', () => {
    it('fails on missing file', function (done) {
        spawn('solarkraft verify --txHash mimimi --monitor doesnotexist')
            .wait('The monitor file doesnotexist does not exist.')
            .expect('[Error]')
            .run(done)
    })

    it('reports success on okay monitor', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --txHash mimimi --monitor test/e2e/tla/timelock_mon1_instrumented_okay.tla'
        )
            .wait('[OK]')
            .run(done)
    })

    it('reports failure on deadlocking monitor', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --txHash mimimi --monitor test/e2e/tla/timelock_mon1_instrumented_fail.tla'
        )
            .wait('Monitor is unable to reproduce the transaction')
            .expect('[Fail]')
            .run(done)
    })
})
