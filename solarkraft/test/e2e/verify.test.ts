// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

describe('verify', () => {
    it('fails on missing file', function (done) {
        spawn(
            'solarkraft verify --txHash mimimi --monitor doesnotexist --state test/e2e/tla/timelock_state.itf.json'
        )
            .wait('The monitor file doesnotexist does not exist.')
            .expect('[Error]')
            .run(done)
    })

    it('reports success on okay monitor1', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --txHash mimimi --monitor test/e2e/tla/timelock_mon1.tla --state test/e2e/tla/timelock_state.itf.json'
        )
            .wait('[OK]')
            .run(done)
    })

    it('reports success on okay monitor2', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --txHash mimimi --monitor test/e2e/tla/timelock_mon2.tla --state test/e2e/tla/timelock_state.itf.json'
        )
            .wait('[OK]')
            .run(done)
    })

    it('reports failure on deadlocking monitor', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --txHash mimimi --monitor test/e2e/tla/timelock_mon1_instrumented_fail.tla --state test/e2e/tla/timelock_state.itf.json'
        )
            .wait('Monitor is unable to reproduce the transaction')
            .expect('[Fail]')
            .run(done)
    })
})
