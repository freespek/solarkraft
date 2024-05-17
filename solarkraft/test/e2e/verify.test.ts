// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

describe('verify', () => {
    it('errors on missing file', function (done) {
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
        this.timeout(50000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash timelock --monitor test/e2e/tla/timelock_mon1_instrumented_fail.tla test/e2e/tla/timelock_mon2.tla'
        )
            .wait('[Fail]')
            .run(done)
    })
})
