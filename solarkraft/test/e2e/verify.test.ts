// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

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

    const txs = [
        'df32f09514abedbf9d4b843fb8ad53de81d74b62914c4c9faf290760324abd0f',
        '8f97b05ce36b9f2b2988150131cd8990bd018dfcace5250ad5df5e872af436bf',
        '03a01ff64502f5d992bb28e784212235a5da55ebb68c75345f58364559cb5921',
        '337365516cbe5f9287bc6b81428fb94be08d8e5d1ba580454d0907378c06c0da',
        'ad3c4d82300b50972fdbc887c20bb7771c722a1c63bd44c8e8d4ddf4597f4143',
        'e3dba60ada9fd7cb1d3490cf72b5e53e17b154e237aed2d2dcacfec6b0b1d883',
        '762575ca214bd9cb85824356b799689bf4920aafcac24f790defac54b1a0cc9d',
        '98c2468aad6626b59230b4fcc83d921897cbf76dc49f7bea13e46e443035a682',
        'df673ab5399dcbd5ac434c0ac51c53e9b9367b1d2507ab7e4b8cebfe3e796499',
        '101111c4a7087070366d035f59cc20b80215231955f9253c4ad85ff94f1dc61b',
        '9c46c29a985ceeaffe567dc405a757805ff0496fe5740228abcb22b7aefa3e64',
        '4da2e37effde690b6cf2c11ade5fc2f4e72971b37866f6d75fa2ea5728b6be6e',
        'b39cf7d57120fa72bde0aec90f709551ff777132e1b5db89e2575ee942d8bb70',
        '1bd53234a4eb4f9316f63bd77f4a2c191bded377ad3c53caeb7ed285f9d77d64',
        '406d278860b5531dd1443532f3457c5daa288e8eb0007d2a8e2aa0127e87949e',
    ]
    txs.forEach(tx => {
        it(`verifies the setter contract (tx ${tx})`, function (done) {
            this.timeout(150_000)
            spawn(
                `solarkraft verify --home test/e2e/tla/ --txHash ${tx} --monitor test/e2e/tla/setter_mon.tla`
            )
                .wait('[OK]')
                .run(done)
        })
    })
})
