// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

describe('fetch', () => {
    it('fetches transactions', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft fetch --rpc https://horizon-testnet.stellar.org --id CC22QGTOUMERDNIYN7TPNX3V6EMPHQXVSRR3XY56EADF7YTFISD2ROND --height 1638368 --timeout 10'
        )
            .wait(
                'Target contract: CC22QGTOUMERDNIYN7TPNX3V6EMPHQXVSRR3XY56EADF7YTFISD2ROND'
            )
            .wait('Fetching the ledger for 1638368')
            .wait('+ save: 1638383')
            .run(done)
    })
})
