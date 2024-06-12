// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

// Tests against the last tx of the deployed setter contract

describe('fetch', () => {
    it('fails to fetch when provided typemap does not exist', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft fetch --typemap bogusFile --rpc https://horizon-testnet.stellar.org --id CA6DAY7MPOKVL5BB3CVKMAPX3UGFURQCNLTT4DPPF6MDNA3RSERQZ55Y --height 9391 --timeout 10'
        )
            .wait('The typemap file bogusFile does not exist.')
            .wait('[Error]')
            .run(done)
    })

    it('fetches transactions', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft fetch --rpc https://horizon-testnet.stellar.org --id CA6DAY7MPOKVL5BB3CVKMAPX3UGFURQCNLTT4DPPF6MDNA3RSERQZ55Y --height 9391 --timeout 10'
        )
            .wait(
                'Target contract: CA6DAY7MPOKVL5BB3CVKMAPX3UGFURQCNLTT4DPPF6MDNA3RSERQZ55Y'
            )
            .wait('Fetching the ledger for 9391')
            .wait('+ save: 9391')
            .run(done)
    })
})
