// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

import {
    SETTER_CONTRACT_HASH,
    SETTER_HEIGHT,
} from './generated/setterHardcoded.js'

// Tests against the last tx of the deployed setter contract

describe('fetch', () => {
    it('fails to fetch when provided typemap does not exist', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft',
            [
                'fetch',
                '--typemap=bogusFile',
                `--id=${SETTER_CONTRACT_HASH}`,
                `--height=${SETTER_HEIGHT}`,
                '--timeout=10',
            ],
            { verbose: false }
        )
            .wait('The typemap file bogusFile does not exist.')
            .wait('[Error]')
            .run(done)
    })

    it('fetches transactions', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft',
            [
                'fetch',
                `--id=${SETTER_CONTRACT_HASH}`,
                `--height=${SETTER_HEIGHT}`,
                '--timeout=10',
            ],
            { verbose: false }
        )
            .wait(`Target contract: ${SETTER_CONTRACT_HASH}...`)
            .wait(`Fetching the ledger for ${SETTER_HEIGHT}`)
            .wait(/\+ save: \d+/)
            .run(done)
    })
})
