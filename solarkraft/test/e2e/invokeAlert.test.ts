import { assert } from 'chai'
import { describe, it } from 'mocha'
import { spawn } from 'nexpect'

import { invokeAlert } from '../../src/verifier/invokeAlert.js'
import { Keypair, Networks } from '@stellar/stellar-sdk'
import { VerificationStatus } from '../../src/fetcher/storage.js'

// hard-coded contract id that has to be changed,
// when the Setter contract is redeployed via alert-deploy.sh
const CONTRACT_ID = 'CDRCCMLPCAKOZSEECX7EEXIPNPU32JGEKG3QMHKM7ZNO5IRBUE66DQ6O'
// const LocalRPC = 'https://localhost:8000/'
const TestnetRPC = 'https://soroban-testnet.stellar.org:443'

describe('alert contract invocation', () => {
    it('successfully submits a NoViolation', async function () {
        this.timeout(50000)

        // set up a new account and initial funds, to submit txs from
        const sourceKeypair = Keypair.random()
        try {
            await fetch(
                `https://friendbot.stellar.org?addr=${encodeURIComponent(
                    sourceKeypair.publicKey()
                )}`
            )
        } catch {
            assert(false)
        }

        const txHash = 'a'.repeat(64)

        const ret = await invokeAlert(
            TestnetRPC,
            sourceKeypair,
            Networks.TESTNET,
            CONTRACT_ID,
            txHash,
            VerificationStatus.NoViolation
        )

        assert(ret === VerificationStatus.NoViolation)
    })

    it('errors on bogus alert id', function (done) {
        this.timeout(50000)
        spawn(
            'solarkraft verify --home test/e2e/tla/ --txHash 406d278860b5531dd1443532f3457c5daa288e8eb0007d2a8e2aa0127e87949e --monitor test/e2e/tla/setter_mon.tla --alert bogus'
        )
            .wait('Invalid contract ID: bogus')
            .expect('No alert submitted.')
            .run(done)
    })

    it('alerts the contrat when specified', function (done) {
        this.timeout(50000)
        spawn(
            `solarkraft verify --home test/e2e/tla/ --txHash 406d278860b5531dd1443532f3457c5daa288e8eb0007d2a8e2aa0127e87949e --monitor test/e2e/tla/setter_mon.tla --alert ${CONTRACT_ID}`
        )
            .wait('Preparing to submit alert.')
            .wait('Transaction successful')
            .run(done)
    })
})
