import { assert } from 'chai'
import { describe, it } from 'mocha'

import { invokeAlert } from '../../src/invokeAlert.js'
import { Keypair, Networks } from '@stellar/stellar-sdk'
import { MonitorAnalysisStatus } from '../../src/MonitorAnalysis.js'

// hard-coded contract id that has to be changed,
// when the Setter contract is redeployed via alert-deploy.sh
const CONTRACT_ID = 'CDXBZCCRCCIHSHHXONEFX4DOD5XSM34EA7M22JIVU35ZDQ6ZBADIARLB'
// const LocalRPC = 'https://localhost:8000/'
const TestnetRPC = 'https://soroban-testnet.stellar.org:443'

describe('Alert contract invocation', () => {
    it('Submits a NoViolation', async function () {
        this.timeout(50000)

        // set up a new account adn initial funds, to submit txs from
        const sourceKeypair = Keypair.random()
        try {
            await fetch(
                `https://friendbot.stellar.org?addr=${encodeURIComponent(
                    sourceKeypair.publicKey()
                )}`
            )
        } catch (e) {
            assert(false)
        }

        const txHash = 'a'.repeat(64)

        const ret = await invokeAlert(
            TestnetRPC,
            sourceKeypair,
            Networks.TESTNET,
            CONTRACT_ID,
            txHash,
            MonitorAnalysisStatus.NoViolation
        )

        assert(ret === MonitorAnalysisStatus.NoViolation)
    })
})
