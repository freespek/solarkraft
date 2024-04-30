// an example unit test to copy from

import { assert } from 'chai'
import { describe, it } from 'mocha'

import { instrumentMonitor } from '../../src/instrument.js'

import { instrumentedMonitor as expected } from './verify.instrumentedMonitor.js'

describe('Apalache JSON instrumentor', () => {
    it('instruments TLA+ monitors', () => {
        const monitor = { modules: [{ declarations: [] }] }
        const state = [
            { name: 'is_initialized', type: 'TlaBool', value: false },
        ]
        const tx = {
            functionName: 'Claim',
            functionArgs: [{ type: 'TlaStr', value: 'alice' }],
            env: { timestamp: 100 },
            error: 'contract is not initialized',
        }

        const instrumented = instrumentMonitor(monitor, state, tx)
        assert.deepEqual(instrumented, expected)
    })
})
