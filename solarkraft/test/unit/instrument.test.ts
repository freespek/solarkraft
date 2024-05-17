// an example unit test to copy from

import { assert } from 'chai'
import { describe, it } from 'mocha'

import { OrderedMap } from 'immutable'

import { instrumentMonitor } from '../../src/instrument.js'

import { instrumentedMonitor as expected } from './verify.instrumentedMonitor.js'

describe('Apalache JSON instrumentor', () => {
    it('instruments TLA+ monitors', () => {
        const monitor = {
            modules: [
                {
                    declarations: [
                        { kind: 'TlaVarDecl', name: 'is_initialized' },
                    ],
                },
            ],
        }
        const contractCall = {
            height: 100,
            txHash: '0xasdf',
            contractId: '0xqwer',
            returnValue: null,
            method: 'Claim',
            methodArgs: ['alice'],
            fields: OrderedMap<string, any>([['is_initialized', false]]),
            oldFields: OrderedMap<string, any>([['is_initialized', false]]),
        }

        const instrumented = instrumentMonitor(monitor, contractCall)
        assert.deepEqual(expected, instrumented)
    })

    it('only instruments variables declared in the monitor', () => {
        const monitor = {
            modules: [
                {
                    declarations: [
                        { kind: 'TlaVarDecl', name: 'is_initialized' },
                    ],
                },
            ],
        }
        const contractCall = {
            height: 100,
            txHash: '0xasdf',
            contractId: '0xqwer',
            returnValue: null,
            method: 'Claim',
            methodArgs: ['alice'],
            fields: OrderedMap<string, any>([
                ['is_initialized', false],
                ['additional_variable', false],
            ]),
            oldFields: OrderedMap<string, any>([
                ['is_initialized', false],
                ['additional_variable', false],
            ]),
        }
        const instrumented = instrumentMonitor(monitor, contractCall)
        assert.deepEqual(expected, instrumented)
    })
})
