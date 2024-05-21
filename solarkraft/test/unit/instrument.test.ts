// an example unit test to copy from

import { assert } from 'chai'
import { describe, it } from 'mocha'

import { OrderedMap } from 'immutable'

import {
    instrumentMonitor,
    tlaJsonTypeOfValue,
    tlaJsonValueOfNative,
} from '../../src/instrument.js'

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

    it('decodes Soroban values to Apalache JSON IR values', () => {
        assert.equal(true, tlaJsonValueOfNative(true))
        assert.equal(false, tlaJsonValueOfNative(false))
        assert.equal(-42000, tlaJsonValueOfNative(-42000))
        assert.equal(0, tlaJsonValueOfNative(0))
        assert.equal(1, tlaJsonValueOfNative(1))
        assert.equal(42000, tlaJsonValueOfNative(42000))
        assert.equal('', tlaJsonValueOfNative(''))
        assert.equal('asdf', tlaJsonValueOfNative('asdf'))
        assert.equal('00', tlaJsonValueOfNative({ type: 'Buffer', data: [0] }))
        assert.equal(
            'beef',
            tlaJsonValueOfNative({ type: 'Buffer', data: [190, 239] })
        )
    })

    it('finds appropriate types for values', () => {
        assert.equal('TlaBool', tlaJsonTypeOfValue(true))
        assert.equal('TlaBool', tlaJsonTypeOfValue(false))
        assert.equal('TlaInt', tlaJsonTypeOfValue(-42000))
        assert.equal('TlaInt', tlaJsonTypeOfValue(0))
        assert.equal('TlaInt', tlaJsonTypeOfValue(1))
        assert.equal('TlaInt', tlaJsonTypeOfValue(42000))
        assert.equal('TlaStr', tlaJsonTypeOfValue(''))
        assert.equal('TlaStr', tlaJsonTypeOfValue('asdf'))
        assert.equal('TlaStr', tlaJsonTypeOfValue('00'))
        assert.equal('TlaStr', tlaJsonTypeOfValue('beef'))
    })
})
