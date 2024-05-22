// an example unit test to copy from

import { assert } from 'chai'
import { describe, it } from 'mocha'

import { OrderedMap } from 'immutable'

import {
    instrumentMonitor,
    tlaJsonTypeOfPrimitive,
    tlaJsonOfNative,
} from '../../src/instrument.js'

import { instrumentedMonitor as expected } from './verify.instrumentedMonitor.js'

// Assert that `tlaJsonOfNative` returns a proper TLA+ `ValEx` for the primitive JS value `v`
function assertProperValExOfPrimitive(v: any) {
    const valEx = tlaJsonOfNative(v)
    assert.propertyVal(valEx, 'type', 'Untyped')
    assert.propertyVal(valEx, 'kind', 'ValEx')
    assert.property(valEx, 'value')
    assert.propertyVal(valEx.value, 'value', v)
}

// Assert that `tlaJsonOfNative` returns a proper TLA+ `ValEx` for the Soroban `Buffer` `v`
function assertProperValExOfBuffer(v: any, expected: string) {
    const valEx = tlaJsonOfNative(v)
    assert.propertyVal(valEx, 'type', 'Untyped')
    assert.propertyVal(valEx, 'kind', 'ValEx')
    assert.property(valEx, 'value')
    assert.propertyVal(valEx.value, 'kind', 'TlaStr')
    assert.propertyVal(valEx.value, 'value', expected)
}

// Assert that `tlaJsonOfNative` returns a proper TLA+ sequence constructor for the Soroban `Vec` `v`
function assertProperVec(v: any[]) {
    const tla = tlaJsonOfNative(v)
    assert.propertyVal(tla, 'type', 'Untyped')
    assert.propertyVal(tla, 'kind', 'OperEx')
    assert.propertyVal(tla, 'oper', 'TUPLE')
    assert.deepPropertyVal(tla, 'args', v.map(tlaJsonOfNative))
}

// Assert that `tlaJsonOfNative` returns a proper Apalache/TLA+ `SetAsFun({<<k1, v1>>, <<k2, v2>>, ...})` for the Soroban `Map` `v`
function assertProperMap(v: any) {
    const tla = tlaJsonOfNative(v)
    assert.propertyVal(tla, 'type', 'Untyped')
    assert.propertyVal(tla, 'kind', 'OperEx')
    assert.propertyVal(tla, 'oper', 'Apalache!SetAsFun')
    assert.property(tla, 'args')
    assert.equal(tla.args.length, 1)
    const setEnum = tla.args[0]
    assert.propertyVal(setEnum, 'type', 'Untyped')
    assert.propertyVal(setEnum, 'kind', 'OperEx')
    assert.propertyVal(setEnum, 'oper', 'SET_ENUM')
    assert.property(setEnum, 'args')
    setEnum.args.forEach((tuple) => {
        const key = tuple.args[0].value.value
        assertProperVec([key, v[key]])
    })
}

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

    it('decodes primitive Soroban values to Apalache JSON IR ValEx', () => {
        assertProperValExOfPrimitive(true)
        assertProperValExOfPrimitive(false)
        assertProperValExOfPrimitive(-42000)
        assertProperValExOfPrimitive(0)
        assertProperValExOfPrimitive(1)
        assertProperValExOfPrimitive(42000)
        assertProperValExOfPrimitive('')
        assertProperValExOfPrimitive('asdf')
    })

    it('decodes Soroban Buffer values to Apalache JSON IR ValEx', () => {
        assertProperValExOfBuffer({ type: 'Buffer', data: [0] }, '00')
        assertProperValExOfBuffer({ type: 'Buffer', data: [190, 239] }, 'beef')
    })

    it('decodes Soroban Vec values to Apalache JSON IR', () => {
        assertProperVec([])
        assertProperVec([1, 2, 3])
        assertProperVec(['a', 'b'])
    })

    it('decodes Soroban Map values to Apalache JSON IR', () => {
        assertProperMap({})
        assertProperMap({ 1: 'a' })
        assertProperMap({ a: 2, b: 3 })
    })

    it('finds appropriate types for primitive values', () => {
        assert.equal('TlaBool', tlaJsonTypeOfPrimitive(true))
        assert.equal('TlaBool', tlaJsonTypeOfPrimitive(false))
        assert.equal('TlaInt', tlaJsonTypeOfPrimitive(-42000))
        assert.equal('TlaInt', tlaJsonTypeOfPrimitive(0))
        assert.equal('TlaInt', tlaJsonTypeOfPrimitive(1))
        assert.equal('TlaInt', tlaJsonTypeOfPrimitive(42000))
        assert.equal('TlaStr', tlaJsonTypeOfPrimitive(''))
        assert.equal('TlaStr', tlaJsonTypeOfPrimitive('asdf'))
    })
})
