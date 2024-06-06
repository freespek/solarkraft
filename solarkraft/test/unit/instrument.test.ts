// an example unit test to copy from

import { assert } from 'chai'
import { describe, it } from 'mocha'

import { OrderedMap } from 'immutable'

import {
    instrumentMonitor,
    tlaJsonTypeOfPrimitive,
    tlaJsonOfNative,
    isTlaName,
} from '../../src/instrument.js'

import { instrumentedMonitor as expected } from './verify.instrumentedMonitor.js'
import { instrumentedMonitor as expected2 } from './verify.instrumentedMonitor2.js'
import { instrumentedMonitor as expected3 } from './verify.instrumentedMonitor3.js'

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
function assertProperVec(v: any[], forceVec: boolean = true) {
    const tla = tlaJsonOfNative(v, forceVec)
    assert.propertyVal(tla, 'type', 'Untyped')
    assert.propertyVal(tla, 'kind', 'OperEx')
    assert.propertyVal(tla, 'oper', 'TUPLE')
    assert.deepPropertyVal(
        tla,
        'args',
        v.map((arg) => tlaJsonOfNative(arg, forceVec))
    )
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
        assertProperVec([key, v[key]], true)
    })
}

// Assert that `tlaJsonOfNative` returns a proper Apalache/TLA+ `[ k1 |-> v1, k2 |-> v2 ]` for the Soroban `struct` `v`
function assertProperStruct(v: any) {
    const tla = tlaJsonOfNative(v)
    assert.propertyVal(tla, 'type', 'Untyped')
    assert.propertyVal(tla, 'kind', 'OperEx')
    assert.propertyVal(tla, 'oper', 'RECORD')
    assert.property(tla, 'args')
    assert(tla.args.length % 2 == 0)
    let lastKey = undefined
    tla.args.forEach((el, index) => {
        if (index % 2 == 0) {
            // a key
            assert.propertyVal(el, 'type', 'Untyped')
            assert.propertyVal(el, 'kind', 'ValEx')
            assert.property(el, 'value')
            assert.propertyVal(el.value, 'kind', 'TlaStr')
            assert.property(el.value, 'value')
            assert.typeOf(el.value.value, 'string')
            assert(isTlaName(el.value.value))
            lastKey = el.value.value
        } else {
            // a value
            assert.propertyVal(el, 'type', 'Untyped')
            assert.propertyVal(el, 'kind', 'ValEx')
            assert.property(el, 'value')
            assert.propertyVal(el.value, 'value', v[lastKey])
        }
    })
}

// Assert that `tlaJsonOfNative` returns a proper Apalache/TLA+ Variant for the Soroban `enum` value `v`
function assertProperEnum(v: any) {
    const tla = tlaJsonOfNative(v)
    assert.propertyVal(tla, 'type', 'Untyped')
    assert.propertyVal(tla, 'kind', 'OperEx')
    assert.propertyVal(tla, 'oper', 'Variants!Variant')
    assert.property(tla, 'args')
    assert.typeOf(tla.args[0].value.value, 'string')
    tla.args.forEach((variantArg, index) => {
        assert.propertyVal(variantArg, 'type', 'Untyped')
        assert.propertyVal(variantArg, 'kind', 'ValEx')
        assert.property(variantArg, 'value')
        assert.propertyVal(variantArg.value, 'value', v[index])
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
            timestamp: 1716393856,
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
            timestamp: 1716393856,
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

    it('instruments variables declared in the monitor, but absent in the data', () => {
        const monitor = {
            modules: [
                {
                    declarations: [
                        { kind: 'TlaVarDecl', name: 'is_initialized' },
                        { kind: 'TlaVarDecl', name: 'absent' },
                    ],
                },
            ],
        }
        const contractCall = {
            timestamp: 1716393856,
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
        assert.deepEqual(expected2, instrumented)
    })

    it('fails when type hint is needed but not given', () => {
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
            timestamp: 1716393856,
            height: 100,
            txHash: '0xasdf',
            contractId: '0xqwer',
            returnValue: null,
            method: 'Claim',
            methodArgs: [['MaybeEnum']],
            fields: OrderedMap<string, any>([['is_initialized', false]]),
            oldFields: OrderedMap<string, any>([['is_initialized', false]]),
            typeHints: undefined,
        }
        assert.throws(() => instrumentMonitor(monitor, contractCall))
    })

    it('succeeds when type hint is correctly supplied', () => {
        const monitor = {
            modules: [
                {
                    declarations: [],
                },
            ],
        }
        const contractCall = {
            timestamp: 1716393856,
            height: 100,
            txHash: '0xasdf',
            contractId: '0xqwer',
            returnValue: null,
            method: 'foo',
            methodArgs: [['MaybeEnum'], ['MaybeVec']],
            fields: OrderedMap<string, any>(),
            oldFields: OrderedMap<string, any>(),
            typeHints: {
                methods: { foo: [[{ enum: [] }, { vec: 'Str' }], 'BAR'] },
            },
        }
        const instrumented = instrumentMonitor(monitor, contractCall)
        assert.deepEqual(expected3, instrumented)
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
        assertProperMap({ 'a%': 2, b: 3 })
        assertProperMap({ a: 2, _: 3 })
    })

    it('decodes Soroban struct values to Apalache JSON IR', () => {
        assertProperStruct({ some_long_name: 1 })
        assertProperStruct({ a: 2, b: 3 })
    })

    it('decodes Soroban enum values to Apalache JSON IR', () => {
        assertProperEnum(['A', 1])
        assertProperEnum(['B', 3, 44])
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

    it('recognizes TLA+ names', () => {
        assert.isTrue(isTlaName('a'))
        assert.isTrue(isTlaName('x'))
        assert.isTrue(isTlaName('3x'))
        assert.isTrue(isTlaName('x3'))
        assert.isTrue(isTlaName('some_long_name'))
        assert.isTrue(isTlaName('_x_'))

        assert.isFalse(isTlaName('3'))
        assert.isFalse(isTlaName('_'))
    })
})
