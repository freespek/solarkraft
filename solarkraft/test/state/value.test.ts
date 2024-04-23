import { assert } from 'chai'
import { describe, it } from 'mocha'

import { OrderedMap } from 'immutable'
import {
    isValid,
    u32,
    i32,
    u64,
    i64,
    u128,
    i128,
    symb,
    addr,
    bytes,
    bytesN,
    vec,
    map,
    bool,
    Value,
    byte,
    toArr,
    KeyValuePair,
    mapFromKV,
    MapT,
    getFullType,
} from '../../src/state/value.js'

describe('Integer tests', () => {
    it('asserts 32-bit integer constructors respect bounds', () => {
        assert.throws(() => {
            u32(-1n)
        }, RangeError)
        assert.throws(() => {
            u32(2n ** 32n + 1n)
        }, RangeError)
        assert.throws(() => {
            i32(-(2n ** 31n) - 1n)
        }, RangeError)
        assert.throws(() => {
            i32(2n ** 31n)
        }, RangeError)

        const x_u32 = u32(2n ** 20n)
        assert(isValid(x_u32))
        assert(x_u32.type === 'u32')
        assert(x_u32.val === 2n ** 20n)

        const x_i32 = i32(-(2n ** 20n))
        assert(isValid(x_i32))
        assert(x_i32.type === 'i32')
        assert(x_i32.val === -(2n ** 20n))
    })

    it('asserts 64-bit integer constructors respect bounds', () => {
        assert.throws(() => {
            u64(-1n)
        }, RangeError)
        assert.throws(() => {
            u64(2n ** 64n + 1n)
        }, RangeError)
        assert.throws(() => {
            i64(-(2n ** 63n) - 1n)
        }, RangeError)
        assert.throws(() => {
            i64(2n ** 63n)
        }, RangeError)

        const x_u64 = u64(2n ** 40n)
        assert(isValid(x_u64))
        assert(x_u64.type === 'u64')
        assert(x_u64.val === 2n ** 40n)

        const x_i64 = i64(-(2n ** 40n))
        assert(isValid(x_i64))
        assert(x_i64.type === 'i64')
        assert(x_i64.val === -(2n ** 40n))
    })

    it('asserts 128-bit integer constructors respect bounds', () => {
        assert.throws(() => {
            u128(-1n)
        }, RangeError)
        assert.throws(() => {
            u128(2n ** 128n + 1n)
        }, RangeError)
        assert.throws(() => {
            i128(-(2n ** 127n) - 1n)
        }, RangeError)
        assert.throws(() => {
            i128(2n ** 127n)
        }, RangeError)

        const x_u128 = u128(2n ** 80n)
        assert(isValid(x_u128))
        assert(x_u128.type === 'u128')
        assert(x_u128.val === 2n ** 80n)

        const x_i128 = i128(-(2n ** 80n))
        assert(isValid(x_i128))
        assert(x_i128.type === 'i128')
        assert(x_i128.val === -(2n ** 80n))
    })
})

describe('Stringlike tests', () => {
    it('asserts SymValue constructors properly check requirements', () => {
        assert.throws(() => {
            symb(
                'waaaaaaaaaaaaaaaaay tooooooooooooooooooooooooo loooooooooooooooooooooooooooooong'
            )
        }, TypeError)
        assert.throws(() => {
            symb('\u2615')
        }, TypeError)

        const s = symb('FOO')
        assert(s.val === 'FOO')
    })

    it('asserts Address constructors properly check requirements', () => {
        assert.throws(() => {
            addr(
                'LOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOONG'
            )
        }, TypeError)
        assert.throws(() => {
            addr('========================================================')
        }, TypeError)
        assert.throws(() => {
            addr('FOO')
        }, TypeError)

        const s = addr(
            'ALICE000000000000000000000000000000000000000000000000000'
        )
        assert(
            s.val === 'ALICE000000000000000000000000000000000000000000000000000'
        )
    })
})

describe('Collection tests', () => {
    it('asserts array valididty chekcs properly assert length equality', () => {
        const arr3: byte[] = [0, 1, 0]

        const customVariable: Value = { type: 'arr', val: [] }
        const customFixed: Value = { type: 'arr', val: [], len: 10 }

        assert(isValid(customVariable))
        assert(!isValid(customFixed))

        const variableArr = bytes(arr3)
        const fixedArr = bytesN(arr3)

        assert(isValid(variableArr))
        assert(isValid(fixedArr))

        assert(variableArr.val === fixedArr.val)
        assert(variableArr.val === arr3)
        assert(variableArr.type === fixedArr.type)
        assert(variableArr.type === 'arr')

        assert(!Object.keys(variableArr).includes('len'))
        assert(fixedArr.len === arr3.length)
    })

    it('asserts vector constructors properly assert child validity', () => {
        const homogeneousArr = [u64(0n), u64(0n), u64(0n)]
        const heterogeneousArr = [bool(false), symb('fOo')]
        const vecWithInvalid: Value[] = [{ type: 'u64', val: -1n }]

        assert.throws(() => {
            vec(vecWithInvalid)
        }, TypeError)

        assert.throws(() => {
            vec(heterogeneousArr)
        }, TypeError)

        const homVec = vec(homogeneousArr)
        const hetVec = vec(heterogeneousArr, true)

        assert(homVec.val.length == homogeneousArr.length)
        assert(hetVec.val.length == heterogeneousArr.length)
    })

    it('asserts basic map constructors properly assert child validity', () => {
        const k0 = u32(0n)
        const k1 = u32(1n)
        const alice = addr(
            'ALICE000000000000000000000000000000000000000000000000000'
        )
        const bob = addr(
            'BOB00000000000000000000000000000000000000000000000000000'
        )

        const mapValid: MapT = OrderedMap<Value, Value>()
            .set(k0, alice)
            .set(k1, bob)

        const mapHetKey: MapT = OrderedMap<Value, Value>()
            .set(k0, alice)
            .set(u64(1n), bob)

        const mapHetVal: MapT = OrderedMap<Value, Value>()
            .set(k0, alice)
            .set(k1, symb('BOB'))

        const mapInvalidVal: MapT = OrderedMap<Value, Value>().set(k0, {
            type: 'addr',
            val: 'ALICE',
        })
        const mapInvalidKey: MapT = OrderedMap<Value, Value>().set(
            { type: 'u32', val: -1n },
            bob
        )

        assert.throws(() => {
            map(mapInvalidKey)
        }, TypeError)
        assert.throws(() => {
            map(mapInvalidVal)
        }, TypeError)

        assert.throws(() => {
            map(mapHetKey)
        }, TypeError)
        assert.throws(() => {
            map(mapHetVal)
        }, TypeError)

        const valdiMap = map(mapValid)
        const asArr = toArr(valdiMap)

        assert(asArr.length === 2)
        assert(asArr[0].length === 2)
        assert(asArr[1].length === 2)

        assert(asArr[0][0] === k0)
        assert(asArr[0][1] === alice)
        assert(asArr[1][0] === k1)
        assert(asArr[1][1] === bob)

        // check for no throws
        const hetMapKey = map(mapHetKey, true)
        const keyTypes = [...hetMapKey.val.keys()].map((x) => x.type)
        assert(keyTypes[0] !== keyTypes[1])

        const hetMapVal = map(mapHetVal, true)
        const valTypes = [...hetMapVal.val.values()].map((x) => x.type)
        assert(valTypes[0] !== valTypes[1])
    })

    it('asserts map array constructors properly assert child validity', () => {
        const k0 = u32(0n)
        const k1 = u32(1n)
        const alice = addr(
            'ALICE000000000000000000000000000000000000000000000000000'
        )
        const bob = addr(
            'BOB00000000000000000000000000000000000000000000000000000'
        )

        const arrValid: KeyValuePair[] = [
            [k0, alice],
            [k1, bob],
        ]

        const arrInvalidVal: KeyValuePair[] = [
            [k0, { type: 'addr', val: 'ALICE' }],
        ]
        const arrInvalidKey: KeyValuePair[] = [[{ type: 'u32', val: -1n }, bob]]
        const arrInvalidDup: KeyValuePair[] = [
            [k0, alice],
            [k0, bob],
        ]

        assert.throws(() => {
            mapFromKV(arrInvalidVal)
        }, TypeError)
        assert.throws(() => {
            mapFromKV(arrInvalidKey)
        }, TypeError)
        assert.throws(() => {
            mapFromKV(arrInvalidDup)
        }, TypeError)

        const valdiMap = mapFromKV(arrValid)
        const asArr = toArr(valdiMap)

        assert(asArr.length === arrValid.length)
        assert(asArr[0].length === arrValid[0].length)
        assert(asArr[1].length === arrValid[1].length)

        assert(asArr[0][0] === arrValid[0][0])
        assert(asArr[0][1] === arrValid[0][1])
        assert(asArr[1][0] === arrValid[1][0])
        assert(asArr[1][1] === arrValid[1][1])
    })
})

describe('Type tests', () => {
    it("Checks basic types' type tag is their full type", () => {
        const vals = [
            u32(0n),
            i32(0n),
            u64(0n),
            i64(0n),
            u128(0n),
            i128(0n),
            bool(true),
            addr('ALICE000000000000000000000000000000000000000000000000000'),
            symb('BOB'),
        ]

        assert(!vals.some((v) => v.type != getFullType(v)))
    })

    it('Checks byte array type is Bytes', () => {
        const bytesNoN = bytes([0, 1, 0, 129])
        const bytesWithN = bytesN([1, 0, 1, 0])

        assert(getFullType(bytesNoN) === 'Bytes')
        assert(getFullType(bytesWithN) === 'Bytes')
    })

    it('Checks vector type is Vec and heterogeneous vectors are distinctly typed', () => {
        const emptyVec = vec([], false)
        const homVec = vec([u32(0n), u32(1n)], false)
        const hetVec = vec([u32(0n), i32(0n), u32(0n)], true)
        const nestedHomVec = vec(
            [vec([u32(0n), u32(1n)], false), vec([u32(2n), u32(3n)], false)],
            false
        )
        const nestedHetVec = vec(
            [vec([u32(0n), u32(1n)], false), vec([u32(2n), i32(3n)], true)],
            true
        )

        assert(getFullType(emptyVec) === `Vec(T)`)
        assert(getFullType(homVec) === `Vec(u32)`)
        assert(getFullType(hetVec) === `<u32, i32, u32>`)
        assert(getFullType(nestedHomVec) === `Vec(Vec(u32))`)
        assert(getFullType(nestedHetVec) === `<Vec(u32), <u32, i32>>`)
    })

    it('Checks map type is Map and heterogeneous maps are distinclty typed', () => {
        const emptyMap = map(OrderedMap<Value, Value>(), false)

        const k0 = u32(0n)
        const k1 = u32(1n)
        const alice = symb('ALICE')
        const bob = symb('BOB')

        const homMap = map(
            OrderedMap<Value, Value>().set(k0, alice).set(k1, bob),
            false
        )

        const hetMapK = map(
            OrderedMap<Value, Value>().set(k0, alice).set(i32(1n), bob),
            true
        )

        const hetMapV = map(
            OrderedMap<Value, Value>()
                .set(
                    k0,
                    addr(
                        'ALICE000000000000000000000000000000000000000000000000000'
                    )
                )
                .set(k1, bob),
            true
        )

        const nestedHomMap = map(
            OrderedMap<Value, Value>()
                .set(
                    k0,
                    map(
                        OrderedMap<Value, Value>().set(k0, alice).set(k1, bob),
                        false
                    )
                )
                .set(
                    k1,
                    map(
                        OrderedMap<Value, Value>()
                            .set(u32(2n), symb('CHARLIE'))
                            .set(u32(3n), symb('DELTA')),
                        false
                    )
                ),
            false
        )

        const nestedHetMap = map(
            OrderedMap<Value, Value>()
                .set(
                    k0,
                    map(
                        OrderedMap<Value, Value>().set(k0, alice).set(k1, bob),
                        false
                    )
                )
                .set(
                    k1,
                    map(
                        OrderedMap<Value, Value>()
                            .set(u32(2n), symb('CHARLIE'))
                            .set(i32(3n), symb('DELTA')),
                        true
                    )
                ),
            true
        )

        assert(getFullType(emptyMap) === `(T1 -> T2)`)
        assert(getFullType(homMap) === `(u32 -> symb)`)
        assert(getFullType(hetMapK) === `((u32 -> symb) | (i32 -> symb))`)
        assert(getFullType(hetMapV) === `((u32 -> addr) | (u32 -> symb))`)
        assert(getFullType(nestedHomMap) === `(u32 -> (u32 -> symb))`)
        assert(
            getFullType(nestedHetMap) ===
                `((u32 -> (u32 -> symb)) | (u32 -> ((u32 -> symb) | (i32 -> symb))))`
        )
    })
})
