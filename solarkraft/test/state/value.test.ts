import { assert } from 'chai'
import { describe, it } from 'mocha'

import { isValid, u32, i32, u64, i64, u128, i128, symb, addr, bytes, bytesN, vec, map, bool, Value, u32T, toArr, KeyValuePair, mapFromKV } from '../../src/state/value.js'

describe('Integer tests', () => {
    it('asserts 32-bit integer constructors respect bounds', () => {
        assert.throws(() => { u32(-1n) }, RangeError)
        assert.throws(() => { u32(2n ** 32n + 1n) }, RangeError)
        assert.throws(() => { i32(-(2n ** 31n) - 1n) }, RangeError)
        assert.throws(() => { i32(2n ** 31n) }, RangeError)

        const x_u32 = u32(2n ** 20n)
        assert(isValid(x_u32))
        assert(x_u32.type === "u32")
        assert(x_u32.val === 2n ** 20n)

        const x_i32 = i32(-(2n ** 20n))
        assert(isValid(x_i32))
        assert(x_i32.type === "i32")
        assert(x_i32.val === -(2n ** 20n))
    })

    it('asserts 64-bit integer constructors respect bounds', () => {
        assert.throws(() => { u64(-1n) }, RangeError)
        assert.throws(() => { u64(2n ** 64n + 1n) }, RangeError)
        assert.throws(() => { i64(-(2n ** 63n) - 1n) }, RangeError)
        assert.throws(() => { i64(2n ** 63n) }, RangeError)

        const x_u64 = u64(2n ** 40n)
        assert(isValid(x_u64))
        assert(x_u64.type === "u64")
        assert(x_u64.val === 2n ** 40n)

        const x_i64 = i64(-(2n ** 40n))
        assert(isValid(x_i64))
        assert(x_i64.type === "i64")
        assert(x_i64.val === -(2n ** 40n))
    })

    it('asserts 128-bit integer constructors respect bounds', () => {
        assert.throws(() => { u128(-1n) }, RangeError)
        assert.throws(() => { u128(2n ** 128n + 1n) }, RangeError)
        assert.throws(() => { i128(-(2n ** 127n) - 1n) }, RangeError)
        assert.throws(() => { i128(2n ** 127n) }, RangeError)

        const x_u128 = u128(2n ** 80n)
        assert(isValid(x_u128))
        assert(x_u128.type === "u128")
        assert(x_u128.val === 2n ** 80n)

        const x_i128 = i128(-(2n ** 80n))
        assert(isValid(x_i128))
        assert(x_i128.type === "i128")
        assert(x_i128.val === -(2n ** 80n))
    })
})

describe('Stringlike tests', () => {
    it('asserts SymValue constructors properly check requirements', () => {
        assert.throws(() => { symb("waaaaaaaaaaaaaaaaay tooooooooooooooooooooooooo loooooooooooooooooooooooooooooong") }, TypeError)
        assert.throws(() => { symb('\u2615') }, TypeError)

        const s = symb("FOO")
        assert(s.val === 'FOO')
    })

    it('asserts Address constructors properly check requirements', () => {
        assert.throws(() => { addr("LOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOONG") }, TypeError)
        assert.throws(() => { addr('========================================================') }, TypeError)
        assert.throws(() => { addr('FOO') }, TypeError)

        const s = addr("ALICE000000000000000000000000000000000000000000000000000")
        assert(s.val === "ALICE000000000000000000000000000000000000000000000000000")
    })
})

describe('Collection tests', () => {
    it('asserts array constructors properly assert length equality and child validity', () => {
        const uintArr3 = [u32(1n), u32(2n), u32(3n)]
        const invalidU32arr: u32T[] = [{ type: "u32", val: -1n }]

        assert.throws(() => { bytes(invalidU32arr) }, TypeError) // child not valid
        assert.throws(() => { bytesN(invalidU32arr) }, TypeError) // child not valid

        const customVariable: Value = { type: "arr", val: [] }
        const customFixed: Value = { type: "arr", val: [], len: 10 }

        assert(isValid(customVariable))
        assert(!isValid(customFixed))

        const variableArr = bytes(uintArr3)
        const fixedArr = bytesN(uintArr3)

        assert(isValid(variableArr))
        assert(isValid(fixedArr))

        assert(variableArr.val === fixedArr.val)
        assert(variableArr.val === uintArr3)
        assert(variableArr.type === fixedArr.type)
        assert(variableArr.type === "arr")

        assert(!Object.keys(variableArr).includes("len"))
        assert(fixedArr.len === uintArr3.length)
    })

    it('asserts vector constructors properly assert child validity', () => {
        const homogeneousArr = [u64(0n), u64(0n), u64(0n)]
        const heterogeneousArr = [bool(false), symb("fOo")]
        const vecWithInvalid: Value[] = [{ type: "u64", val: -1n }]

        assert.throws(() => { vec(vecWithInvalid) }, TypeError)

        const homVec = vec(homogeneousArr)
        const hetVec = vec(heterogeneousArr)

        assert(homVec.val.length == homogeneousArr.length)
        assert(hetVec.val.length == heterogeneousArr.length)
    })

    it('asserts basic map constructors properly assert child validity', () => {
        const k0 = u32(0n)
        const k1 = u32(1n)
        const alice = addr("ALICE000000000000000000000000000000000000000000000000000")
        const bob = addr("BOB00000000000000000000000000000000000000000000000000000")

        const mapValid: Map<Value, Value> =
            new Map()
                .set(k0, alice)
                .set(k1, bob)

        const mapInvalidVal: Map<Value, Value> =
            new Map().set(k0, { type: "addr", val: "ALICE" })
        const mapInvalidKey: Map<Value, Value> =
            new Map().set({ type: "u32", val: -1n }, bob)

        assert.throws(() => { map(mapInvalidKey) }, TypeError)
        assert.throws(() => { map(mapInvalidVal) }, TypeError)

        const valdiMap = map(mapValid)
        const asArr = toArr(valdiMap)

        assert(asArr.length === 2)
        assert(asArr[0].length === 2)
        assert(asArr[1].length === 2)

        assert(asArr[0][0] === k0)
        assert(asArr[0][1] === alice)
        assert(asArr[1][0] === k1)
        assert(asArr[1][1] === bob)
    })

    it('asserts map array constructors properly assert child validity', () => {
        const k0 = u32(0n)
        const k1 = u32(1n)
        const alice = addr("ALICE000000000000000000000000000000000000000000000000000")
        const bob = addr("BOB00000000000000000000000000000000000000000000000000000")

        const arrValid: KeyValuePair[] = [[k0, alice], [k1, bob]]

        const arrInvalidVal: KeyValuePair[] = [[k0, { type: "addr", val: "ALICE" }]]
        const arrInvalidKey: KeyValuePair[] = [[{ type: "u32", val: -1n }, bob]]
        const arrInvalidDup: KeyValuePair[] = [[k0, alice], [k0, bob]]

        assert.throws(() => { mapFromKV(arrInvalidVal) }, TypeError)
        assert.throws(() => { mapFromKV(arrInvalidKey) }, TypeError)
        assert.throws(() => { mapFromKV(arrInvalidDup) }, TypeError)

        const valdiMap = mapFromKV(arrValid)
        const asArr = toArr(valdiMap)

        assert(asArr.length === arrValid.length)
        assert(asArr[0].length === arrValid[0].length)
        assert(asArr[1].length === arrValid[0].length)

        assert(asArr[0][0] === arrValid[0][0])
        assert(asArr[0][1] === arrValid[0][1])
        assert(asArr[1][0] === arrValid[1][0])
        assert(asArr[1][1] === arrValid[1][1])
    })
})