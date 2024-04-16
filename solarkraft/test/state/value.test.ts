import { assert } from 'chai'
import { describe, it } from 'mocha'

import {IntValue_u32, IntValue_i32, IntValue_u64, IntValue_i64,IntValue_u128, IntValue_i128, SymValue, AddrValue}  from '../../src/state/value.js'

describe('Integer tests', () => {
    it('asserts 32-bit integer constructors respect bounds', () => {
        assert.throws( () => {new IntValue_u32(-1n)}, RangeError )
        assert.throws( () => {new IntValue_u32(2n**32n + 1n)}, RangeError )
        assert.throws( () => {new IntValue_i32(-(2n**31n) - 1n)}, RangeError )
        assert.throws( () => {new IntValue_i32(2n**31n)}, RangeError )

        const x_u32 = new IntValue_u32(2n**20n)
        assert(x_u32.isValid)
        assert(x_u32.type === "u32")
        assert(x_u32.val === 2n**20n)

        const x_i32 = new IntValue_i32(-(2n**20n))
        assert(x_i32.isValid)
        assert(x_i32.type === "i32")
        assert(x_i32.val === -(2n**20n))
    })

    it('asserts 64-bit integer constructors respect bounds', () => {
        assert.throws( () => {new IntValue_u64(-1n)}, RangeError )
        assert.throws( () => {new IntValue_u64(2n**64n + 1n) }, RangeError )
        assert.throws( () => {new IntValue_i64(-(2n**63n) - 1n)}, RangeError )
        assert.throws( () => {new IntValue_i64(2n**63n)}, RangeError )

        const x_u64 = new IntValue_u64(2n**40n)
        assert(x_u64.isValid)
        assert(x_u64.type === "u64")
        assert(x_u64.val === 2n**40n)

        const x_i64 = new IntValue_i64(-(2n**40n))
        assert(x_i64.isValid)
        assert(x_i64.type === "i64")
        assert(x_i64.val === -(2n**40n))
    })

    it('asserts 128-bit integer constructors respect bounds', () => {
        assert.throws( () => {new IntValue_u128(-1n)}, RangeError )
        assert.throws( () => {new IntValue_u128(2n**128n + 1n)}, RangeError )
        assert.throws( () => {new IntValue_i128(-(2n**127n) - 1n)}, RangeError )
        assert.throws( () => {new IntValue_i128(2n**127n)}, RangeError )

        const x_u128 = new IntValue_u128(2n**80n)
        assert(x_u128.isValid)
        assert(x_u128.type === "u128")
        assert(x_u128.val === 2n**80n)

        const x_i128 = new IntValue_i128(-(2n**80n))
        assert(x_i128.isValid)
        assert(x_i128.type === "i128")
        assert(x_i128.val === -(2n**80n))
    })
})

describe('Stringlike tests', () => {
    it('asserts SymValue constructors properly check requirements', () => {
        assert.throws( () => {new SymValue("waaaaaaaaaaaaaaaaay tooooooooooooooooooooooooo loooooooooooooooooooooooooooooong")}, TypeError )
        
        assert.throws( () => {new SymValue('\u2615')}, TypeError )

        const s = new SymValue("FOO")
        assert(s.val === 'FOO')
    })

    it('asserts Address constructors properly check requirements', () => {
        assert.throws( () => {new AddrValue("LOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOONG")}, TypeError )
        
        assert.throws( () => {new AddrValue('========================================================')}, TypeError )

        assert.throws( () => {new AddrValue('FOO')}, TypeError )

        const s = new AddrValue("ALICE000000000000000000000000000000000000000000000000000")
        assert(s.val === "ALICE000000000000000000000000000000000000000000000000000")
    })
})

describe('Array tests', () => {
    it('asserts something about arrays (TODO)', () => {
        // TODO, placeholder
    })
})