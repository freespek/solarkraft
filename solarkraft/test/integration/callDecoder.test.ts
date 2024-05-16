/**
 * Integration tests that ensure that our contract decoder works correctly on the testnet.
 * These tests use hardcoded ledger entries that are created with:
 *
 * `ContractExamples/scripts/setter-populate.sh`
 *
 * In case the Stellar testnet is reset, we have to update the hardcoded entries.
 * The easiest way to do this is by exploring the contract transactions on https://stellar.expert/.
 */

import { Horizon } from '@stellar/stellar-sdk'
import { assert } from 'chai'
import { describe, it } from 'mocha'
import { extractContractCall } from '../../src/fetcher/callDecoder.js'
import { ContractCallEntry } from '../../src/fetcher/storage.js'
import { Maybe, none } from '@sweet-monads/maybe'

// Horizon instance that we use for testing
const HORIZON_URL = 'https://horizon-testnet.stellar.org'

// hard-coded contract id that has to be changed,
// when the Setter contract is redeployed via setter-populate.sh
const CONTRACT_ID = 'CC22QGTOUMERDNIYN7TPNX3V6EMPHQXVSRR3XY56EADF7YTFISD2ROND'

// 0xbeef
const beef = Buffer.from([0xbe, 0xef])

// 0xbeef0123456789beef0123456789beef0123456789ab
const bytes32 = Buffer.from([
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xbe, 0xef,
    0x01, 0x23, 0x45, 0x67, 0x89, 0xbe, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89,
    0xbe, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab,
])

// extract the only contract entry from a given ledger
async function extractEntry(txHash: string): Promise<ContractCallEntry> {
    const server = new Horizon.Server(HORIZON_URL)
    const operations = await server.operations().forTransaction(txHash).call()
    let resultingEntry: Maybe<ContractCallEntry> = none<ContractCallEntry>()
    for (const op of operations.records) {
        const entry = await extractContractCall(op, (id) => id === CONTRACT_ID)
        if (entry.isJust()) {
            assert(
                resultingEntry.isNone(),
                `found two call entries for contract ${CONTRACT_ID}, tx hash ${txHash}`
            )
            resultingEntry = entry
        }
    }

    if (resultingEntry.isJust()) {
        return resultingEntry.value
    } else {
        assert.fail(
            `expected non-empty call entry for contract ${CONTRACT_ID}, tx hash ${txHash}`
        )
    }
}

describe('call decoder from Horizon', () => {
    it('call #1: Setter.set_bool(true)', async () => {
        const entry = await extractEntry(
            '9fb12935fbadcd28aa220d076f11be631590d22c60977a53997a746898322ca3'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_bool')
        assert.deepEqual(entry.methodArgs, [true])
        assert.deepEqual(entry.returnValue, false)
        assert.deepEqual(entry.oldFields.toArray(), [])
        assert.deepEqual(entry.fields.toArray(), [['MY_BOOL', true]])
    })

    it('call #2: Setter.set_u32([42u32])', async () => {
        const entry = await extractEntry(
            '6e3b0f948326708f439036df4aa2b165de5be35448e23c56d7eb989e1112c807'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_u32')
        assert.deepEqual(entry.methodArgs, [42])
        assert.deepEqual(entry.returnValue, 0)
        assert.deepEqual(entry.oldFields.toArray(), [['MY_BOOL', true]])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_U32', 42],
        ])
    })

    it('call #3: Setter.set_i32([-42u32])', async () => {
        const entry = await extractEntry(
            '5638fc047c2ba312e0ec5077bcb97788c56c6047ffdb9d966d1de674a7a651c0'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_i32')
        assert.deepEqual(entry.methodArgs, [-42])
        assert.deepEqual(entry.returnValue, 0)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_U32', 42],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
        ])
    })

    it('call #4: Setter.set_u64([42u64])', async () => {
        const entry = await extractEntry(
            'bc280eb46635d7f9494b5723b8d6146186033489844b9610506af595864ad6a2'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_u64')
        assert.deepEqual(entry.methodArgs, [42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
    })

    it('call #5: Setter.set_i64([-42i64])', async () => {
        const entry = await extractEntry(
            '640615ad2c1b642920bcc25422c05503ab440bee3e0c04e193328ca7214afe25'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_i64')
        assert.deepEqual(entry.methodArgs, [-42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
    })

    it('call #6: Setter.set_u128([42u128])', async () => {
        const entry = await extractEntry(
            'afd928352182c7b1c93cb10052c56d290fbcdd9d99c1948f4d59b3c1853c1ffb'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_u128')
        assert.deepEqual(entry.methodArgs, [42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
    })

    it('call #7: Setter.set_i128([-42i128])', async () => {
        const entry = await extractEntry(
            '64f74cfe018d881cb6648e2311571b770304d471044187130791d179edd8cbb2'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_i128')
        assert.deepEqual(entry.methodArgs, [-42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
    })

    it('call #8: Setter.set_sym("hello")', async () => {
        const entry = await extractEntry(
            '10aedf3c4368b1eaba990dfea9a8372d5d03c6da938b9ca5aa7be330dc9908a5'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_sym')
        assert.deepEqual(entry.methodArgs, ['hello'])
        assert.deepEqual(entry.returnValue, 'NONE')
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
    })

    it('call #9: Setter.set_bytes(0xbeef)', async () => {
        const entry = await extractEntry(
            '59621a7b161c9eccbf797ca1125817947cedc57d86b78c4397761a7e7312f09e'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_bytes')
        assert.deepEqual(entry.methodArgs, [beef])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
    })

    it('call #10: Setter.set_bytes32(...)', async () => {
        const entry = await extractEntry(
            '476ed0e3f0db900d5ecd50bd3eab65924c89acf6c78b2866ce09f17f65d702de'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_bytes32')
        assert.deepEqual(entry.methodArgs, [bytes32])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
    })

    it('call #11: Setter.set_vec([[1i32, -2i32, 3i32]])', async () => {
        const entry = await extractEntry(
            'ff44c4f9ba29885f6e76ddc33f0f987a6e122682bbee99489b7594159036125c'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_vec')
        assert.deepEqual(entry.methodArgs, [[1, -2, 3]])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
    })

    it('call #12: Setter.set_map([{2u32: 3i32, 4u32: 5i32}])', async () => {
        const entry = await extractEntry(
            'dcea98f78c9ec655082cfeee76072ee736cf98a3d9df9243838ff4c1568c5bf1'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_map')
        assert.deepEqual(entry.methodArgs, [{ '2': 3, '4': 5 }])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
    })

    it('call #13: Setter.set_address([GDIY...R4W4]', async () => {
        const entry = await extractEntry(
            '85c63081689992b3b3f5013f083d74ecdad6ecab035ddd758323f634cd1cb1c8'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_address')
        assert.deepEqual(entry.methodArgs, [
            'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
        ])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
    })

    it('call #14: Setter.set_my_struct([{"a"sym: 1u32, "b"sym: -100i128}])', async () => {
        const entry = await extractEntry(
            '5fcb114c5e55d286f8bec90b1b6c52a242884c9594d4d49d6f4ff11994e08786'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_my_struct')
        assert.deepEqual(entry.methodArgs, [{ a: 1, b: -100n }])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
    })

    it('call #15: Setter.set_my_enum([["A"sym]])', async () => {
        const entry = await extractEntry(
            '4246f33f7d1258ccdfbbf3afde0f4ccd3de81e5bbecb355dcf3f557d31c7bb9c'
        )
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_my_enum')
        assert.deepEqual(entry.methodArgs, [['A']])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_ENUM', ['A']],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
    })
})
