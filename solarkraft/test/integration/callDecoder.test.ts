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
const CONTRACT_ID = 'CA6DAY7MPOKVL5BB3CVKMAPX3UGFURQCNLTT4DPPF6MDNA3RSERQZ55Y'

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
            '169ae9177a0e36d89c64c54e2367969d956f75d07a5c0f5d809b39b4b5a437e1'
        )
        assert.isDefined(entry.timestamp)
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
            '86d5004773275ba2581c366eacf0e8ab4441d40d75ebf0a4697c9feffcc0d279'
        )
        assert.isDefined(entry.timestamp)
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
            '40e0c91dca003d11ac2317cf522bdf947e8048e41a9bf59cd85e8232bc4a9fab'
        )
        assert.isDefined(entry.timestamp)
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
            '06f61c92360915e8155ee3c1eb1c7aa3d0a3227c4cac10975dad4f56f8b59c11'
        )
        assert.isDefined(entry.timestamp)
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
            '8bbbae5a0803e6d8cfdc67c0285083a22f32423ced0d423313e32d4e9c7b943f'
        )
        assert.isDefined(entry.timestamp)
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
            '45dd47df1201a67f4a91762af6405d9df63315fdcec09815fef8e0fd5e8ab498'
        )
        assert.isDefined(entry.timestamp)
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
            'e9b2e056dc2889e3c974b9b5d3aeedbe0718c37bb1e7219b1e8cdda16416e8ed'
        )
        assert.isDefined(entry.timestamp)
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
            '653f5e2c316d174b6cb653b9eae28f1dc0c1d296cde98f2eb85ba82d7b71b8a3'
        )
        assert.isDefined(entry.timestamp)
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
            'ac2d10afb665dc154f486f60575e336997e9b45da8f7dbc6c4c7ecc184638c1a'
        )
        assert.isDefined(entry.timestamp)
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
            'bcd7eea353e28f8f2232bb703c9c350290fd6705574cebab046eff3f52159857'
        )
        assert.isDefined(entry.timestamp)
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
            'b8106ddd3a4e6533a1543d9d0c471f9c23c059f9523ef552f21340db8571bd11'
        )
        assert.isDefined(entry.timestamp)
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
            'efa5382b575d95d56a3386d5727f1405e840a64b790522b956a5e9d89c9b4bc7'
        )
        assert.isDefined(entry.timestamp)
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
            'f2ffa0da716a75a1ac99740856eb2451caefe512679f89ac5b9da587fee025fa'
        )
        assert.isDefined(entry.timestamp)
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

    it('call #14: Setter.set_struct([{"a"sym: 1u32, "b"sym: -100i128}])', async () => {
        const entry = await extractEntry(
            '0c3ae16ab47e78ae665ad8129cc54c615800c2a416c4518dfc7dd98aae2d8937'
        )
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_struct')
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

    it('call #15: Setter.set_enum([["B"sym, -200i128]])', async () => {
        const entry = await extractEntry(
            '9fb49e22ba82c36f2c02e69ecf0cc9755c00cc057c5fede469be2877ba6fa3b7'
        )
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_enum')
        assert.deepEqual(entry.methodArgs, [['B', -200n]])
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
            ['MY_ENUM', ['B', -200n]],
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
