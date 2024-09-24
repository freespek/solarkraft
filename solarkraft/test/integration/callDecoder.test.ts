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
const CONTRACT_ID = 'CD4MXYZJKHXHEP7YK72L6K4Y6ANFVSXSTI3VPJXV5M4QFGF5PGH5PDDJ'

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
            'b05390b622fe133f73f2471c1b5c651e0bbafee85a7f5051012c50fa91a67e75'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: { instance: {}, temporary: {}, persistent: {} },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #2: Setter.set_u32([42u32])', async () => {
        const entry = await extractEntry(
            'e76a1b9e3e59528a3ddfe89954f17ff3d96eabc59332dc85b044b69443de8a2a'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42 },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #3: Setter.set_i32([-42u32])', async () => {
        const entry = await extractEntry(
            '556f1c0a1a0829213671f95827f343fb2910d07a6e7a017a56e1ff2ab3c4173d'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42 },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42, MY_I32: -42 },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #4: Setter.set_u64([42u64])', async () => {
        const entry = await extractEntry(
            '8f83f2c093fe4cef11f60e74d071494c9d0e1f4b4a288b7b7fa137aa9751195d'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42, MY_I32: -42 },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #5: Setter.set_i64([-42i64])', async () => {
        const entry = await extractEntry(
            '91f8d67b2224aa6ad47756a72b31b5139d790d94c16c4d7bddaad6ef149650af'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #6: Setter.set_u128([42u128])', async () => {
        const entry = await extractEntry(
            '8a640ba50e1b61eaa7865e10037fa8d04066c512c711081132ac4954f90ce398'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #7: Setter.set_i128([-42i128])', async () => {
        const entry = await extractEntry(
            'f4a51fcc957c5bbb3c6f54528a605dd09988c1fc1864c40e14d12ffacc6c0458'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #8: Setter.set_sym("hello")', async () => {
        const entry = await extractEntry(
            '39bf81d229de6295e5abffa24a128fac02c584a6e2c7b17c483579fe9ed544ad'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #9: Setter.set_bytes(0xbeef)', async () => {
        const entry = await extractEntry(
            'fa62c7c3fdc5a8aa7c76d83c4c7eca90b63eea72d87550933ca1b5e70a86fcd9'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #10: Setter.set_bytes32(...)', async () => {
        const entry = await extractEntry(
            'cf380860bbac39a5699af1d272296880020629a798af7c77b81787bba1582ffe'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #11: Setter.set_vec([[1i32, -2i32, 3i32]])', async () => {
        const entry = await extractEntry(
            '57ca932e4670d1b98bf657f0548f1f360c8a93b18c6c62f65c3307b167c2ccbf'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #12: Setter.set_map([{2u32: 3i32, 4u32: 5i32}])', async () => {
        const entry = await extractEntry(
            '1585b6e384eb52d03642c745682039e987ac93d747419b435c654b79e28dc928'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #13: Setter.set_address([GDIY...R4W4]', async () => {
        const entry = await extractEntry(
            '3aa904623cb321ce7c0fa4ad2d47ae90e1820bdce6f29ae339bc92c6d5f03a4b'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #14: Setter.set_struct([{"a"sym: 1u32, "b"sym: -100i128}])', async () => {
        const entry = await extractEntry(
            '8e13755bf402d2d9f9d981e0597f87b5b8af24f97e83bdfe5280757934315a48'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
    })

    it('call #15: Setter.set_enum([["B"sym, -200i128]])', async () => {
        const entry = await extractEntry(
            'b695cc284078f126f1b257d5475d9520061661f0f6a1d15b0ef073e7f0602d45'
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
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_ENUM: ['B', -200n],
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
    })
})
