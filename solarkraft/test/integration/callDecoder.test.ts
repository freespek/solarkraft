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
const CONTRACT_ID = 'CCIVIIO6OFFCPUU22W5HRP3UOWUGLY54TRTQXV5Z3IEOFQDMKIA2JXTZ'

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
            'c7629f7deaeaf7f4450eddfa4756d252af5cab8aef4547ffb621b826eae3a2cf'
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
                temporary: { MY_BOOL: true },
                persistent: { MY_BOOL: true },
            },
        })
    })

    it('call #2: Setter.set_u32([42u32])', async () => {
        const entry = await extractEntry(
            'f29f0f4f4156acf58862f316472cc8fc153e687b85af915c8a9e11dd1c41bf26'
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
                temporary: { MY_U32: 42 },
                persistent: { MY_U32: 42 },
            },
        })
    })

    it('call #3: Setter.set_i32([-42u32])', async () => {
        const entry = await extractEntry(
            '9f5c0ce5c23f3e9508f14c6800bbdf0f5e598e7a78c38205df5dd9541483d385'
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
                temporary: { MY_I32: -42 },
                persistent: { MY_I32: -42 },
            },
        })
    })

    it('call #4: Setter.set_u64([42u64])', async () => {
        const entry = await extractEntry(
            'abc11abf026f3cdfa76e1386f8ba38e84ec73f05dca9102d7aa620ff19f61478'
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
                temporary: { MY_U64: 42n },
                persistent: { MY_U64: 42n },
            },
        })
    })

    it('call #5: Setter.set_i64([-42i64])', async () => {
        const entry = await extractEntry(
            '1cf04a4145677376837ff4d38587911bc571b6c98e35ca54b312344f68ae3025'
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
                temporary: { MY_I64: -42n },
                persistent: { MY_I64: -42n },
            },
        })
    })

    it('call #6: Setter.set_u128([42u128])', async () => {
        const entry = await extractEntry(
            '63c135dcae01d93e556caaec4977c0d07d185f80cf4a9eed34d9334dafac623e'
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
                temporary: { MY_U128: 42n },
                persistent: { MY_U128: 42n },
            },
        })
    })

    it('call #7: Setter.set_i128([-42i128])', async () => {
        const entry = await extractEntry(
            '10a33ed40724c71f0ae78453fe50f6cbaa2e6a6ccb0b1968cdd99cd1fd186968'
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
                temporary: { MY_I128: -42n },
                persistent: { MY_I128: -42n },
            },
        })
    })

    it('call #8: Setter.set_sym("hello")', async () => {
        const entry = await extractEntry(
            '651c29141ca83c57a4c6ebd3bc757f200a2f299ecab9a2cfc4e68facd28dde2c'
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
                temporary: { MY_SYM: 'hello' },
                persistent: { MY_SYM: 'hello' },
            },
        })
    })

    it('call #9: Setter.set_bytes(0xbeef)', async () => {
        const entry = await extractEntry(
            '3382c5568cc71f97adeed8511c6b69b39fcae68026e82a8219874d46e0c6c33c'
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
                temporary: { MY_BYTES: beef },
                persistent: { MY_BYTES: beef },
            },
        })
    })

    it('call #10: Setter.set_bytes32(...)', async () => {
        const entry = await extractEntry(
            'edb69201f2b3cc15db7bf4cac5a96098bb0cc4448c3ff23965591aa9dce42c30'
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
                temporary: { MY_BTES32: bytes32 },
                persistent: { MY_BTES32: bytes32 },
            },
        })
    })

    it('call #11: Setter.set_vec([[1i32, -2i32, 3i32]])', async () => {
        const entry = await extractEntry(
            '0b3d09453c837e0b8957760a0e62a101ebc316423634fd3d5e736f4eb94d3b8e'
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
                temporary: { MY_VEC: [1, -2, 3] },
                persistent: { MY_VEC: [1, -2, 3] },
            },
        })
    })

    it('call #12: Setter.set_map([{2u32: 3i32, 4u32: 5i32}])', async () => {
        const entry = await extractEntry(
            'f46f345896bf7ddc0b60d17b2f79e08d92dc1965befe20dd5b196b0a0daf8658'
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
                temporary: { MY_MAP: { '2': 3, '4': 5 } },
                persistent: { MY_MAP: { '2': 3, '4': 5 } },
            },
        })
    })

    it('call #13: Setter.set_address([GDIY...R4W4]', async () => {
        const entry = await extractEntry(
            '24b513b57777b3533c0dcb15929eb35f22005d850058782325e6cd4db0349dc9'
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
                temporary: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                },
                persistent: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                },
            },
        })
    })

    it('call #14: Setter.set_struct([{"a"sym: 1u32, "b"sym: -100i128}])', async () => {
        const entry = await extractEntry(
            '1cc5a558453b12096b4cfdd238bd764602457b07fab5085156b0626a56220e99'
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
                temporary: { MY_STRUCT: { a: 1, b: -100n } },
                persistent: { MY_STRUCT: { a: 1, b: -100n } },
            },
        })
    })

    it('call #15: Setter.set_enum([["B"sym, -200i128]])', async () => {
        const entry = await extractEntry(
            'd44814c5d57d547fe80ca6ce476cd39359d7cbf0941d299466be5dc7d9993def'
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
                temporary: { MY_ENUM: ['B', -200n] },
                persistent: { MY_ENUM: ['B', -200n] },
            },
        })
    })
})
