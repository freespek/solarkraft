/**
 * Storage tests.
 *
 * Igor Konnov, 2024
 */

import { assert, expect } from 'chai'
import { mkdtempSync } from 'fs'
import { describe, it } from 'mocha'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import {
    ContractStorage,
    emptyFieldsMap,
    loadContractCallEntry,
    saveContractCallEntry,
    storagePath,
    FullState,
    saveContractFullState,
    loadContractFullState,
} from '../../src/fetcher/storage.js'
import { OrderedMap } from 'immutable'

const TX_HASH =
    '9fb12935fbadcd28aa220d076f11be631590d22c60977a53997a746898322ca3'
const CONTRACT_ID = 'CCQURSVQRCMNZPLNYA4AMP2JUODZ5QOLG5XCLQWEJAEE3NBLR5ZWZ5KX'

describe('Solarkraft storage', () => {
    function storeEntry(): [string, string] {
        const root = mkdtempSync(join(tmpdir(), 'solarkraft-storage-'))
        const filename = saveContractCallEntry(root, {
            timestamp: 1716393856,
            height: 1000,
            txHash: TX_HASH,
            txSuccess: true,
            contractId: CONTRACT_ID,
            method: 'set_i32',
            methodArgs: [42],
            returnValue: 0,
            fields: OrderedMap<string, any>([
                ['a', 3],
                ['b', 993143214321423154315154321n],
            ]),
            oldFields: OrderedMap<string, any>([
                ['a', 1],
                ['b', 993143214321423154315154322n],
            ]),
            oldStorage: OrderedMap<string, ContractStorage>([
                [
                    CONTRACT_ID,
                    {
                        instance: OrderedMap<string, any>([
                            ['a', 1],
                            ['b', 993143214321423154315154322n],
                        ]),
                        persistent: emptyFieldsMap(),
                        temporary: emptyFieldsMap(),
                    },
                ],
            ]),
            storage: OrderedMap<string, ContractStorage>([
                [
                    CONTRACT_ID,
                    {
                        instance: OrderedMap<string, any>([
                            ['a', 3],
                            ['b', 993143214321423154315154321n],
                        ]),
                        persistent: emptyFieldsMap(),
                        temporary: emptyFieldsMap(),
                    },
                ],
            ]),
        })

        return [root, filename]
    }

    it('store entry', () => {
        const [root, filename] = storeEntry()

        assert.equal(
            filename,
            join(
                storagePath(root),
                CONTRACT_ID,
                '1000',
                `entry-${TX_HASH}.json`
            )
        )
    })

    it('load entry', () => {
        const [root] = storeEntry()
        const entry = loadContractCallEntry(root, TX_HASH).unwrap()
        assert.equal(entry.timestamp, 1716393856)
        assert.equal(entry.height, 1000)
        assert.equal(entry.txHash, TX_HASH)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.equal(entry.method, 'set_i32')
        assert.deepEqual(entry.methodArgs, [42n])
        assert.equal(entry.returnValue, 0)
        assert.deepEqual(entry.fields.toArray(), [
            ['a', 3n],
            ['b', 993143214321423154315154321n],
        ])
        assert.deepEqual(entry.oldFields.toArray(), [
            ['a', 1n],
            ['b', 993143214321423154315154322n],
        ])
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: { a: 3n, b: 993143214321423154315154321n },
                persistent: {},
                temporary: {},
            },
        })
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: { a: 1n, b: 993143214321423154315154322n },
                persistent: {},
                temporary: {},
            },
        })
    })

    function storeFullStateFixture() {
        const root = mkdtempSync(join(tmpdir(), 'solarkraft-storage-'))
        const contractId =
            'CCQURSVQRCMNZPLNYA4AMP2JUODZ5QOLG5XCLQWEJAEE3NBLR5ZWZ5KX'
        const fullStorage = OrderedMap<string, ContractStorage>([
            [
                contractId,
                {
                    instance: OrderedMap<string, any>([
                        ['i32', 42],
                        ['i64', 123],
                        ['i128', 1001],
                    ]),
                    persistent: OrderedMap<string, any>([
                        ['i32', 142],
                        ['i64', 124],
                        ['i128', 1002],
                    ]),
                    temporary: OrderedMap<string, any>([
                        ['i32', 242],
                        ['i64', 125],
                        ['i128', 1003],
                    ]),
                },
            ],
        ])
        const state: FullState = {
            timestamp: 1,
            height: 2,
            latestTxHash: '9fb0',
            contractId: contractId,
            storage: fullStorage,
        }
        const filename = saveContractFullState(root, state)
        return [root, filename]
    }

    it('store full state', () => {
        const [root, filename] = storeFullStateFixture()
        assert(root !== undefined, 'expected root')
        assert(filename !== undefined, 'expected filename')
    })

    it('load full state', () => {
        const [root, filename] = storeFullStateFixture()
        assert(filename !== undefined, 'expected filename')
        const state = loadContractFullState(root, CONTRACT_ID).unwrap()
        expect(state.contractId).to.equal(CONTRACT_ID)
        expect(state.timestamp).to.equal(1n)
        expect(state.height).to.equal(2n)
        expect(state.latestTxHash).to.equal('9fb0')
        expect(state.storage.toJS()).to.deep.equal({
            [CONTRACT_ID]: {
                instance: {
                    i32: 42n,
                    i64: 123n,
                    i128: 1001n,
                },
                persistent: {
                    i32: 142n,
                    i64: 124n,
                    i128: 1002n,
                },
                temporary: {
                    i32: 242n,
                    i64: 125n,
                    i128: 1003n,
                },
            },
        })
    })
})
