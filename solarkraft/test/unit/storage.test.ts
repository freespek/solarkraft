/**
 * Storage tests.
 *
 * Igor Konnov, 2024
 */

import { assert } from 'chai'
import { mkdtempSync } from 'fs'
import { describe, it } from 'mocha'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import {
    loadContractCallEntry,
    saveContractCallEntry,
    storagePath,
} from '../../src/fetcher/storage.js'
import { OrderedMap } from 'immutable'

const TX_HASH =
    '9fb12935fbadcd28aa220d076f11be631590d22c60977a53997a746898322ca3'
const CONTRACT_ID = 'CCQURSVQRCMNZPLNYA4AMP2JUODZ5QOLG5XCLQWEJAEE3NBLR5ZWZ5KX'

describe('storage tests', () => {
    function storeEntry() {
        const root = join(tmpdir(), 'solarkraft-storage-')
        mkdtempSync(root)
        const filename = saveContractCallEntry(root, {
            timestamp: 1716393856,
            height: 1000,
            txHash: TX_HASH,
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
        })

        return [root, filename]
    }

    it('store entry', async () => {
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

    it('load entry', async () => {
        const filename = storeEntry()[1]
        const entry = loadContractCallEntry(filename)
        assert.equal(entry.timestamp, 1716393856)
        assert.equal(entry.height, 1000)
        assert.equal(entry.txHash, TX_HASH)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.equal(entry.method, 'set_i32')
        assert.deepEqual(entry.methodArgs, [42])
        assert.equal(entry.returnValue, 0)
        assert.deepEqual(entry.fields.toArray(), [
            ['a', 3],
            ['b', 993143214321423154315154321n],
        ])
        assert.deepEqual(entry.oldFields.toArray(), [
            ['a', 1],
            ['b', 993143214321423154315154322n],
        ])
    })
})
