// Integration tests for the `verify` command

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'
import { mkdtempSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import {
    ContractStorage,
    saveContractCallEntry,
} from '../../src/fetcher/storage.js'
import { OrderedMap } from 'immutable'

const TX_HASH =
    '9fb12935fbadcd28aa220d076f11be631590d22c60977a53997a746898322ca3'
const CONTRACT_ID = 'CC22QGTOUMERDNIYN7TPNX3V6EMPHQXVSRR3XY56EADF7YTFISD2ROND'

describe('list', () => {
    it('lists a single entry', function (done) {
        // create a single entry in a temporary directory
        const root = join(tmpdir(), 'solarkraft-storage-')
        mkdtempSync(root)
        saveContractCallEntry(root, {
            timestamp: 1716393856,
            height: 1000,
            txHash: TX_HASH,
            transaction_successful: true,
            contractId: CONTRACT_ID,
            method: 'set_i32',
            methodArgs: [42],
            returnValue: 0,
            fields: OrderedMap<string, any>(),
            oldFields: OrderedMap<string, any>(),
            oldStorage: OrderedMap<string, ContractStorage>(),
            storage: OrderedMap<string, ContractStorage>(),
        })

        this.timeout(50000)
        spawn(`solarkraft list --home ${root}`)
            .wait(`Contract ${CONTRACT_ID}`)
            .wait('  [unverified]')
            .wait('    height: 1000')
            .wait(`    tx: ${TX_HASH}`)
            .run(done)
    })
})
