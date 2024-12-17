/**
 * State aggregation tests.
 *
 * Igor Konnov, 2024
 */

import { describe, it } from 'mocha'
import { expect } from 'chai'
import { OrderedMap } from 'immutable'
import {
    ContractCallEntry,
    ContractStorage,
    emptyFieldsMap,
    emptyFullState,
    emptyMultiContractStorage,
    FullState,
} from '../../src/fetcher/storage.js'
import { aggregate } from '../../src/fetcher/aggregator.js'

// these are unit tests, as we are trying to minimize the number of e2e tests
describe('State aggregation', () => {
    it('updates empty state on successful transaction', () => {
        const empty = emptyFullState()
        const contractId =
            'CCQURSVQRCMNZPLNYA4AMP2JUODZ5QOLG5XCLQWEJAEE3NBLR5ZWZ5KX'
        const callEntry: ContractCallEntry = {
            timestamp: 123,
            height: 1234,
            txHash: '9fb1',
            txSuccess: true,
            contractId: contractId,
            method: 'set_i32',
            methodArgs: [42],
            returnValue: 0,
            // the fields are irrelevant, only the storage
            fields: emptyFieldsMap(),
            oldFields: emptyFieldsMap(),
            // oldStorage is irrelevant, only the storage
            oldStorage: emptyMultiContractStorage(),
            // the storage is very much relevant
            storage: OrderedMap<string, ContractStorage>([
                [
                    contractId,
                    {
                        // we set i32 to different values in different storages, because we can
                        instance: OrderedMap<string, any>([['i32', 42]]),
                        persistent: OrderedMap<string, any>([['i32', 142]]),
                        temporary: OrderedMap<string, any>([['i32', 242]]),
                    },
                ],
            ]),
        }

        const nextState = aggregate(empty, callEntry)
        expect(nextState.contractId).to.equal(contractId)
        expect(nextState.timestamp).to.equal(callEntry.timestamp)
        expect(nextState.height).to.equal(callEntry.height)
        expect(nextState.latestTxHash).to.equal(callEntry.txHash)
        expect(nextState.storage.get(contractId).instance.get('i32')).to.equal(
            42
        )
        expect(
            nextState.storage.get(contractId).persistent.get('i32')
        ).to.equal(142)
        expect(nextState.storage.get(contractId).temporary.get('i32')).to.equal(
            242
        )
    })

    /* eslint-disable @typescript-eslint/no-unused-expressions */
    it('updates previous state on successful transaction', () => {
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
        const prevState: FullState = {
            timestamp: 1,
            height: 2,
            latestTxHash: '9fb0',
            contractId: contractId,
            storage: fullStorage,
        }
        const callEntry: ContractCallEntry = {
            timestamp: 123,
            height: 1234,
            txHash: '9fb1',
            txSuccess: true,
            contractId: contractId,
            method: 'update',
            methodArgs: [42],
            returnValue: 0,
            // the fields are irrelevant, only the storage
            fields: emptyFieldsMap(),
            oldFields: emptyFieldsMap(),
            // oldStorage is relevant for finding removed keys
            oldStorage: OrderedMap<string, ContractStorage>([
                [
                    contractId,
                    {
                        instance: OrderedMap<string, any>([
                            ['i32', 42],
                            ['i64', 123],
                        ]),
                        persistent: OrderedMap<string, any>([
                            ['i32', 142],
                            ['i64', 124],
                        ]),
                        temporary: OrderedMap<string, any>([
                            ['i32', 242],
                            ['i64', 125],
                        ]),
                    },
                ],
            ]),
            // the storage is very much relevant
            storage: OrderedMap<string, ContractStorage>([
                [
                    contractId,
                    {
                        instance: OrderedMap<string, any>([['i32', 101]]),
                        persistent: OrderedMap<string, any>([['i32', 102]]),
                        temporary: OrderedMap<string, any>([['i32', 103]]),
                    },
                ],
            ]),
        }

        const nextState = aggregate(prevState, callEntry)
        expect(nextState.contractId).to.equal(contractId)
        expect(nextState.timestamp).to.equal(callEntry.timestamp)
        expect(nextState.height).to.equal(callEntry.height)
        expect(nextState.latestTxHash).to.equal(callEntry.txHash)
        expect(nextState.storage.get(contractId).instance.get('i32')).to.equal(
            101
        )
        expect(
            nextState.storage.get(contractId).persistent.get('i32')
        ).to.equal(102)
        expect(nextState.storage.get(contractId).temporary.get('i32')).to.equal(
            103
        )
        expect(nextState.storage.get(contractId).instance.get('i64')).to.be
            .undefined
        expect(nextState.storage.get(contractId).persistent.get('i64')).to.be
            .undefined
        expect(nextState.storage.get(contractId).temporary.get('i64')).to.be
            .undefined
        expect(nextState.storage.get(contractId).instance.get('i128')).to.equal(
            1001
        )
        expect(
            nextState.storage.get(contractId).persistent.get('i128')
        ).to.equal(1002)
        expect(
            nextState.storage.get(contractId).temporary.get('i128')
        ).to.equal(1003)
    })
})
