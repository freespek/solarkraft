// an example unit test to copy from

import { assert } from 'chai'
import { OrderedMap } from 'immutable'
import { describe, it } from 'mocha'
import { Value, i32, u128, addr, map } from '../../src/state/value.js'
import { stateToITF } from '../../src/io/itf.js'
import { State } from '../../src/state/state.js'

describe('itf tests', () => {
    const aliceAddr = 'ALICE000000000000000000000000000000000000000000000000000'
    const bobAddr = 'BOB00000000000000000000000000000000000000000000000000000'

    const state: State = OrderedMap<string, Value>()
        .set(
            'balances',
            map(
                OrderedMap<Value, Value>()
                    .set(addr(aliceAddr), u128(10n ** 20n))
                    .set(addr(bobAddr), u128(10n ** 10n))
            )
        )
        .set('COUNTER', i32(-50n))

    const itf = stateToITF(state)

    it('outputs metadata and type information correctly', () => {
        assert(itf['vars'].length === 2)
        assert(itf['vars'][0] === 'balances')
        assert(itf['vars'][1] === 'COUNTER')

        assert(itf['#meta']['format'] === 'ITF')
        assert(itf['#meta']['varTypes']['balances'] === '(addr -> u128)')
        assert(itf['#meta']['varTypes']['COUNTER'] === 'i32')

        assert(itf['states'].length === 1)
    })

    it('serializes the contract state correctly', () => {
        const s = itf['states'][0]

        const expectedBalances = [
            [aliceAddr, { '#bigint': '1' + '0'.repeat(20) }],
            [bobAddr, { '#bigint': '1' + '0'.repeat(10) }],
        ]

        const expectedCounter = { '#bigint': '-50' }

        const bmap = s['balances']['#map']

        assert(bmap.length == 2)
        assert(bmap[0].length == 2)
        assert(bmap[1].length == 2)

        assert(bmap[0][0] === expectedBalances[0][0])
        assert(bmap[0][1]['#bigint'] === expectedBalances[0][1]['#bigint'])
        assert(bmap[1][0] === expectedBalances[1][0])
        assert(bmap[1][1]['#bigint'] === expectedBalances[1][1]['#bigint'])

        assert[s['COUNTER']['#bigint'] === expectedCounter['#bigint']]
    })
})
