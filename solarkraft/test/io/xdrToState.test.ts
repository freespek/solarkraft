// an example unit test to copy from

import { assert } from 'chai'
import { describe, it } from 'mocha'

import { fetchContractState } from '../../src/io/xdrToState.js'

describe('xdr', () => {
    it('tests an async call to the testnet URL, reading the contract from the online tutorial', async () => {
        // Data from https://developers.stellar.org/network/soroban-rpc/api-reference/methods/getLedgerEntries
        const contractId =
            'CCPYZFKEAXHHS5VVW5J45TOU7S2EODJ7TZNJIA5LKDVL3PESCES6FNCI'
        const where = 'https://soroban-testnet.stellar.org'

        const fields = ['COUNTER']

        const state = await fetchContractState(contractId, fields, where)

        const keys = Array.from(state.keySeq())
        assert(keys.length === fields.length)
        for (const i of fields.keys()) {
            assert(fields[i] === keys[i])
        }

        const ctrVal = state.get('COUNTER')
        assert(ctrVal.type === 'u32')
        assert(ctrVal.val === 2n)
    })
})
