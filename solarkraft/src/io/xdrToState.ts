/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
import { State } from '../state/state.js'
import * as V from '../state/value.js'

import { xdr, Address } from '@stellar/stellar-sdk'
import { OrderedMap } from 'immutable'

// Request bodies have a standardized shape, we parameterize the method (e.g. "getLedgerEntries"),
// and the keys (e.g. the fields of the contracts to be read by "getLedgerEntries")
// Technically we can assign unique IDs to our requests/responses, but this field should not matter for now.
export function makeRequestBody(
    method: string,
    contractLedgerKeys: string[],
    id: number = 0
): object {
    return {
        jsonrpc: '2.0',
        id: id,
        method: method,
        params: {
            keys: contractLedgerKeys,
        },
    }
}

export type Response = {
    jsonrpc: string
    id: number
    result: {
        entries: {
            key: string
            xdr: string
            lastModifiedLedgerSeq: number
        }[]
        latestLedger: number
    }
}

// Async RPC calls give us a Promise<unknown>.
// We need to make sure it's safe to cast to a Response, so we can access fields programmatically
function isResponse(data: unknown): boolean {
    if (typeof data === 'object' && data !== null) {
        const maybe = data as Response
        if (typeof maybe['jsonrpc'] !== 'string') return false
        if (typeof maybe['id'] !== 'number') return false
        const res = maybe['result']
        if (typeof res !== 'object') return false
        if (typeof res['latestLedger'] !== 'number') return false
        const entries = res['entries']
        if (!Array.isArray(entries)) return false

        return !entries.some((e) => {
            if (typeof e['key'] !== 'string') return true
            if (typeof e['xdr'] !== 'string') return true
            if (typeof e['lastModifiedLedgerSeq'] !== 'number') return true
            return false
        })
    } else return false
}

// ------------ SOROBAN RPC METHODS ------------
// ---- Copied from https://developers.stellar.org/network/soroban-rpc/api-reference/methods/getLedgerEntries ----

// Given a contract ID and a field belonging to that contract (`symbolText`),
// creates a lookup key to be used to query the current value of
// the field variable
function getLedgerKeySymbol(contractId: string, symbolText: string) {
    const ledgerKey = xdr.LedgerKey.contractData(
        new xdr.LedgerKeyContractData({
            contract: new Address(contractId).toScAddress(),
            key: xdr.ScVal.scvSymbol(symbolText),
            durability: xdr.ContractDataDurability.persistent(),
        })
    )
    return ledgerKey.toXDR('base64')
}

// Given either the testnet URL, or a path to a local node, as `where`, we can send a
// request with the given body and receive what should be a Response
// If the response does not have the correct shape, throws a TypeError.
async function queryRPC(where: string, requestBody: object): Promise<Response> {
    const res = await fetch(where, {
        method: 'POST',
        headers: {
            'Content-Type': 'application/json',
        },
        body: JSON.stringify(requestBody),
    })
    const json = await res.json()

    if (!isResponse(json))
        throw new TypeError(
            'Response received does not match the Response type'
        )

    return json as Response
}

// ------------------------

// Conversion method from ScVal to Value
// After the RPC response is returned, it contains XDR-encoded values of type ScVal. In order to use
// our internal representation, we need to convert each ScVal to a corresponding Value
// TODO: in the future, we could consider getting rid of `Value` and using `ScVal` directly, as
//       well as implementing a direct `ScVal` -> ITF translation. Note, however, that `ScValType` types are
//       not in direct correspondence with Sorban types, and that handling `ScVal`s is more complicated than `Value`s
export function scValAsValue(v: xdr.ScVal): V.Value {
    const vType = v.switch()
    switch (vType) {
        case xdr.ScValType.scvBool():
            return V.bool(v.value() as boolean)
        case xdr.ScValType.scvAddress():
            return V.addr(
                (v.value() as xdr.ScAddress).accountId().value().toString()
            )
        case xdr.ScValType.scvSymbol():
            return V.symb(v.value() as string)
        case xdr.ScValType.scvU32():
            return V.u32(BigInt(v.value() as number))
        case xdr.ScValType.scvI32():
            return V.i32(BigInt(v.value() as number))
        case xdr.ScValType.scvU64():
            return V.u64((v.value() as xdr.Uint64).toBigInt())
        case xdr.ScValType.scvI64():
            return V.i64((v.value() as xdr.Int64).toBigInt())
        case xdr.ScValType.scvU128(): {
            const cast = v.value() as xdr.UInt128Parts
            const hiInt = cast.hi().toBigInt() * 2n ** 64n
            const loInt = cast.lo().toBigInt()
            return V.u128(hiInt + loInt)
        }
        case xdr.ScValType.scvI128(): {
            // TODO: investigate how exactly the conversion to u128 from Int128Parts works.
            throw new Error('scvI128 conversion not yet implemented')
            // const cast = v.value() as xdr.Int128Parts
            // const hiBits = cast.hi().toBigInt()
            // const sign = hiBits >> 63n
            // const hiInt = hiBits & ~(1n << 63n)
            // const loInt = cast.lo().toBigInt()
            // V.u128(sign * (hiInt + loInt))
        }
        case xdr.ScValType.scvBytes():
            return V.bytes(Array.from((v.value() as Buffer).valueOf()))

        case xdr.ScValType.scvVec():
            return V.vec((v.value() as xdr.ScVal[]).map(scValAsValue), false)

        case xdr.ScValType.scvMap(): {
            const entries = v.value() as xdr.ScMapEntry[]
            const pairs: V.KeyValuePair[] = entries.map((x) => [
                scValAsValue(x.key()),
                scValAsValue(x.val()),
            ])
            return V.mapFromKV(pairs, false)
        }

        default: {
            console.log(`Got: ${v.switch().name}`)
            throw new TypeError(`${v} does not correspond to any Value`)
        }
    }
}

// Main entry point function
// Given a contract's ID `cid`, and the field names, the values of which we want to read, retrieves a `State`
// object, by submitting an RPC query to the location `where`, and interpreting the Response obtained.
// The keys of the `State` returned are the field names provided, and their corresponding values are the `Value`s interpreted from
// the response XDRs.
export async function fetchContractState(
    cid: string,
    fields: string[],
    where: string
): Promise<State> {
    // First, we must convert each key (string) to a `LedgerKey`.
    const keys = fields.map((fld) => getLedgerKeySymbol(cid, fld))

    // Second, we create the request, containing all of the ledger keys at once
    const request = makeRequestBody('getLedgerEntries', keys)

    // We receive a Response (queryRPC throws if the response shape is incorrect)
    const response: Response = await queryRPC(where, request)

    // We don't care about the response metadata, we just need to extract the xdrs.
    const xdrs = response.result.entries.map((e) => e.xdr)

    // sanity check, the number of fields in the resonse should match the number of fields in the query
    if (xdrs.length !== fields.length)
        throw new Error(
            'Number of fields in response does not match the number of fields in the input'
        )

    // Each XDR is a base64 encoded `LedgerEntryData` object, we read them back
    const data = xdrs.map((singleXDR) =>
        xdr.LedgerEntryData.fromXDR(singleXDR, 'base64')
    )

    // To create a state, we need to check under _.contractData.val to read the value.
    // Since it comes in ScVal, we need scValAsValue to convert it.
    const values = data.map((d) => scValAsValue(d.contractData().val()))

    // Finally, we zip the inputs (field names) with the values, and create the State map
    const pairs: Iterable<[string, V.Value]> = fields.map((f, idx) => [
        f,
        values[idx],
    ])

    return OrderedMap<string, V.Value>(pairs)
}
