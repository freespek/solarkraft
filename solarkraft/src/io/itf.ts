/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
import { byte, getFullType, Value } from '../state/value.js'
import { State } from '../state/state.js'

const META_FIELD: string = '#meta'
const VAR_TYPES_FIELD: string = 'varTypes'
const VARS_FIELD: string = 'vars'
const DESCRIPTION_FIELD: string = 'description'
const FORMAT_FIELD: string = 'format'
const FORMAT_DESCRIPTION_FIELD: string = 'format-description'
const BIG_INT_FIELD: string = '#bigint'
const MAP_FIELD: string = '#map'
const UNSERIALIZABLE_FIELD: string = '#unserializable'
const STATES_FIELD: string = 'states'

const UNSERIALIZABLE = { [UNSERIALIZABLE_FIELD]: true }

// Wraps bigint or byte literals in the ITF #bigint wrapper
function numWrap(b: bigint | byte) {
    return { [BIG_INT_FIELD]: b.toString() }
}

// Transforms the internal representation into the Apalache ITF format for serialization
export function valToITF(v: Value) {
    switch (v.type) {
        case 'bool':
            return v.val
        case 'u32':
        case 'i32':
        case 'u64':
        case 'i64':
        case 'u128':
        case 'i128':
            return numWrap(v.val)
        case 'symb':
        case 'addr':
            return v.val
        case 'arr':
            // array of 0/1 s, must be wrapped
            return v.val.map(numWrap)
        case 'vec':
            return v.val.map(valToITF)
        case 'map':
            return {
                [MAP_FIELD]: Array.from(v.val.entries()).map(
                    ([mapkey, mapval]) => [valToITF(mapkey), valToITF(mapval)]
                ),
            }
        default:
            return UNSERIALIZABLE
    }
}

export function stateToITF(s: State): object {
    const formatter = new Intl.DateTimeFormat('en-GB', {
        dateStyle: 'full',
        timeStyle: 'long',
    })

    const desc = `Created by Solarkraft on ${formatter.format(new Date().getTime())}`

    const formatDesc =
        'https://apalache.informal.systems/docs/adr/015adr-trace.html'

    const meta: object = {
        [FORMAT_FIELD]: 'ITF',
        [DESCRIPTION_FIELD]: desc,
        [FORMAT_DESCRIPTION_FIELD]: formatDesc,
    }

    const varTypes = {}
    const varNames = []
    const stateObj = {}

    for (const [varName, varValue] of s) {
        varTypes[varName] = getFullType(varValue)
        varNames.push(varName)
        stateObj[varName] = valToITF(varValue)
    }
    meta[VAR_TYPES_FIELD] = varTypes

    const ret = {
        [META_FIELD]: meta,
        [VARS_FIELD]: varNames,
        [STATES_FIELD]: [stateObj],
    }

    return ret
}
