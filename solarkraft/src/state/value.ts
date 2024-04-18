/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
import { OrderedMap } from 'immutable'

export type Value = {
    type: string
} & (
    | IntValue
    | BoolValue
    | SymbValue
    | AddrValue
    | ArrValue
    | VecValue
    | MapValue
)

export function isValid(v: Value): boolean {
    switch (v.type) {
        // Integers are valid iff their values lie within the [0, 2^n) or [-2^{n-1},2^{n-1}) intervals
        case 'u32': {
            const val = v.val
            return 0n <= val && val < 2n ** 32n
        }
        case 'i32': {
            const val = v.val
            return -(2n ** 31n) <= val && val < 2n ** 31n
        }
        case 'u64': {
            const val = v.val
            return 0n <= val && val < 2n ** 64n
        }
        case 'i64': {
            const val = v.val
            return -(2n ** 63n) <= val && val < 2n ** 63n
        }
        case 'u128': {
            const val = v.val
            return 0n <= val && val < 2n ** 128n
        }
        case 'i128': {
            const val = v.val
            return -(2n ** 127n) <= val && val < 2n ** 127n
        }
        // Symbols are valid iff they have at most 32 alphanumeric or underscore characters
        case 'symb': {
            const regex: RegExp = /^[a-zA-Z0-9_]{0,32}$/
            return regex.test(v.val)
        }
        // Addresses are valid iff they have _exactly_ 56 uppercase alphanumeric characters
        case 'addr': {
            const regex: RegExp = /^[A-Z0-9]{56}$/
            return regex.test(v.val)
        }
        // Fixed-length byte arrays are valid only if their declared length matches their actual length
        case 'arr': {
            return typeof v.len === 'undefined' || v.val.length === v.len
        }
        // Vectors are valid iff their elements are all valid.
        case 'vec': {
            return !v.val.some((elem) => !isValid(elem))
        }
        // Maps are valid iff their keys and values are all valid.
        case 'map': {
            return ![...v.val.entries()].some(
                ([key, value]) => !isValid(key) || !isValid(value)
            )
        }
        // Booleans are always valid, under TS type constraints.
        default:
            return true
    }
}

/**
 * Any of the follwing:
 *  - Unsigned 32-bit Integer (u32)
 *  - Signed 32-bit Integer (i32)
 *  - Unsigned 64-bit Integer (u64)
 *  - Signed 64-bit Integer (i64)
 *  - Unsigned 128-bit Integer (u128)
 *  - Signed 128-bit Integer (i128)
 *
 * Example: 2u32 would be represented as { val: 2, type: "u32" }, whereas 2i32 would be { val: 2, type: "i32" }
 */

export type ValidIntT = 'u32' | 'i32' | 'u64' | 'i64' | 'u128' | 'i128'

export type IntValue = {
    val: bigint
    type: ValidIntT
}

// Internal function for creating values of integer types.
// Calls isValid() to check whether `val` belongs to the range determined by `type`
function mkInt(type: ValidIntT, val: bigint): IntValue {
    const obj: IntValue = { type: type, val: val }
    if (!isValid(obj)) {
        throw new RangeError(`${val} lies outside the ${type} range.`)
    }
    return obj
}

// Safe constructor for u32-typed `Value`s. Throws a `RangeError` if `v` lies outside [0, 2^32)
export function u32(v: bigint): IntValue {
    return mkInt('u32', v)
}

// Safe constructor for i32-typed `Value`s. Throws a `RangeError` if `v` lies outside [-2^31, 2^31)
export function i32(v: bigint): IntValue {
    return mkInt('i32', v)
}

// Safe constructor for u64-typed `Value`s. Throws a `RangeError` if `v` lies outside [0, 2^64)
export function u64(v: bigint): IntValue {
    return mkInt('u64', v)
}

// Safe constructor for i64-typed `Value`s. Throws a `RangeError` if `v` lies outside [-2^63, 2^63)
export function i64(v: bigint): IntValue {
    return mkInt('i64', v)
}

// Safe constructor for u128-typed `Value`s. Throws a `RangeError` if `v` lies outside [0, 2^128)
export function u128(v: bigint): IntValue {
    return mkInt('u128', v)
}

// Safe constructor for i128-typed `Value`s. Throws a `RangeError` if `v` lies outside [-2^127, 2^127)
export function i128(v: bigint): IntValue {
    return mkInt('i128', v)
}

// true or false
export type BoolValue = {
    val: boolean
    type: 'bool'
}

// Wrapper around a `boolean`. Can never throw an exception, and is always valid.
export function bool(v: boolean): BoolValue {
    return { type: 'bool', val: v }
}

// Symbols are small efficient strings up to 32 characters in length and limited to `a-z`, `A-Z`, `0-9`, and `_`,
// that are encoded into 64-bit integers. We store the string representation, and optionally the number.
// TODO: determine _how_ the strings are encoded as numbers?
export type SymbValue = {
    val: string
    type: 'symb'
    num?: number
}

// Safe constructor for symb-typed `Value`s. Throws a `TypeError` if `s` is too long, or contains illegal characters.
export function symb(s: string): SymbValue {
    const obj: SymbValue = { type: 'symb', val: s }
    if (!isValid(obj)) {
        throw new TypeError(
            `Symbols must be up to 32 alphanumeric characters or underscores, found: ${s}.`
        )
    }
    return obj
}

// Addresses are always length-56, and limited to `A-Z`, `0-9`.
export type AddrValue = {
    val: string
    type: 'addr'
}

// Safe constructor for addr-typed `Value`s. Throws a `TypeError` if `s` is not 56 characters long or contains illegal characters.
export function addr(s: string): AddrValue {
    const obj: AddrValue = { type: 'addr', val: s }
    if (!isValid(obj)) {
        throw new TypeError(
            `Symbols must be up to 32 alphanumeric characters or underscores, found: ${s}.`
        )
    }
    return obj
}

export type byte = 0 | 1

// Byte arrays (Bytes, BytesN)
// The `len` field is present iff the length is fixed (i.e. for BytesN)
export type ArrValue = {
    val: byte[]
    type: 'arr'
    len?: number
}

// Safe constructor for arr-typed `Value`s representing non-fixed width byte arrays. Cannot throw.
export function bytes(v: byte[]): Value {
    return { type: 'arr', val: v }
}

// Safe constructor for arr-typed `Value`s representing fixed width byte arrays. Cannot throw.
export function bytesN(v: byte[]): ArrValue {
    OrderedMap()
    return { type: 'arr', val: v, len: v.length }
}

// Vectors are an ordered collection of `Value`s, with possible duplicates.
// The values in a Vec are not guaranteed to be of any specific type. <-- from the docs
export type VecValue = {
    val: Value[]
    type: 'vec'
}

// Safe constructor for vec-typed `Value`s. Throws a `TypeError` if `v` contains an invalid value.
export function vec(v: Value[]): VecValue {
    const obj: VecValue = { type: 'vec', val: v }
    if (!isValid(obj)) {
        throw new TypeError(`Some element of ${v} is not valid.`)
    }
    return obj
}

// Soroban Map is an ordered key-value dictionary (note that JS maps are in principle unordered, but will iterate in insertion order).
// Maps have at most one entry per key. Setting a value for a key in the map that already has a value for that key replaces the value. <-- docs
export type MapValue = {
    val: OrderedMap<Value, Value>
    type: 'map'
}

export type KeyValuePair = [Value, Value]

// Safe constructor for map-typed `Value`s. Throws a `TypeError` if `v` contains an invalid key or value.
export function map(v: OrderedMap<Value, Value>): MapValue {
    const obj: MapValue = { type: 'map', val: v }
    if (!isValid(obj)) {
        throw new TypeError(`Some key or value of ${v} is not valid.`)
    }
    return obj
}

// Safe constructor for vec-typed `Value`s. Throws a `TypeError` if `v` contains an invalid key or value, or if it contains duplicate keys.
export function mapFromKV(a: KeyValuePair[]): MapValue {
    let partialMap = OrderedMap<Value, Value>()

    for (const [k, v] of a) {
        if (partialMap.has(k)) {
            throw new TypeError(
                `Pairs must have unique keys, found duplicate ${k}`
            )
        }
        partialMap = partialMap.set(k, v)
    }
    return map(partialMap)
}

// Helper function, returns the contents of the map as an array of key-value pairs for serialization
export function toArr(m: MapValue): KeyValuePair[] {
    return Array.from(m.val.entries())
}
