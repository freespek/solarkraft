export type Value = {
    type: string
} & (IntValue | BoolValue | SymbValue | AddrValue)

export function isValid(v: Value): boolean {
    switch (v.type) {
        case "u32": {
            const val = (v as IntValue).val
            return (0n <= val) && (val <= 2n ** 32n)
        }
        case "i32": {
            const val = (v as IntValue).val
            return (-(2n ** 31n) <= val) && (val < (2n ** 31n))
        }
        case "u64": {
            const val = (v as IntValue).val
            return (0n <= val) && (val <= 2n ** 64n)
        }
        case "i64": {
            const val = (v as IntValue).val
            return (-(2n ** 63n) <= val) && (val < (2n ** 63n))
        }
        case "u128": {
            const val = (v as IntValue).val
            return (0n <= val) && (val <= 2n ** 128n)
        }
        case "i128": {
            const val = (v as IntValue).val
            return (-(2n ** 127n) <= val) && (val < (2n ** 127n))
        }
        case "symb": {
            const regex: RegExp = /^[a-zA-Z0-9_]{0,32}$/
            return regex.test((v as SymbValue).val)
        }
        case "addr": {
            const regex: RegExp = /^[A-Z0-9]{56}$/
            return regex.test((v as AddrValue).val)
        }
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

export type ValidIntT = "u32" | "i32" | "u64" | "i64" | "u128" | "i128"

export type IntValue = {
    val: bigint
    type: ValidIntT
}


function mkInt(type: ValidIntT, val: bigint) {
    const obj = { type: type, val: val } as Value
    if (!isValid(obj)) {
        throw new RangeError(`${val} lies outside the ${type} range.`)
    }
    return obj
}

export function u32(v: bigint): Value {
    return mkInt("u32", v)
}

export function i32(v: bigint): Value {
    return mkInt("i32", v)
}

export function u64(v: bigint): Value {
    return mkInt("u64", v)
}

export function i64(v: bigint): Value {
    return mkInt("i64", v)
}

export function u128(v: bigint): Value {
    return mkInt("u128", v)
}

export function i128(v: bigint): Value {
    return mkInt("i128", v)
}

// true or false
export type BoolValue = {
    val: boolean
    type: "bool"
}

export function bool(v: boolean): Value {
    return { type: "bool", val: v }
}

// Symbols are small efficient strings up to 32 characters in length and limited to a-z A-Z 0-9 _ that are encoded into 64-bit integers.
// We store the string representation, and optionally the number.
// TODO: determine _how_ the strings are encoded as numbers
export type SymbValue = {
    val: string
    type: "symb"
    num?: number
}

export function symb(s: string): Value {
    const obj = { type: "symb", val: s } as Value
    if (!isValid(obj)) {
        throw new TypeError(`Symbols must be up to 32 alphanumeric characters or underscores, found: ${s}.`)
    }
    return obj
}

// Addresses are always length-56
export type AddrValue = {
    val: string
    type: "addr"
}

export function addr(s: string): Value {
    const obj = { type: "addr", val: s } as Value
    if (!isValid(obj)) {
        throw new TypeError(`Symbols must be up to 32 alphanumeric characters or underscores, found: ${s}.`)
    }
    return obj
}

// Byte arrays (Bytes, BytesN)
// The `len` field is present iff the length is fixed (i.e. for BytesN)
// TODO: tests
export type ArrValue = {
    val: { type: "u32", val: bigint }[]
    type: "arr"
    len?: number
    // if (typeof (l) !== 'undefined' && v.length !== l) {
    //     throw new TypeError(`Array declared as fixed-length ${l}, but actual length is ${v.length}.`)
    // }
}





