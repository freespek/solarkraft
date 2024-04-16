interface Value { }

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
abstract class IntValue implements Value {
    val: bigint
    type: string

    constructor(v: bigint) {
        this.val = v
        if (!this.isValid()) {
            throw new RangeError(`${v} lies outside the ${this.type} range.`)
        }
    }

    abstract isValid(): boolean
}

// u32
export class IntValue_u32 extends IntValue {
    val: bigint
    type = "u32"

    isValid(): boolean {
        return (0n <= this.val) && (this.val <= 2n ** 32n)
    }
}

// i32
export class IntValue_i32 extends IntValue {
    val: bigint
    type = "i32"

    isValid(): boolean {
        return (-(2n ** 31n) <= this.val) && (this.val < (2n ** 31n))
    }
}

// u64
export class IntValue_u64 extends IntValue {
    val: bigint
    type = "u64"

    isValid(): boolean {
        return (0n <= this.val) && (this.val <= 2n ** 64n)
    }
}

// i64
export class IntValue_i64 extends IntValue {
    val: bigint
    type = "i64"

    isValid(): boolean {
        return (-(2n ** 63n) <= this.val) && (this.val < (2n ** 63n))
    }
}

// u128
export class IntValue_u128 extends IntValue {
    val: bigint
    type = "u128"

    isValid(): boolean {
        return (0n <= this.val) && (this.val <= 2n ** 128n)
    }
}

// i128
export class IntValue_i128 extends IntValue {
    val: bigint
    type = "i128"

    isValid(): boolean {
        return (-(2n ** 127n) <= this.val) && (this.val < (2n ** 127n))
    }
}

// true or false
export class BoolValue implements Value {
    val: boolean

    constructor(v: boolean) {
        this.val = v
    }
}

// Symbols are small efficient strings up to 32 characters in length and limited to a-z A-Z 0-9 _ that are encoded into 64-bit integers.
// We store the string representation, and optionally the number.
// TODO: determine _how_ the strings are encoded as numbers
export class SymValue implements Value {
    val: string
    num?: number

    private regex: RegExp = /^[a-zA-Z0-9_]{0,32}$/

    constructor(v: string) {
        this.val = v
        if (!this.regex.test(v)) {
            throw new TypeError(`Symbols must be up to 32 alphanumeric characters or underscores, found: ${v}.`)
        }
    }
}

// Addresses are always length-56
export class AddrValue implements Value {
    val: string

    private regex: RegExp = /^[A-Z0-9]{56}$/

    constructor(v: string) {
        this.val = v
        if (!this.regex.test(v)) {
            throw new TypeError(`Address must be exactly 56 uppercase alphanumeric characters, found: ${v}.`)
        }
    }
}

// Byte arrays (Bytes, BytesN)
// The `len` field is present iff the length is fixed (i.e. for BytesN)
// TODO: tests
export class ArrValue implements Value {
    val: IntValue_u32[]
    len?: number

    constructor(v: IntValue_u32[], l?: number) {
        this.val = v
        if (typeof (l) !== 'undefined' && v.length !== l) {
            throw new TypeError(`Array declared as fixed-length ${l}, but actual length is ${v.length}.`)
        }
    }
}





