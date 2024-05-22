/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Instrument a Solarkraft monitor spec with a ledger state.
 *
 * The monitor spec is given as Apalache TLA+ JSON IR, which can be obtained from
 * `apalache-mc typecheck --output file.json`:
 * https://apalache.informal.systems/docs/adr/005adr-json.html
 *
 * The ledger state can be obtained using the Solarkraft fetcher, see `./fetch.ts`.
 *
 * The entry point to this module is `instrumentMonitor`; other exports are made
 * to facilitate finer-grained unit testing.
 *
 * @author Thomas Pani, 2024
 */

import { assert } from 'console'
import { ContractCallEntry } from './fetcher/storage.js'

/**
 * Return an instrumented monitor specification.
 * @param monitor A TLA+ monitor, as returned from `apalache typecheck --output=temp.json`
 * @param contractCall The contract call, fetched from the ledger.
 * @returns The instrumented TLA+ monitor.
 */
export function instrumentMonitor(
    monitor: any,
    contractCall: ContractCallEntry
): any {
    // Only instrument state variables that are delcared in the monitor spec
    // (otherwise we provoke type errors in Apalache Snowcat, via undeclared variables)
    const declaredMonitorVariables = monitor.modules[0].declarations
        .filter(({ kind }) => kind == 'TlaVarDecl')
        .map(({ name }) => name)
    const fieldsToInstrument = contractCall.oldFields.filter((value, key) =>
        declaredMonitorVariables.includes(key)
    )

    // TODO(#61): handle failed transactions
    // Add a special variable `last_error` that tracks error messages of failed transactions
    // fieldsToInstrument.push({ name: 'last_error', type: 'TlaStr', value: '' })

    // Declaration of  "Init" (according to `contractCall.oldFields`)
    const tlaInit = tlaJsonOperDecl__And(
        'Init',
        fieldsToInstrument
            .map((value, name) => {
                return tlaJsonEq__NameEx__ValEx(
                    name,
                    false,
                    tlaJsonOfNative(value)
                )
            })
            .valueSeq()
            .toArray()
    )

    // Declaration of "Next" (according to `tx`)
    const envRecord = tlaJsonRecord([
        { name: 'height', kind: 'TlaInt', value: contractCall.height },
    ])
    const tlaMethodArgs = contractCall.methodArgs.map((arg) =>
        tlaJsonOfNative(arg)
    )
    const tlaNext = tlaJsonOperDecl__And('Next', [
        tlaJsonApplication(
            contractCall.method,
            [envRecord].concat(tlaMethodArgs)
        ),
        // TODO(#61): handle failed transactions
        // tlaJsonEq__NameEx__ValEx(
        //     'last_error',
        //     true,
        //     tlaJsonValEx('TlaStr', tx.error)
        // ),
    ])

    // Instantiate the monitor spec with declarations of "Init" and "Next"
    const extendedDeclarations = monitor['modules'][0]['declarations'].concat([
        tlaInit,
        tlaNext,
    ])
    const extendedModule = {
        ...monitor['modules'][0],
        declarations: extendedDeclarations,
    }
    return { ...monitor, modules: [extendedModule] }
}

// Return the appropriate type for an Apalache JSON IR value `v`.
export function tlaJsonTypeOfPrimitive(v: any) {
    switch (typeof v) {
        case 'boolean':
            return 'TlaBool'
        case 'bigint':
        case 'number':
            return 'TlaInt'
        case 'string':
            return 'TlaStr'
        default:
            assert(false, `Expected primitive type, got ${typeof v}`)
    }
}

// Return true iff `name` is a valid TLA+ Name.
// See Lamport, Specifying Systems, 15.1. The Simple Grammar
export function isTlaName(name: string): boolean {
    // From Lamport, Specifying Systems, 15.1. The Simple Grammar:
    // Letter = OneOf("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")
    // Numeral = OneOf("0123456789")
    // NameChar = Letter ∪ Numeral ∪ {"_"}
    // Name = Tok ( (NameChar* & Letter & NameChar*) \ ({"WF_", "SF_"} & NameChar+) )
    const re = /^[a-zA-Z0-9_]*[a-zA-Z][a-zA-Z0-9_]*$/
    return re.test(name)
}

/**
 * Return the Apalache JSON IR representation of a native JS value `v`.
 *
 * If `v` is a JS array (representing a Soroban `Vec` or `enum`), it is
 * translated into either a TLA+ sequence, or an Apalache variant, in particular:
 *   - a TLA+ sequence, if the array is empty or of homogenous types, or if `forceVec` is set.
 *   - an Apalache variant, in all other cases where the array is non-empty and its first element is a string.
 *
 * If `v` is a JS object (representing a Soroban `Bytes`, `Map` or `struct`), it is
 * translated into either a TLA+ string, a TLA+ record, or a TLA+ function, in particular:
 *   - a string, if the object has a `Buffer` property, that contains a zero-padded hex encoding of the payload.
 *   - a TLA+ record, if its keys are all strings and valid TLA+ names,
 *   - a TLA+ function, for all other keys.
 *
 * For example,
 *   [ 1, 2, 3 ]  ~~>  << 1, 2, 3 >>
 *   [ 'A', 42 ]  ~~>  Variant("A", 42)
 *   { type: 'Buffer', data: [190, 239] }  ~~>  "beef"
 *   { "a": 3, "b": 5 }  ~~>  [ a |-> 3, b |-> 5 ]
 *   { "2": 3, "4": 5 }  ~~>  SetAsFun({ <<"2", 3>>, <<"4", 5>> })
 */
export function tlaJsonOfNative(v: any, forceVec: boolean = false): any {
    if (typeof v === 'object') {
        if (Array.isArray(v)) {
            // a JS array
            if (
                v.length == 0 ||
                forceVec ||
                v.every((elem) => typeof elem === typeof v[0])
            ) {
                // a Soroban `Vec`
                // [ 1, 2, 3 ]  ~~>  << 1, 2, 3 >>
                return {
                    type: 'Untyped',
                    kind: 'OperEx',
                    oper: 'TUPLE',
                    args: v.map((arg) => tlaJsonOfNative(arg)),
                }
            } else if (v.length > 0 && typeof v[0] === 'string') {
                // a Soroban `enum`
                // [ 'A', 42 ]   ~~>  Variant("A", 42)
                const tlaUnit = {
                    type: 'Untyped',
                    kind: 'OperEx',
                    oper: 'OPER_APP',
                    args: [{ type: 'Untyped', kind: 'NameEx', name: 'UNIT' }],
                }
                return {
                    type: 'Untyped',
                    kind: 'OperEx',
                    oper: 'Variants!Variant',
                    args:
                        v.length > 1
                            ? v.map((arg) => tlaJsonOfNative(arg))
                            : [...v.map(tlaJsonApplication), tlaUnit],
                }
            } else {
                assert(false, `Unexpected native value: ${v}`)
            }
        }
        // a "proper" JS object (not an array)
        if (v.type == 'Buffer') {
            // a Soroban `Bytes[N]`
            // v.data contains the bytes, as integers - render them into a string
            // { type: 'Buffer', data: [190, 239] }  ~~>  "beef"
            return tlaJsonOfNative(
                v.data
                    .map((x: number) => x.toString(16).padStart(2, '0'))
                    .join('')
            )
        }
        // a Soroban struct or `Map`
        // If there is at least one key and all keys are TLA+ names, make it a TLA+ record, otherwise a TLA+ function.
        // { "a": 3, "b": 5 }  ~~>  [ a |-> 3, b |-> 5 ]
        if (
            Object.keys(v).length > 0 &&
            Object.keys(v).every(
                (key) => typeof key === 'string' && isTlaName(key)
            )
        ) {
            return {
                type: 'Untyped',
                kind: 'OperEx',
                oper: 'RECORD',
                args: Object.entries(v)
                    .flat()
                    .map((arg) => tlaJsonOfNative(arg)),
            }
        }
        // { "2": 3, "4": 5 }  ~~>  SetAsFun({ <<"2", 3>>, <<"4", 5>> })
        return {
            type: 'Untyped',
            kind: 'OperEx',
            oper: 'Apalache!SetAsFun',
            args: [
                {
                    type: 'Untyped',
                    kind: 'OperEx',
                    oper: 'SET_ENUM',
                    args: Object.entries(v).map(([key, value]) =>
                        tlaJsonOfNative([key, value], true)
                    ),
                },
            ],
        }
    }
    // a primitive value
    // v  ~~>  ValEx(v)
    return tlaJsonValEx(tlaJsonTypeOfPrimitive(v), v)
}

/**
 * Return an Apalache TLA+ operator declaration of the form `operDeclName` == `conjuncts`_0 /\ ... /\ `conjuncts`_n.
 * @param operDeclName Operator name
 * @param conjuncts Body conjuncts
 * @returns The operator declaration in Apalache IR JSON: https://apalache.informal.systems/docs/adr/005adr-json.html
 */
function tlaJsonOperDecl__And(operDeclName: string, conjuncts: any): any {
    return {
        type: 'Untyped',
        kind: 'TlaOperDecl',
        name: operDeclName,
        formalParams: [],
        isRecursive: false,
        body: {
            type: 'Untyped',
            kind: 'OperEx',
            oper: 'AND',
            args: conjuncts,
        },
    }
}

/**
 * Return an Apalache TLA+ name expression.
 * @returns the name expression in Apalache IR JSON: https://apalache.informal.systems/docs/adr/005adr-json.html
 */
function tlaJsonNameEx(name: string): any {
    return { type: 'Untyped', kind: 'NameEx', name: name }
}

/**
 * Return an Apalache TLA+ value expression.
 * @param kind Apalache type (e.g., "TlaStr" or "TlaBool")
 * @param value Expression value
 * @returns The value expression in Apalache IR JSON: https://apalache.informal.systems/docs/adr/005adr-json.html
 */
function tlaJsonValEx(kind: string, value: any): any {
    return {
        type: 'Untyped',
        kind: 'ValEx',
        value: { kind: kind, value: value },
    }
}

/**
 * Return an Apalache TLA+ record.
 * @param bindings Interleaved array of field names and field values.
 * @returns The record in Apalache IR JSON: https://apalache.informal.systems/docs/adr/005adr-json.html
 */
function tlaJsonRecord(bindings: any): any {
    return {
        type: 'Untyped',
        kind: 'OperEx',
        oper: 'RECORD',
        args: bindings.flatMap((binding) => [
            tlaJsonValEx('TlaStr', binding.name),
            tlaJsonValEx(binding.kind, binding.value),
        ]),
    }
}

/**
 * Return an Apalache TLA+ operator application.
 * @param operName Name of the operator to apply.
 * @param args Application arguments
 * @returns The operator application in Apalache IR JSON: https://apalache.informal.systems/docs/adr/005adr-json.html
 */
function tlaJsonApplication(operName: string, args: any): any {
    return {
        type: 'Untyped',
        kind: 'OperEx',
        oper: 'OPER_APP',
        args: [tlaJsonNameEx(operName)].concat(args),
    }
}

/**
 * Return an Apalache equality expression applied to a name expression LHS, and a value expression RHS, optionally priming the LHS.
 * @param name LHS name.
 * @param prime True iff `name` should appear primed in the expression.
 * @param valEx RHS value.
 * @returns The equality in Apalache IR JSON: https://apalache.informal.systems/docs/adr/005adr-json.html
 */
function tlaJsonEq__NameEx__ValEx(name: any, prime: boolean, valEx: any): any {
    const nameEx = { type: 'Untyped', kind: 'NameEx', name: name }
    const lhs = prime
        ? { type: 'Untyped', kind: 'OperEx', oper: 'PRIME', args: [nameEx] }
        : nameEx
    return { type: 'Untyped', kind: 'OperEx', oper: 'EQ', args: [lhs, valEx] }
}
