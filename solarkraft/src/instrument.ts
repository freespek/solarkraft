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
 * Expected monitor shape:
 * We assume the monitors are organized in the following way:
 *  - 1 central monitor specification `Spec`, which declares invariants relating to the pre- and post-transaction states.
 *    No invariant declared in this specification reasons about contract methods or their internals.
 *  - 1 method monitor per method. For each method `foo`, we expect a `foo.tla` specification, which declares no variables
 *    and defines a top-level operator `foo(...)`, representing the collection of all method invariants.
 *    This operator takes `k` arguments, where `k` is the number of arguments declared for the contract method `foo`,
 *    in the same order as the contract method `foo`. The operator parameter names should, but are not required to,
 *    correspond to the parameter names of `foo`.
 *    This enumeration counts the parameters in the contract source code, and assumes the first argument passed captures
 *    the environment data.
 *
 * It is assumed the central specification extends all method specifications. Alternitively, for small monitors, all such method operators could
 * be delared directly in the central specification, though we recommend the modular approach for readability reasons.
 *
 * Given a transaction JSON with the shape:
 * ```
 * {
 *  ...
 *  "method": "foo",
 *  "methodArgs": [arg1, ..., argK],
 *  "fields": [
 *     [v1, b1],
 *     ...,
 *     [vn, bn]
 *  ],
 *  "oldFields": [
 *     [v1, a1],
 *     ...,
 *     [vn, an]
 *  ]
 * }
 * ```
 * the corresponding instrumented monitor specification has the shape:
 * ```
 * ...
 * <Spec>
 * ...
 *
 * Init == v1 = a1 /\ ...  /\ vn = an
 * Next ==
 *   /\ foo(arg1, ..., argK)
 *   /\ v1' = b1 /\ ... /\ vn' = bn
 * ```
 * (we omit the conversion from JS values to TLA values for brevty)
 */

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
    // Since `fields` and `oldFields` can have different entries, due to data storage lifetimes,
    // we initialize all variables that appear in the monitor specification but are
    // missing from either fields collection, with Gen(1).
    //
    // Example:
    //   - Monitor declares variables A, B
    //   - oldFields contains {A: a, C: c}
    //
    // then:
    //   - declaredMonitorVariables = [A,B]
    //   - oldFieldsToInstrument = {A: a}
    //   - missingOldFields = [B]
    const declaredMonitorVariables = monitor.modules[0].declarations
        .filter(({ kind }) => kind == 'TlaVarDecl')
        .map(({ name }) => name)
    const oldFieldsToInstrument = contractCall.oldFields.filter((value, key) =>
        declaredMonitorVariables.includes(key)
    )
    const missingOldFields = declaredMonitorVariables.filter(
        (k) => !contractCall.oldFields.has(k)
    )
    const fieldsToInstrument = contractCall.fields.filter((value, key) =>
        declaredMonitorVariables.includes(key)
    )
    const missingFields = declaredMonitorVariables.filter(
        (k) => !contractCall.fields.has(k)
    )

    const typeHints = contractCall.typeHints ?? {
        methods: {},
        variables: {},
    }
    const varHints = typeHints['variables'] ?? {}

    // TODO(#61): handle failed transactions
    // Add a special variable `last_error` that tracks error messages of failed transactions
    // fieldsToInstrument.push({ name: 'last_error', type: 'TlaStr', value: '' })

    // Declaration of  "Init" (according to `contractCall.oldFields`)
    const oldInstrumented = tlaJsonAnd(
        oldFieldsToInstrument
            .map((value, name) =>
                tlaJsonEq__NameEx__ValEx(
                    name,
                    false,
                    tlaJsonOfNative(value, false, varHints[name])
                )
            )
            .valueSeq()
            .toArray()
    )

    const oldMissing = tlaJsonAnd(
        missingOldFields.map((name) =>
            tlaJsonEq__NameEx__ValEx(name, false, GEN1)
        )
    )

    const tlaInit = tlaJsonOperDecl__And('Init', [oldInstrumented, oldMissing])

    // Declaration of "Next" (according to `contractCall.fields` and `contractCall.method` / `.methodArgs`)
    const envRecord = tlaJsonRecord([
        { name: 'height', kind: 'TlaInt', value: contractCall.height },
        { name: 'timestamp', kind: 'TlaInt', value: contractCall.timestamp },
    ])

    const currentInstrumented = tlaJsonAnd(
        fieldsToInstrument
            .map((value, name) =>
                tlaJsonEq__NameEx__ValEx(
                    name,
                    true, // prime `name`
                    tlaJsonOfNative(value, false, varHints[name])
                )
            )
            .valueSeq()
            .toArray()
    )
    const currentMissing = tlaJsonAnd(
        missingFields.map((name) => tlaJsonEq__NameEx__ValEx(name, true, GEN1)) // name' = Gen(1)
    )

    const methodArgHints = ((typeHints['methods'] ?? {})[
        contractCall.method
    ] ?? [Array(contractCall.methodArgs.length).fill(undefined)])[0]

    const tlaMethodArgs = contractCall.methodArgs.map((arg, i) =>
        tlaJsonOfNative(arg, false, methodArgHints[i])
    )
    const tlaNext = tlaJsonOperDecl__And('Next', [
        tlaJsonApplication(
            contractCall.method,
            [envRecord].concat(tlaMethodArgs)
        ),
        currentInstrumented,
        currentMissing,
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
export function tlaJsonOfNative(
    v: any,
    forceVec: boolean = false,
    hint?: any
): any {
    if (typeof v === 'object') {
        if (Array.isArray(v)) {
            // a JS array
            // we require a hint in the case of ambiguous inputs
            const mustHaveHint =
                !forceVec &&
                v.length > 0 &&
                v.every((elem) => typeof elem === 'string')

            if (mustHaveHint && hint === undefined)
                throw new TypeError(
                    `Ambiguous type detected for ${v}. Please \`fetch\` with --typemap provided.`
                )

            if (
                v.length == 0 ||
                forceVec ||
                (!mustHaveHint &&
                    v.every((elem) => typeof elem === typeof v[0])) ||
                (mustHaveHint && 'vec' in hint)
            ) {
                // a Soroban `Vec`
                // [ 1, 2, 3 ]  ~~>  << 1, 2, 3 >>
                const childHints: any[] = Array(v.length).fill(
                    (hint ?? {})['vec']
                )
                return {
                    type: 'Untyped',
                    kind: 'OperEx',
                    oper: 'TUPLE',
                    args: v.map((arg, i) =>
                        tlaJsonOfNative(arg, forceVec, childHints[i])
                    ),
                }
            } else if (
                v.length > 0 &&
                typeof v[0] === 'string' &&
                (!mustHaveHint || 'enum' in hint)
            ) {
                // a Soroban `enum`
                // [ 'A', 42 ]   ~~>  Variant("A", 42)
                const tlaUnit = {
                    type: 'Untyped',
                    kind: 'OperEx',
                    oper: 'OPER_APP',
                    args: [{ type: 'Untyped', kind: 'NameEx', name: 'UNIT' }],
                }
                const childHints: any[] =
                    (hint ?? {})['enum'] ?? Array(v.length).fill(undefined)
                childHints[0] = 'Str'
                return {
                    type: 'Untyped',
                    kind: 'OperEx',
                    oper: 'Variants!Variant',
                    args:
                        v.length > 1
                            ? v.map((arg, i) =>
                                  tlaJsonOfNative(arg, forceVec, childHints[i])
                              )
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
            const entries = Object.entries(v)
            const flatEntries: any[] = entries.flat()
            const childHints = entries
                .map((arg) => {
                    const k: string = arg[0]
                    return ['Str', (hint ?? {})[k]]
                })
                .flat()

            return {
                type: 'Untyped',
                kind: 'OperEx',
                oper: 'RECORD',
                args: flatEntries.map((arg, i) =>
                    tlaJsonOfNative(arg, forceVec, childHints[i])
                ),
            }
        }
        // { "2": 3, "4": 5 }  ~~>  SetAsFun({ <<"2", 3>>, <<"4", 5>> })
        const childHints = (hint ?? {})['map']
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
                        tlaJsonOfNative([key, value], true, childHints)
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
 * Return an Apalache TLA+ expression of the form `conjuncts`_0 /\ ... /\ `conjuncts`_n.
 * @param conjuncts Body conjuncts
 * @returns The conjunction in Apalache IR JSON: https://apalache.informal.systems/docs/adr/005adr-json.html
 */
function tlaJsonAnd(conjuncts: any[]): any {
    return {
        type: 'Untyped',
        kind: 'OperEx',
        oper: 'AND',
        args: conjuncts,
    }
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
        body: tlaJsonAnd(conjuncts),
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
 * The Apalache TLA+ expression `Gen(1)`.
 */
const GEN1 = {
    type: 'Untyped',
    kind: 'OperEx',
    oper: 'Apalache!Gen',
    args: [tlaJsonValEx('TlaInt', 1)],
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
