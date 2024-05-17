import { ContractCallEntry } from './fetcher/storage.js'

/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
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
            .map((value, name) =>
                tlaJsonEq__NameEx__ValEx(
                    name,
                    false,
                    tlaJsonValEx(tlaJsonTypeOfNative(value), value)
                )
            )
            .valueSeq()
            .toArray()
    )

    // Declaration of "Next" (according to `tx`)
    const envRecord = tlaJsonRecord([
        { name: 'height', kind: 'TlaInt', value: contractCall.height },
    ])
    const tlaMethodArgs = contractCall.methodArgs.map((v) =>
        tlaJsonValEx(tlaJsonTypeOfNative(v), v)
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

// Decode a Native JS value `v` into its corresponding Apalache IR type.
function tlaJsonTypeOfNative(v: any) {
    switch (typeof v) {
        case 'string':
            return 'TlaStr'
        case 'number':
            return 'TlaInt'
        case 'bigint':
            return 'TlaInt'
        case 'boolean':
            return 'TlaBool'
        // an array or object
        // TODO(#46): support composite types (sequence, tuple, record, set, map)
        // if (Array.isArray(o)) ...
        case 'object':
        case 'symbol':
        case 'undefined':
        case 'function':
            return undefined
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
