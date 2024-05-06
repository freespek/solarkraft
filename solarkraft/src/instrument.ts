/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
type Value = { type: string; value: any }
type Binding = { name: string; type: string; value: any }
type State = Binding[]
type Transaction = {
    functionName: string
    functionArgs: Value[]
    env: { timestamp: number }
    error: string
}

// Return true iff `o` is a Javascript object.
function isObject(o: any) {
    return typeof o === 'object' && !Array.isArray(o) && o !== null
}

// Decode an ITF value `value` into a Javascript value.
// TODO(#46): support composite types (sequence, tuple, record, set, map)
function decodeITFValue(value: any) {
    if (
        isObject(value) &&
        Object.prototype.hasOwnProperty.call(value, '#bigint')
    ) {
        return parseInt(value['#bigint'])
    }
    return value
}

/**
 * Return a `State` from an ITF JSON object.
 * @param itf ITF JSON object, see https://apalache.informal.systems/docs/adr/015adr-trace.html
 * @returns `State`
 */
export function stateFromItf(itf: any): State {
    // const vars = itf['vars'] // e.g., [ "is_initialized", "last_error" ]
    const varTypes = itf['#meta']['varTypes'] // e.g., { "is_initialized": "Bool", "last_error": "Str" }
    const initState = itf['states'][0] // e.g., [ { "is_initialized": false, "last_error": "" }, state1, ... ]
    delete initState['#meta']

    const state = Object.entries(initState)
        .filter(([name]) => name != '#meta')
        .map(([name, value]) => ({
            name: name,
            value: decodeITFValue(value),
            type: 'Tla' + varTypes[name],
        }))
    return state
}

/**
 * Return an instrumented monitor specification.
 * @param monitor A TLA+ monitor, as returned from `apalache typecheck --output=temp.json`
 * @param state The blockchain state before executing the transaction / the monitor.
 * @param tx The transaction being applied to `state`.
 * @returns The instrumented TLA+ monitor.
 */
export function instrumentMonitor(
    monitor: any,
    state: State,
    tx: Transaction
): any {
    // Only instrument state variables that are delcared in the monitor spec
    // (otherwise we provoke type errors in Apalache Snowcat, via undeclared variables)
    const declaredMonitorVariables = monitor.modules[0].declarations
        .filter(({ kind }) => kind == 'TlaVarDecl')
        .map(({ name }) => name)
    state = state.filter(({ name }) => declaredMonitorVariables.includes(name))

    // Add a special variable `last_error` that tracks error messages of failed transactions
    state.push({ name: 'last_error', type: 'TlaStr', value: '' })

    // Declaration of  "Init" (according to `state`)
    const tlaInit = tlaJsonOperDecl__And(
        'Init',
        state.map((binding) =>
            tlaJsonEq__NameEx__ValEx(
                binding.name,
                false,
                tlaJsonValEx(binding.type, binding.value)
            )
        )
    )

    // Declaration of "Next" (according to `tx`)
    const envRecord = tlaJsonRecord([
        { name: 'timestamp', kind: 'TlaInt', value: tx.env.timestamp },
    ])
    const txArgs = tx.functionArgs.map((v) => tlaJsonValEx(v.type, v.value))
    const tlaNext = tlaJsonOperDecl__And('Next', [
        tlaJsonApplication(tx.functionName, [envRecord].concat(txArgs)),
        tlaJsonEq__NameEx__ValEx(
            'last_error',
            true,
            tlaJsonValEx('TlaStr', tx.error)
        ),
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
