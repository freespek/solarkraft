/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

import { spawnSync } from 'child_process'
import { existsSync } from 'node:fs'
import path from 'node:path'

// TODO(#34): fix hardcoded path to Apalache
const APALACHE_DIST = '/opt/apalache'
const APALACHE_BIN = path.join(APALACHE_DIST, 'bin', 'apalache-mc')

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
    // Add a special variable `last_error` that tracks error messages of failed transactions
    state.push({ name: 'last_error', type: 'TlaStr', value: '' })

    // Declaration of  "Init" (according to `state`)
    const tlaInit = tlaJsonOperDecl__Conjunction(
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
    const tlaNext = tlaJsonOperDecl__Conjunction('Next', [
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
function tlaJsonOperDecl__Conjunction(
    operDeclName: string,
    conjuncts: any
): any {
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

/**
 * Verify transactions fetched from the ledger
 * @param args the arguments parsed by yargs
 */
export function verify(args: any) {
    console.log(
        `*** WARNING: THIS IS A MOCK. NOTHING IS IMPLEMENTED YET. ***\n`
    )
    console.log(`Verifying transaction: ${args.txHash}...`)

    if (!existsSync(args.monitor)) {
        console.log(`The monitor file ${args.monitor} does not exist.`)
        console.log('[Error]')
        return
    }

    console.log(`Running Apalache (check ${args.monitor})...`)
    const child = spawnSync(APALACHE_BIN, ['check', '--length=1', args.monitor])

    switch (child.status) {
        case 0: {
            console.log('[OK]')
            break
        }
        case 12: {
            // Deadlock
            console.log('Monitor is unable to reproduce the transaction')
            console.log('[Fail]')
            break
        }
        default: {
            console.log(
                `Internal error: Apalache failed with error code ${child.status}`
            )
            console.log('[Error]')
            break
        }
    }
}
