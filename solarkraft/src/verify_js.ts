/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Solarkraft monitors in JavaScript / TypeScript.
 *
 * This file provides a simple monitor framework to verify Stellar / Soroban
 * smart contract transactions in JavaScript / TypeScript.
 *
 * The monitor is written in TypeScript and run in a Node.js environment.
 * For an example, see `../test/e2e/verify_js_example.ts`.
 *
 * @author Thomas Pani, 2024
 */
import {
    ContractCallEntry,
    emptyContractStorage,
    FieldsMap,
    loadContractCallEntry,
} from './fetcher/storage.js'
import util from 'util'
import fs from 'fs'
import { SOLARKRAFT_DEFAULT_HOME } from './globals.js'

/* Environment types */

/**
 * The storage of a contract at a given ledger / point in time.
 *
 * Mimics the Soroban SDK by exposing the durability levels as functions
 * (rather than fields, as in `ContractStorage`).
 */
type EnvStorage = {
    instance: () => FieldsMap
    persistent: () => FieldsMap
    temporary: () => FieldsMap
}

/**
 * The environment available to the monitor functions.
 *
 * Mimics the Soroban SDK `Env` class:
 * https://docs.rs/soroban-sdk/latest/soroban_sdk/struct.Env.html
 */
abstract class AbstractEnv {
    protected tx: ContractCallEntry

    constructor(contractCall: ContractCallEntry) {
        this.tx = contractCall
    }

    /** @returns The address of the contract that is currently executing. */
    current_contract_address() {
        return this.tx.contractId
    }

    /** @returns The current ledger. */
    ledger() {
        return {
            /** @returns A unix timestamp for when the ledger was closed. */
            timestamp: () => this.tx.timestamp,
        }
    }

    /**
     * Get the storage for accessing data modified by an executing contract.
     *
     * @param contractId The contract address to get the storage for. Defaults to the root invocation.
     */
    abstract storage(contractId: string): EnvStorage
}

/**
 * The environment available to monitor functions, when the transaction reverts.
 *
 * `storage()` returns the storage of the contract at the beginning of the transaction.
 */
export class EnvRevert extends AbstractEnv {
    storage(contractId: string = this.tx.contractId) {
        return {
            instance: () =>
                this.tx.oldStorage.get(contractId, emptyContractStorage())
                    .instance,
            persistent: () =>
                this.tx.oldStorage.get(contractId, emptyContractStorage())
                    .persistent,
            temporary: () =>
                this.tx.oldStorage.get(contractId, emptyContractStorage())
                    .temporary,
        }
    }
}

/**
 * The environment available to monitor functions, when the transaction succeeds.
 *
 * `storage()` returns the storage of the contract at the end of the transaction.
 * `oldStorage()` returns the storage of the contract at the beginning of the transaction.
 */
export class Env extends AbstractEnv {
    storage(contractId: string = this.tx.contractId): EnvStorage {
        return {
            instance: () =>
                this.tx.storage.get(contractId, emptyContractStorage())
                    .instance,
            persistent: () =>
                this.tx.storage.get(contractId, emptyContractStorage())
                    .persistent,
            temporary: () =>
                this.tx.storage.get(contractId, emptyContractStorage())
                    .temporary,
        }
    }
    oldStorage(contractId: string = this.tx.contractId): EnvStorage {
        return {
            instance: () =>
                this.tx.oldStorage.get(contractId, emptyContractStorage())
                    .instance,
            persistent: () =>
                this.tx.oldStorage.get(contractId, emptyContractStorage())
                    .persistent,
            temporary: () =>
                this.tx.oldStorage.get(contractId, emptyContractStorage())
                    .temporary,
        }
    }
}

/* A simple boolean expression language */

type ConditionSome = { type: 'some'; conditions: Condition[] }
type ConditionEvery = { type: 'every'; conditions: Condition[] }
export type Condition = ConditionSome | ConditionEvery | boolean

/** Logical OR of the given conditions. */
export function some(...args: Condition[]): ConditionSome {
    return { type: 'some', conditions: args }
}

/** Logical AND of the given conditions.  */
export function every(...args: Condition[]): ConditionEvery {
    return { type: 'every', conditions: args }
}

/** Evaluate a condition to a boolean. */
export function evaluateCondition(condition: Condition): boolean {
    if (typeof condition === 'boolean') {
        return condition
    }
    switch (condition.type) {
        case 'every':
            return condition.conditions.every((x) => evaluateCondition(x))
        case 'some':
            return condition.conditions.some((x) => evaluateCondition(x))
    }
}

/* Macros / monitor helper functions */

/**
 * Return a condition that checks if the given token amount has been transferred to the given address
 * on a Stellar Asset Contract.
 *
 * @param env The environment to evaluate the condition in.
 * @param token The SAC token address. Must implement CAP-46-6 Smart Contract Standardized Asset.
 * @param to The address of the token receiver.
 * @param amount The amount of tokens transferred.
 */
export function tokenReceived(
    env: Env,
    token: string,
    to: string,
    amount: bigint
): Condition {
    const oldTokenStorage = env.oldStorage(token).persistent()
    const tokenStorage = env.storage(token).persistent()

    return (
        // token balance is stored under a variant data key Balance(Address)
        // that points to a struct { amount: i128, authorized: bool, clawback: bool }
        tokenStorage.get(`Balance,${to}`).amount ==
        (oldTokenStorage.get(`Balance,${to}`)?.amount ?? 0n) + amount
    )
}

/**
 * Return a condition that checks if the given token amount has been transferred from one address
 * to another address on a Stellar Asset Contract.
 *
 * @param env The environment to evaluate the condition in.
 * @param token The SAC token address. Must implement CAP-46-6 Smart Contract Standardized Asset.
 * @param from The address of the token sender.
 * @param to The address of the token receiver.
 * @param amount The amount of tokens transferred.
 */
export function tokenTransferred(
    env: Env,
    token: string,
    from: string,
    to: string,
    amount: bigint
): Condition {
    const oldTokenStorage = env.oldStorage(token).persistent()
    const tokenStorage = env.storage(token).persistent()
    return every(
        // token balance is stored under a variant data key Balance(Address)
        // that points to a struct { amount: i128, authorized: bool, clawback: bool }
        (oldTokenStorage.get(`Balance,${from}`)?.amount ?? 0n) >= amount,
        tokenStorage.get(`Balance,${from}`).amount ==
            (oldTokenStorage.get(`Balance,${from}`)?.amount ?? 0n) - amount,
        tokenStorage.get(`Balance,${to}`).amount ==
            (oldTokenStorage.get(`Balance,${to}`)?.amount ?? 0n) + amount
    )
}

/* Monitoring code */

/**
 * Main entry point to derive a Solarkraft JavaScript monitor.
 */
export class SolarkraftJsMonitor {
    private current_tx: ContractCallEntry

    verify(
        transaction_hashes: string[],
        solarkraftHome: string = SOLARKRAFT_DEFAULT_HOME
    ) {
        transaction_hashes.forEach((txHash) => {
            // Read the state from fetcher output
            const contractCallResult = loadContractCallEntry(
                solarkraftHome,
                txHash
            )
            if (contractCallResult.isLeft()) {
                console.log(contractCallResult.value)
                console.log('[Error]')
                return
            }

            const contractCall = contractCallResult.value

            console.log(
                `Verifying ${contractCall.method} (${contractCall.txSuccess ? 'successful' : 'failed'} tx ${txHash})...`
            )

            // Check if the method exists in the monitor
            if (this[contractCall.method] === undefined) {
                console.warn(
                    `[Warn]: Method ${contractCall.method} not defined in the monitor`
                )
                console.log()
                return
            }

            // Call the monitor function
            this.current_tx = contractCall
            this[contractCall.method](...contractCall.methodArgs)

            console.log()
        })
        console.log('Verification complete.')
    }

    /**
     * Assert that the transaction reverts if the given condition holds.
     */
    reverts_if(should_revert: (env: EnvRevert) => Condition) {
        const env = new EnvRevert(this.current_tx)
        let condition: Condition
        try {
            condition = should_revert(env)
        } catch (e) {
            console.error(`[Error]: Failed to evaluate reverts_if condition:`)
            logEvaluationError(e)
            return
        }
        if (evaluateCondition(condition)) {
            if (!this.current_tx.txSuccess) {
                console.log(
                    `[OK]: tx reverted as expected by reverts_if conditions`
                )
                console.log(
                    util.inspect(condition, { depth: null, colors: true })
                )
            } else {
                console.error(
                    `[Error]: reverts_if conditions indicate that the tx should've reverted`
                )
                console.log(
                    util.inspect(condition, { depth: null, colors: true })
                )
            }
        } else if (!this.current_tx.txSuccess) {
            console.warn(
                `[Warn]: reverts_if conditions do not indicate that the tx should've reverted`
            )
            console.warn(
                `    Consider adding more conditions to the reverts_if block`
            )
        }
    }

    /**
     * Assert a condition that should hold if the transaction succeeds.
     */
    succeeds_with(should_hold: (env: Env) => Condition) {
        const env = new Env(this.current_tx)
        if (this.current_tx.txSuccess) {
            let condition: Condition
            try {
                condition = should_hold(env)
            } catch (e) {
                console.error(
                    `[Error]: Failed to evaluate succeeds_with condition ${e}`
                )
                logEvaluationError(e)
                return
            }
            if (evaluateCondition(condition)) {
                console.log(`[OK]: all succeeds_with conditions hold`)
            } else {
                console.error(
                    `[Error]: some succeeds_with conditions do not hold`
                )
                console.log(
                    util.inspect(condition, { depth: null, colors: true })
                )
            }
        }
    }
}

/**
 * Print a nice error message when evaluating a condition fails.
 *
 * Often, this is triggered by undefined fields in the monitor functions.
 */
function logEvaluationError(e: Error) {
    console.error(`    ${e.message}`)
    try {
        // best-effort attempt parse and print the line of code that caused it
        e.stack
            .split('\n')
            .slice(1, 2)
            .map((r) =>
                r.match(/file:\/\/(?<file>.*):(?<line>\d+):(?<pos>\d+)/)
            )
            .forEach((r) => {
                if (
                    r &&
                    r.groups &&
                    r.groups.file.substr(0, 8) !== 'internal'
                ) {
                    const { file, line, pos } = r.groups
                    const f = fs.readFileSync(file, 'utf8').split('\n')
                    console.error(`    ${file}:${line}:${pos}`)
                    console.error(f[parseInt(line) - 1])
                    console.error(' '.repeat(parseInt(pos) - 1) + '^')
                }
            })
    } catch (e) {
        // fail silently
    }
}
