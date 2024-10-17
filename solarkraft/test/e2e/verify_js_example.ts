/**
 * This is an example of how to write a Solarkraft runtime monitor in
 * TypeScript.
 *
 * This is a monitor for the timelock contract from soroban-examples:
 * https://github.com/stellar/soroban-examples/tree/v21.6.0/timelock
 *
 * We extend the SolarkraftJsMonitor class and provide methods corresponding to the
 * contract functions. We use the `reverts_if` and `succeeds_with` methods to specify
 * the conditions under which the contract should revert or succeed.
 *
 * The monitor is then verified by instantiating `TimelockMonitor` and calling the
 * `verify` method with the transaction hashes of the transactions to be verified.
 * We expect that the tranactions have been fetched from the ledger using the
 * `solarkraft fetch` command.
 *
 * @author Thomas Pani, 2024
 */
import {
    some,
    every,
    Condition,
    Env,
    EnvRevert,
    SolarkraftJsMonitor,
} from '../../src/verify_js.js'
import _ from 'lodash'

// Helper function to check if a token transfer was successful.
//
// `timelock` is using the custom token contract from `soroban-examples`,
// which implements the SEP-41 Token Interface, but not the storage layout
// of a CAP-46-6 Smart Contract Standardized Asset.
// Thus, we do not use the `tokenTransferred` function from the `verify_js`
// module, but instead define a custom function here.
function tokenTransferred(
    env: Env,
    token: string,
    from: string,
    to: string,
    amount: number
): Condition {
    const oldTokenStorage = env.oldStorage(token).persistent()
    const tokenStorage = env.storage(token).persistent()
    return every(
        tokenStorage.get(`Balance,${from}`) ==
            oldTokenStorage.get(`Balance,${from}`) - amount,
        tokenStorage.get(`Balance,${to}`) ==
            oldTokenStorage.get(`Balance,${to}`, 0) + amount
    )
}

/* generate from contract spec */

enum TimeBoundKind {
    Before,
    After,
}

interface TimeBound {
    kind: TimeBoundKind
    timestamp: number
}

interface ClaimableBalance {
    token: string
    amount: number
    claimants: string[]
    time_bound: TimeBound
}

/* the monitor */

class TimelockMonitor extends SolarkraftJsMonitor {
    deposit(
        from: string,
        token: string,
        amount: number,
        claimants: string[],
        time_bound: TimeBound
    ) {
        this.reverts_if((env: EnvRevert) => {
            return env.storage().instance().has('Init')
        })

        this.succeeds_with((env: Env) => {
            const Balance: ClaimableBalance = env.storage().instance().get('Balance')
            return every(
                env.storage().instance().has('Init'),
                Balance.amount == amount,
                _.isEqual(Balance.claimants, claimants),
                _.isEqual(Balance.time_bound, time_bound),
                tokenTransferred(env, token, from, env.current_contract_address(), amount)
            )
        })

        // Alternative:
        this.succeeds_with((env: Env) => env.storage().instance().has('Init'))
        this.succeeds_with((env: Env) => {
            const Balance: ClaimableBalance = env.storage().instance().get('Balance')
            return (
                Balance.amount == amount &&
                _.isEqual(Balance.claimants, claimants) &&
                _.isEqual(Balance.time_bound, time_bound)
            )
        })
        this.succeeds_with((env: Env) =>
            tokenTransferred(env, token, from, env.current_contract_address(), amount)
        )
    }

    claim(claimant: string) {
        this.reverts_if((env: EnvRevert) => {
            const Balance: ClaimableBalance = env.storage().instance().get('Balance')
            return some(
                !env.storage().instance().has('Init'),
                !env.storage().instance().has('Balance'),
                !Balance?.claimants.includes(claimant),
                Balance?.time_bound.kind == TimeBoundKind.Before &&
                    env.ledger().timestamp() > Balance?.time_bound.timestamp,
                Balance?.time_bound.kind == TimeBoundKind.After &&
                    env.ledger().timestamp() < Balance?.time_bound.timestamp
            )
        })
        this.succeeds_with((env: Env) => {
            const Balance: ClaimableBalance = env.oldStorage().instance().get('Balance')
            return every(
                !env.storage().instance().has('Balance'),
                tokenTransferred(env, Balance.token, env.current_contract_address(), claimant, Balance.amount)
            )
        })
    }
}

new TimelockMonitor().verify(
    [
        'e10a55db588f097f8ce9e214ae717c5ecbd6d13d5a2fb3142c71c1866c9ca537',
        '0f3738d9fddc0a17a91b063e54113879d6da88818006144a9db908ed85c7163b',
        '958fb84f272e53fed0cb9ab584770b344691b52dd843821dae47e782f2684ee8',
    ],
    // Contract call entries for the above transactions have been  pre-fetched with
    //   $ solarkraft fetch --id CA36GKEEH7QWJDCHWOEXWAJ7DO5I5STFDDAXUYG27QRORQPTV5P5E7D6 --height 227127 --home test/e2e/tla/
    'test/e2e/tla/'
)
