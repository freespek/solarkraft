/**
 * This is an example of how to write a Solarkraft runtime monitor in
 * TypeScript.
 *
 * This is a monitor for the pool contract from Xycloans:
 * https://github.com/xycloo/xycloans/tree/e0663724eebf2ff52d59c836b697e97cd9f629a8/pool/src
 *
 * The test targets a historical commit known to contain a (now fixed) vulnerability,
 * where the fee per share is subject to a rounding error, found by OtterSec:
 * https://github.com/xycloo/xycloans/blob/main/audits/osec.pdf
 * https://github.com/xycloo/xycloans/commit/b26e0124ab0b84c1be25c636492671f106653f09
 * 
 * The monitor checks that the fee per share is calculated correctly and that
 * the rewards are distributed correctly.
 * 
 * @author Thomas Pani, 2024
 */
import {
    every,
    Env,
    EnvRevert,
    SolarkraftJsMonitor,
    tokenReceived,
    tokenTransferred,
} from '../../src/verify_js.js'
import { OrderedMap } from 'immutable'
import { Divide, ROUNDING_MODE } from 'big-round'

const divideCeil = Divide(ROUNDING_MODE.DIRECTED_TOWARDS_POSITIVE_INFINITY)
const divideFloor = Divide(ROUNDING_MODE.DIRECTED_TOWARDS_NEGATIVE_INFINITY)

const STROOP = 10_000_000n

const XLM_TOKEN_SAC_TESTNET = 'CDLZFC3SYJYDZT7K67VZ75HPJVIEUVNIXF47ZG2FB2RMQQVU2HHGCYSC'

/* the monitor */

class XycloansPoolMonitor extends SolarkraftJsMonitor {
    // shares per address
    private shares = OrderedMap<string, bigint>()
    // fee per share for the entire pool, in stroops
    private fee_per_share_universal = 0n

    // total number of shares
    private total_shares = () => this.shares.reduce((acc, x) => acc + x, 0n)

    initialize(token: string) {
        this.reverts_if((env: EnvRevert) => {
            return env.storage().instance().has('TokenId')
        })

        this.succeeds_with((env: Env) => {
            return every(
                // check that `TokenId` is set to the XLM SAC
                token == XLM_TOKEN_SAC_TESTNET,
                env.storage().instance().get('TokenId') == token
            )
        })
    }

    deposit(from: string, amount: bigint) {
        this.succeeds_with((env: Env) => {
            const token = env.storage().instance().get('TokenId')

            // side-effects: we track deposits locally to compute rewards later
            this.shares = this.shares.update(from, 0n, (x) => x + amount)

            return every(
                // the pool received `amount` tokens
                tokenReceived(env, token, env.current_contract_address(), amount),
                // `from` received `amount` shares
                this.shares.get(from) == env.storage().persistent().get(`Balance,${from}`),
                env.storage().persistent().get(`Balance,${from}`) == env.oldStorage().persistent().get(`Balance,${from}`, 0n) + amount
            )
        })
    }

    borrow(receiver_id: string, amount: bigint) {
        this.succeeds_with((env: Env) => {
            const expected_fee = divideCeil(amount * STROOP, 12_500_000_000n)
            const expected_fee_per_share_universal = env.oldStorage().instance().get('FeePerShareUniversal', 0n) + divideFloor(expected_fee * STROOP, this.total_shares())

            // side-effect: we update the fee per share to compute rewards later
            this.fee_per_share_universal = expected_fee_per_share_universal

            return every(
                // `FeePerShareUniversal` has been updated correctly
                this.fee_per_share_universal == env.storage().instance().get('FeePerShareUniversal'),
                // the receiver paid the expected fee to the pool
                tokenTransferred(env, XLM_TOKEN_SAC_TESTNET, receiver_id, env.current_contract_address(), expected_fee)
            )
        })
    }

    update_fee_rewards(addr: string) {
        this.succeeds_with((env: Env) => {
            const fees_not_yet_considered = this.fee_per_share_universal - env.oldStorage().persistent().get(`FeePerShareParticular,${addr}`, 0n)
            const expected_reward = divideFloor(this.shares.get(addr, 0n) * fees_not_yet_considered, STROOP) 
            const actual_reward = env.storage().persistent().get(`MaturedFeesParticular,${addr}`) - env.oldStorage().persistent().get(`MaturedFeesParticular,${addr}`, 0n)

            // Uncomment the following lines to debug the expected reward
            // if (expected_reward != actual_reward) {
            //     console.warn(`actual <> expected reward: ${actual_reward} <> ${expected_reward}`)
            // }

            return every (
                // fee per share for `addr` is bumped to the universal fee per share
                env.storage().persistent().get(`FeePerShareParticular,${addr}`) == this.fee_per_share_universal,
                // delta of matured rewards for `addr` have been added
                expected_reward == actual_reward
            )
        })
    }

    // we omit the following functions, as they are not relevant for our example:
    //
    // matured(addr: string) { }
    // shares(addr: string) { }
    // withdraw(addr: string, amount: bigint) { }
    // withdraw_matured(addr: string) { }
}

new XycloansPoolMonitor().verify(
    [
        '49ce70a0fe73f9b815f50dbe13403608242cec0770ac32eb24d1a425e39467be',
        'af8d698431a4354bbe74517d741bbb278180eae2c6907ddc0abf5fcacd8b938b',
        '20a4726ab7291e00bfaad767a034844ffffd25f73882b5288da5486e3cc01973',
        'e5064617326554c02de8edd6628f1e1951903497698b3f1f5f0b00e03b2a16b6',
        'e940abb2dbb2f29c2d7bb9ddbc02941742f89c5a8afa795f30441fafb7de8cb7'
    ],
    // Contract call entries for the above transactions have been  pre-fetched with
    //   $ solarkraft fetch --id CBBDVFSEI26N7DJBPMVQDNWX2GD7RF2PC2HYMUVKGU72NCFAKERFYIKL --height 477909 --home test/e2e/tla/
    'test/e2e/tla/'
)
