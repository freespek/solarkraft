/**
 * E2E tests for the JavaScript / TypeScript monitor in
 * `test/e2e/verify_js_example.ts`.
 *
 * @author Thomas Pani, 2024
 */

import { describe, it } from 'mocha'

import { spawn } from 'nexpect'

describe('verify JavaScript monitor', () => {
    it('reports success on `verify_js_example.ts`', function (done) {
        this.timeout(50_000)
        spawn('node dist/test/e2e/verify_js_example.js')
            .wait(
                'Verifying deposit (successful tx e10a55db588f097f8ce9e214ae717c5ecbd6d13d5a2fb3142c71c1866c9ca537)...'
            )
            .expect('[OK]: all succeeds_with conditions hold')
            .expect('[OK]: all succeeds_with conditions hold')
            .expect('[OK]: all succeeds_with conditions hold')
            .expect('[OK]: all succeeds_with conditions hold')
            .wait(
                'Verifying claim (successful tx 0f3738d9fddc0a17a91b063e54113879d6da88818006144a9db908ed85c7163b)...'
            )
            .expect('[OK]: all succeeds_with conditions hold')
            .wait(
                'Verifying claim (failed tx 958fb84f272e53fed0cb9ab584770b344691b52dd843821dae47e782f2684ee8)...'
            )
            .expect('[OK]: tx reverted as expected by reverts_if conditions')
            .run(done)
    })

    it('reports error on `verify_js_example_xycloans.ts`', function (done) {
        this.timeout(50_000)
        spawn('node dist/test/e2e/verify_js_example_xycloans.js', {
            stream: 'all',
        })
            .wait(
                'Verifying deposit (successful tx 49ce70a0fe73f9b815f50dbe13403608242cec0770ac32eb24d1a425e39467be)...'
            )
            .expect('[OK]: all succeeds_with conditions hold')
            .wait(
                'Verifying deposit (successful tx af8d698431a4354bbe74517d741bbb278180eae2c6907ddc0abf5fcacd8b938b)...'
            )
            .expect('[OK]: all succeeds_with conditions hold')
            .wait(
                'Verifying borrow (successful tx 20a4726ab7291e00bfaad767a034844ffffd25f73882b5288da5486e3cc01973)...'
            )
            .expect('[OK]: all succeeds_with conditions hold')
            .wait(
                'Verifying update_fee_rewards (successful tx e5064617326554c02de8edd6628f1e1951903497698b3f1f5f0b00e03b2a16b6)...'
            )
            .expect('[Error]: some succeeds_with conditions do not hold')
            .run(done)
    })
})
