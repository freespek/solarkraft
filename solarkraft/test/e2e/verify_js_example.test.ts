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
})
