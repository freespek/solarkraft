/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Extract the mapping of accounts' public keys to their identities.
 * We need this function, as `stellar contract invoke` requires an account id.
 *
 * Igor Konnov, 2024
 */

import { execSync } from 'child_process'
import { writeFileSync } from 'fs'

export function extractAccounts(args: any) {
    const result = execSync('stellar keys ls')
    const ids = result.toString().trim().split('\n')
    const accounts = ids.reduce((obj, id) => {
        const key = execSync(`stellar keys address ${id}`).toString().trim()
        return { ...obj, [key]: id }
    }, {})
    writeFileSync(args.out, JSON.stringify(accounts, null, 2))
}
