/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

/**
 * List the transactions in the storage.
 *
 * Igor Konnov, 2024.
 */

import { existsSync, readdirSync } from 'fs'
import { storagePath, yieldListEntriesForContract } from './fetcher/storage.js'
import { join } from 'node:path'

// the length of a contract id in its string representation
const CONTRACT_ID_LENGTH = 56

/**
 * List the transactions fetched from the ledger.
 */
export function list(args: any) {
    // Read from the file system directly.
    // In the future versions, we may want to introduce an abstraction in fetcher/storage.ts.
    const storageRoot = storagePath(args.home)
    if (!existsSync(storageRoot)) {
        console.log(`The storage is empty. Run 'solarkraft fetch'`)
        return
    }

    readdirSync(storageRoot, { withFileTypes: true }).map((dirent) => {
        if (dirent.isDirectory() && dirent.name.length === CONTRACT_ID_LENGTH) {
            // this is a storage directory for a contract
            if (args.id === '' || dirent.name === args.id) {
                console.log(`Contract ${dirent.name}:`)
                console.log('')

                for (const e of yieldListEntriesForContract(
                    dirent.name,
                    join(storageRoot, dirent.name)
                )) {
                    console.log(`  [${e.verificationStatus}]`)
                    console.log(`    height: ${e.height}`)
                    console.log(`    tx: ${e.txHash}`)
                    console.log('')
                }
            }
        }
    })
}
