/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Definitions shared across the project
 */

import { Either } from '@sweet-monads/either'
import { homedir } from 'node:os'
import { join } from 'node:path'

// A result type
export type Result<T> = Either<string, T>

// The default home directory for Solarkraft
export const SOLARKRAFT_DEFAULT_HOME = join(homedir(), '.solarkraft')

// JSONbigint for writing/parsing JSON with big integers
import JSONbigint from 'json-bigint'
export const JSONbig = JSONbigint({
    useNativeBigInt: true,
    alwaysParseAsBig: true,
})
