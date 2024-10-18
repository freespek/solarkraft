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

export type Result<T> = Either<string, T>

export const SOLARKRAFT_DEFAULT_HOME = join(homedir(), '.solarkraft')
