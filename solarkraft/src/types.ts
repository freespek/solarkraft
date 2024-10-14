/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Types shared across the project
 */
import { Either } from '@sweet-monads/either'

export type Result<T> = Either<string, T>
