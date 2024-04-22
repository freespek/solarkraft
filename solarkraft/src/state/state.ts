/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
import { OrderedMap } from 'immutable'
import { Value } from './value.js'

export type State = OrderedMap<string, Value>
