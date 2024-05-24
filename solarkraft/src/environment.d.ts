/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
declare global {
    namespace NodeJS {
        interface ProcessEnv {
            APALACHE_HOME: string
        }
    }
}

export {}
