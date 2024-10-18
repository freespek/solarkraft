/**
 * Unit tests for the JavaScript / TypeScript monitoring library.
 *
 * @author Thomas Pani, 2024
 */

import { assert } from 'chai'
import { describe, it } from 'mocha'
import { Map } from 'immutable'
import {
    some,
    every,
    evaluateCondition,
    Env,
    tokenTransferred,
} from '../../src/verify_js.js'

describe('JavaScript/TypeScript monitor', () => {
    describe('conditions', () => {
        describe('some', () => {
            it('returns true if at least one condition is true', () => {
                const condition = some(true, false, false)
                assert.isTrue(evaluateCondition(condition))
            })

            it('returns false if all conditions are false', () => {
                const condition = some(false, false, false)
                assert.isFalse(evaluateCondition(condition))
            })

            it('returns true if all conditions are true', () => {
                const condition = some(true, true, true)
                assert.isTrue(evaluateCondition(condition))
            })

            it('handles nested conditions correctly', () => {
                const condition = some(false, some(true, true), false)
                assert.isTrue(evaluateCondition(condition))
            })
        })

        describe('every', () => {
            it('returns true if all conditions are true', () => {
                const condition = every(true, true, true)
                assert.isTrue(evaluateCondition(condition))
            })

            it('returns false if at least one condition is false', () => {
                const condition = every(true, false, true)
                assert.isFalse(evaluateCondition(condition))
            })

            it('returns false if all conditions are false', () => {
                const condition = every(false, false, false)
                assert.isFalse(evaluateCondition(condition))
            })

            it('handles nested conditions correctly', () => {
                const condition = every(true, every(true, true), true)
                assert.isTrue(evaluateCondition(condition))
            })
        })
    })

    /* eslint-disable @typescript-eslint/no-unused-vars */
    describe('tokenTransferred', () => {
        it('returns true if the token amount has been transferred correctly', () => {
            const env = {
                oldStorage: (_tokenAddr: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, 100],
                            [`Balance,toAddress`, 50],
                        ]),
                }),
                storage: (_tokenAddr: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, 90],
                            [`Balance,toAddress`, 60],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10
            )
            assert.isTrue(evaluateCondition(condition))
        })

        it('returns false if the token amount has not been transferred correctly', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, 100],
                            [`Balance,toAddress`, 50],
                        ]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, 95],
                            [`Balance,toAddress`, 55],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10
            )
            assert.isFalse(evaluateCondition(condition))
        })

        it('handles cases where the recipient had no prior balance', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () => Map([[`Balance,fromAddress`, 100]]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, 90],
                            [`Balance,toAddress`, 10],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10
            )
            assert.isTrue(evaluateCondition(condition))
        })

        it('returns false if the sender had no prior balance', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () => Map([[`Balance,toAddress`, 50]]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, -10],
                            [`Balance,toAddress`, 60],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10
            )
            assert.isFalse(evaluateCondition(condition))
        })
    })
})
