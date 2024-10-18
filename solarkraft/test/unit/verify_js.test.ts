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
    tokenReceived,
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
    describe('tokenReceived', () => {
        it('returns true if the token amount has been received correctly', () => {
            const env = {
                oldStorage: (_tokenAddr: string) => ({
                    persistent: () =>
                        Map([[`Balance,toAddress`, { amount: 50n }]]),
                }),
                storage: (_tokenAddr: string) => ({
                    persistent: () =>
                        Map([[`Balance,toAddress`, { amount: 60n }]]),
                }),
            } as unknown as Env

            const condition = tokenReceived(env, 'token', 'toAddress', 10n)
            assert.isTrue(evaluateCondition(condition))
        })

        it('returns false if the token amount has not been received correctly', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () =>
                        Map([[`Balance,toAddress`, { amount: 50n }]]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([[`Balance,toAddress`, { amount: 55n }]]),
                }),
            } as unknown as Env

            const condition = tokenReceived(env, 'token', 'toAddress', 10n)
            assert.isFalse(evaluateCondition(condition))
        })

        it('handles cases where the recipient had no prior balance', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () => Map([]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([[`Balance,toAddress`, { amount: 10n }]]),
                }),
            } as unknown as Env

            const condition = tokenReceived(env, 'token', 'toAddress', 10n)
            assert.isTrue(evaluateCondition(condition))
        })

        it('returns false if the recipient had no prior balance and received incorrect amount', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () => Map([]),
                }),
                storage: (_token: string) => ({
                    persistent: () => Map([[`Balance,toAddress`, 5n]]),
                }),
            } as unknown as Env

            const condition = tokenReceived(env, 'token', 'toAddress', 10n)
            assert.isFalse(evaluateCondition(condition))
        })
    })

    /* eslint-disable @typescript-eslint/no-unused-vars */
    describe('tokenTransferred', () => {
        it('returns true if the token amount has been transferred correctly', () => {
            const env = {
                oldStorage: (_tokenAddr: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, { amount: 100n }],
                            [`Balance,toAddress`, { amount: 50n }],
                        ]),
                }),
                storage: (_tokenAddr: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, { amount: 90n }],
                            [`Balance,toAddress`, { amount: 60n }],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10n
            )
            assert.isTrue(evaluateCondition(condition))
        })

        it('returns false if the token amount has not been transferred correctly', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, { amount: 100n }],
                            [`Balance,toAddress`, { amount: 50n }],
                        ]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, { amount: 95n }],
                            [`Balance,toAddress`, { amount: 55n }],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10n
            )
            assert.isFalse(evaluateCondition(condition))
        })

        it('handles cases where the recipient had no prior balance', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () =>
                        Map([[`Balance,fromAddress`, { amount: 100n }]]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, { amount: 90n }],
                            [`Balance,toAddress`, { amount: 10n }],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10n
            )
            assert.isTrue(evaluateCondition(condition))
        })

        it('returns false if the sender had no prior balance', () => {
            const env = {
                oldStorage: (_token: string) => ({
                    persistent: () =>
                        Map([[`Balance,toAddress`, { amount: 50n }]]),
                }),
                storage: (_token: string) => ({
                    persistent: () =>
                        Map([
                            [`Balance,fromAddress`, { amount: -10n }],
                            [`Balance,toAddress`, { amount: 60n }],
                        ]),
                }),
            } as unknown as Env

            const condition = tokenTransferred(
                env,
                'token',
                'fromAddress',
                'toAddress',
                10n
            )
            assert.isFalse(evaluateCondition(condition))
        })
    })
})
