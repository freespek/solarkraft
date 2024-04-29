// an example unit test to copy from

import { assert } from 'chai'
import { describe, it } from 'mocha'

import { instrumentMonitor } from '../../src/verify.js'

describe('verify command', () => {
    it('instruments TLA+ monitors', () => {
        const monitor = { modules: [{ declarations: [] }] }
        const state = [
            { name: 'is_initialized', type: 'TlaBool', value: false },
        ]
        const tx = {
            functionName: 'Claim',
            functionArgs: [{ type: 'TlaStr', value: 'alice' }],
            env: { timestamp: 100 },
            error: 'contract is not initialized',
        }

        const instrumented = instrumentMonitor(monitor, state, tx)
        const expected = {
            modules: [
                {
                    declarations: [
                        {
                            kind: 'TlaOperDecl',
                            name: 'Init',
                            type: 'Untyped',
                            formalParams: [],
                            isRecursive: false,
                            body: {
                                kind: 'OperEx',
                                oper: 'AND',
                                type: 'Untyped',
                                args: [
                                    {
                                        kind: 'OperEx',
                                        oper: 'EQ',
                                        type: 'Untyped',
                                        args: [
                                            {
                                                kind: 'NameEx',
                                                name: 'is_initialized',
                                                type: 'Untyped',
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaBool',
                                                    value: false,
                                                },
                                            },
                                        ],
                                    },
                                    {
                                        kind: 'OperEx',
                                        oper: 'EQ',
                                        type: 'Untyped',
                                        args: [
                                            {
                                                kind: 'NameEx',
                                                name: 'last_error',
                                                type: 'Untyped',
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: '',
                                                },
                                            },
                                        ],
                                    },
                                ],
                            },
                        },
                        {
                            kind: 'TlaOperDecl',
                            name: 'Next',
                            type: 'Untyped',
                            formalParams: [],
                            isRecursive: false,
                            body: {
                                kind: 'OperEx',
                                oper: 'AND',
                                type: 'Untyped',
                                args: [
                                    {
                                        kind: 'OperEx',
                                        oper: 'OPER_APP',
                                        type: 'Untyped',
                                        args: [
                                            {
                                                kind: 'NameEx',
                                                name: 'Claim',
                                                type: 'Untyped',
                                            },
                                            {
                                                kind: 'OperEx',
                                                oper: 'RECORD',
                                                type: 'Untyped',
                                                args: [
                                                    {
                                                        kind: 'ValEx',
                                                        type: 'Untyped',
                                                        value: {
                                                            kind: 'TlaStr',
                                                            value: 'timestamp',
                                                        },
                                                    },
                                                    {
                                                        kind: 'ValEx',
                                                        type: 'Untyped',
                                                        value: {
                                                            kind: 'TlaInt',
                                                            value: 100,
                                                        },
                                                    },
                                                ],
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: 'alice',
                                                },
                                            },
                                        ],
                                    },
                                    {
                                        kind: 'OperEx',
                                        oper: 'EQ',
                                        type: 'Untyped',
                                        args: [
                                            {
                                                kind: 'OperEx',
                                                oper: 'PRIME',
                                                type: 'Untyped',
                                                args: [
                                                    {
                                                        kind: 'NameEx',
                                                        name: 'last_error',
                                                        type: 'Untyped',
                                                    },
                                                ],
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: 'contract is not initialized',
                                                },
                                            },
                                        ],
                                    },
                                ],
                            },
                        },
                    ],
                },
            ],
        }
        assert.deepEqual(instrumented, expected)
    })
})
