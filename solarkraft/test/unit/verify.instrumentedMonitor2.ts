const instrumentedMonitor = {
    modules: [
        {
            declarations: [
                {
                    kind: 'TlaVarDecl',
                    name: 'is_initialized',
                },
                {
                    kind: 'TlaVarDecl',
                    name: 'absent',
                },
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
                                ],
                            },
                            {
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
                                                name: 'absent',
                                                type: 'Untyped',
                                            },
                                            {
                                                kind: 'OperEx',
                                                oper: 'Apalache!Gen',
                                                type: 'Untyped',
                                                args: [
                                                    {
                                                        kind: 'ValEx',
                                                        type: 'Untyped',
                                                        value: {
                                                            kind: 'TlaInt',
                                                            value: 1,
                                                        },
                                                    },
                                                ],
                                            },
                                        ],
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
                                                    value: 'sequence',
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
                                                    value: 1716393856,
                                                },
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: 'current_contract_address',
                                                },
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: '0xqwer',
                                                },
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: 'invoked_function_name',
                                                },
                                            },
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: 'Claim',
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
                                oper: 'AND',
                                type: 'Untyped',
                                args: [
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
                                                        name: 'is_initialized',
                                                        type: 'Untyped',
                                                    },
                                                ],
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
                                ],
                            },
                            {
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
                                                kind: 'OperEx',
                                                oper: 'PRIME',
                                                type: 'Untyped',
                                                args: [
                                                    {
                                                        kind: 'NameEx',
                                                        name: 'absent',
                                                        type: 'Untyped',
                                                    },
                                                ],
                                            },
                                            {
                                                kind: 'OperEx',
                                                oper: 'Apalache!Gen',
                                                type: 'Untyped',
                                                args: [
                                                    {
                                                        kind: 'ValEx',
                                                        type: 'Untyped',
                                                        value: {
                                                            kind: 'TlaInt',
                                                            value: 1,
                                                        },
                                                    },
                                                ],
                                            },
                                        ],
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

export { instrumentedMonitor }
