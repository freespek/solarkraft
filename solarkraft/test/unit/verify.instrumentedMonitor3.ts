const instrumentedMonitor = {
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
                                oper: 'AND',
                                type: 'Untyped',
                                args: [],
                            },
                            {
                                kind: 'OperEx',
                                oper: 'AND',
                                type: 'Untyped',
                                args: [],
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
                                        name: 'foo',
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
                                                    value: 'height',
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
                                        ],
                                    },
                                    {
                                        type: 'Untyped',
                                        kind: 'OperEx',
                                        oper: 'Variants!Variant',
                                        args: [
                                            {
                                                type: 'Untyped',
                                                kind: 'OperEx',
                                                oper: 'OPER_APP',
                                                args: [
                                                    {
                                                        kind: 'NameEx',
                                                        type: 'Untyped',
                                                        name: 'MaybeEnum',
                                                    },
                                                ],
                                            },
                                            {
                                                type: 'Untyped',
                                                kind: 'OperEx',
                                                oper: 'OPER_APP',
                                                args: [
                                                    {
                                                        type: 'Untyped',
                                                        kind: 'NameEx',
                                                        name: 'UNIT',
                                                    },
                                                ],
                                            },
                                        ],
                                    },
                                    {
                                        type: 'Untyped',
                                        kind: 'OperEx',
                                        oper: 'TUPLE',
                                        args: [
                                            {
                                                kind: 'ValEx',
                                                type: 'Untyped',
                                                value: {
                                                    kind: 'TlaStr',
                                                    value: 'MaybeVec',
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
                                args: [],
                            },
                            {
                                kind: 'OperEx',
                                oper: 'AND',
                                type: 'Untyped',
                                args: [],
                            },
                        ],
                    },
                },
            ],
        },
    ],
}

export { instrumentedMonitor }
