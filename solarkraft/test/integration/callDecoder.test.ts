/**
 * Integration tests that ensure that our contract decoder works correctly on the testnet.
 *
 * First deploys a fresh copy of the setter contract (`ContractExamples/contracts/setter`)
 * on the testnet from its on-ledger WASM code hash. Then, each test calls a different
 * contract function and checks the decoded contract call entry.
 *
 * @author Igor Konnov, 2024
 * @author Thomas Pani, 2024
 */

import {
    Address,
    BASE_FEE,
    Contract,
    Horizon,
    Keypair,
    nativeToScVal,
    Networks,
    Operation,
    SorobanRpc,
    Transaction,
    TransactionBuilder,
    xdr,
} from '@stellar/stellar-sdk'
import { assert } from 'chai'
import { before, describe, it } from 'mocha'
import { extractContractCall } from '../../src/fetcher/callDecoder.js'
import { ContractCallEntry } from '../../src/fetcher/storage.js'
import { Maybe, none } from '@sweet-monads/maybe'

// Horizon and Soroban instances that we use for testing
const HORIZON_URL = 'https://horizon-testnet.stellar.org'
const SOROBAN_URL = 'https://soroban-testnet.stellar.org:443'

// hard-coded WASM code hash of the setter contract on the ledger (deployed via setter-populate.sh)
const WASM_HASH =
    '5218397dd64e5b5c2eead7e03f15a3ddb25c759fdf068d6f7dc8bffc8a033711'

// contract ID of the deployed setter contract (will be set up by `before()`)
let CONTRACT_ID: string

// a random keypair to sign transactions
const sourceKeypair = Keypair.random()

// 0xbeef
const beef = Buffer.from([0xbe, 0xef])

// 0xbeef0123456789beef0123456789beef0123456789ab
const bytes32 = Buffer.from([
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xbe, 0xef,
    0x01, 0x23, 0x45, 0x67, 0x89, 0xbe, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89,
    0xbe, 0xef, 0x01, 0x23, 0x45, 0x67, 0x89, 0xab,
])

// extract the only contract entry from a given ledger
async function extractEntry(txHash: string): Promise<ContractCallEntry> {
    const server = new Horizon.Server(HORIZON_URL)
    const operations = await server.operations().forTransaction(txHash).call()
    let resultingEntry: Maybe<ContractCallEntry> = none<ContractCallEntry>()
    for (const op of operations.records) {
        const entry = await extractContractCall(op, (id) => id === CONTRACT_ID)
        if (entry.isJust()) {
            assert(
                resultingEntry.isNone(),
                `found two call entries for contract ${CONTRACT_ID}, tx hash ${txHash}`
            )
            resultingEntry = entry
        }
    }

    if (resultingEntry.isJust()) {
        return resultingEntry.value
    } else {
        assert.fail(
            `expected non-empty call entry for contract ${CONTRACT_ID}, tx hash ${txHash}`
        )
    }
}

// submit a transaction; if successful, return its transaction hash and the response
async function submitTx(
    server: SorobanRpc.Server,
    tx: Transaction
): Promise<[string, SorobanRpc.Api.GetSuccessfulTransactionResponse]> {
    // Use the RPC server to "prepare" the transaction (simulate, update storage footprint)
    const preparedTransaction = await server.prepareTransaction(tx)

    // Sign the transaction with the source account's keypair
    preparedTransaction.sign(sourceKeypair)

    // Submit the transaction
    const sendResponse = await server.sendTransaction(preparedTransaction)

    // Poll for result and check for errors
    if (sendResponse.status === 'PENDING') {
        let getResponse = await server.getTransaction(sendResponse.hash)
        // Poll `getTransaction` until the status is not "NOT_FOUND"
        while (getResponse.status === 'NOT_FOUND') {
            getResponse = await server.getTransaction(sendResponse.hash)
            await new Promise((resolve) => setTimeout(resolve, 1000))
        }
        if (getResponse.status === 'SUCCESS') {
            if (!getResponse.resultMetaXdr) {
                throw 'Empty resultMetaXDR in getTransaction response'
            }
        } else {
            throw `Transaction failed: ${getResponse.resultXdr}`
        }
        return [sendResponse.hash, getResponse]
    } else {
        throw sendResponse.errorResult
    }
}

// Invoke contract function `functionName` with arguments `args` and return the transaction hash.
//
// `args` are converted to Soroban values using `nativeToScVal`.
async function callContract(
    functionName: string,
    ...args: xdr.ScVal[]
): Promise<string> {
    // adapted from https://developers.stellar.org/docs/learn/encyclopedia/contract-development/contract-interactions/stellar-transaction#function
    const server = new SorobanRpc.Server(SOROBAN_URL)

    // the deployed setter contract
    const contract = new Contract(CONTRACT_ID)

    // build the transaction
    const sourceAccount = await server.getAccount(sourceKeypair.publicKey())
    const builtTransaction = new TransactionBuilder(sourceAccount, {
        fee: BASE_FEE,
        networkPassphrase: Networks.TESTNET,
    })
        .addOperation(contract.call(functionName, ...args))
        .setTimeout(30) // tx is valid for 30 seconds
        .build()

    const [txHash] = await submitTx(server, builtTransaction)
    return txHash
}

describe('call decoder from Horizon', function () {
    // increase timeout to allow for populating the contract
    this.timeout(10_000)
    before(async function () {
        // Deploy a fresh setter contract from the WASM code `WASM_HASH`

        // This may take a bit; increase the timeout
        this.timeout(50_000)

        // Fund the keypair
        console.log(`Funding the keypair ${sourceKeypair.publicKey()} ...`)
        const horizon = new Horizon.Server(HORIZON_URL)
        await horizon.friendbot(sourceKeypair.publicKey()).call()

        // Redeploy a fresh copy of the setter contract WASM from CONTRACT_ID_TEMPLATE
        console.log(`Creating a contract from WASM code ${WASM_HASH} ...`)
        const soroban = new SorobanRpc.Server(SOROBAN_URL)
        const sourceAccount = await soroban.getAccount(
            sourceKeypair.publicKey()
        )
        const builtTransaction = new TransactionBuilder(sourceAccount, {
            fee: BASE_FEE,
            networkPassphrase: Networks.TESTNET,
        })
            .addOperation(
                Operation.createCustomContract({
                    address: Address.fromString(sourceKeypair.publicKey()),
                    wasmHash: Buffer.from(WASM_HASH, 'hex'),
                })
            )
            .setTimeout(30) // tx is valid for 30 seconds
            .build()

        const [txHash, response] = await submitTx(soroban, builtTransaction)
        CONTRACT_ID = Address.fromScAddress(
            response.resultMetaXdr.v3().sorobanMeta().returnValue().address()
        ).toString()
        console.log(
            `Fresh setter contract deployed by tx ${txHash} at ${CONTRACT_ID}`
        )
    })
    it('call #1: Setter.set_bool(true)', async function () {
        const txHash = await callContract('set_bool', nativeToScVal(true))
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_bool')
        assert.deepEqual(entry.methodArgs, [true])
        assert.deepEqual(entry.returnValue, false)
        assert.deepEqual(entry.oldFields.toArray(), [])
        assert.deepEqual(entry.fields.toArray(), [['MY_BOOL', true]])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: { instance: {}, temporary: {}, persistent: {} },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true },
                temporary: { MY_BOOL: true },
                persistent: { MY_BOOL: true },
            },
        })
    })

    it('call #2: Setter.set_u32([42u32])', async function () {
        const txHash = await callContract(
            'set_u32',
            nativeToScVal(42, { type: 'u32' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_u32')
        assert.deepEqual(entry.methodArgs, [42])
        assert.deepEqual(entry.returnValue, 0)
        assert.deepEqual(entry.oldFields.toArray(), [['MY_BOOL', true]])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_U32', 42],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42 },
                temporary: { MY_U32: 42 },
                persistent: { MY_U32: 42 },
            },
        })
    })

    it('call #3: Setter.set_i32([-42u32])', async function () {
        const txHash = await callContract(
            'set_i32',
            nativeToScVal(-42, { type: 'i32' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_i32')
        assert.deepEqual(entry.methodArgs, [-42])
        assert.deepEqual(entry.returnValue, 0)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_U32', 42],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42 },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42, MY_I32: -42 },
                temporary: { MY_I32: -42 },
                persistent: { MY_I32: -42 },
            },
        })
    })

    it('call #4: Setter.set_u64([42u64])', async function () {
        const txHash = await callContract(
            'set_u64',
            nativeToScVal(42, { type: 'u64' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_u64')
        assert.deepEqual(entry.methodArgs, [42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: { MY_BOOL: true, MY_U32: 42, MY_I32: -42 },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                },
                temporary: { MY_U64: 42n },
                persistent: { MY_U64: 42n },
            },
        })
    })

    it('call #5: Setter.set_i64([-42i64])', async () => {
        const txHash = await callContract(
            'set_i64',
            nativeToScVal(-42, { type: 'i64' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_i64')
        assert.deepEqual(entry.methodArgs, [-42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                },
                temporary: { MY_I64: -42n },
                persistent: { MY_I64: -42n },
            },
        })
    })

    it('call #6: Setter.set_u128([42u128])', async () => {
        const txHash = await callContract(
            'set_u128',
            nativeToScVal(42, { type: 'u128' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_u128')
        assert.deepEqual(entry.methodArgs, [42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                },
                temporary: { MY_U128: 42n },
                persistent: { MY_U128: 42n },
            },
        })
    })

    it('call #7: Setter.set_i128([-42i128])', async () => {
        const txHash = await callContract(
            'set_i128',
            nativeToScVal(-42, { type: 'i128' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_i128')
        assert.deepEqual(entry.methodArgs, [-42n])
        assert.deepEqual(entry.returnValue, 0n)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                },
                temporary: { MY_I128: -42n },
                persistent: { MY_I128: -42n },
            },
        })
    })

    it('call #8: Setter.set_sym("hello")', async () => {
        const txHash = await callContract(
            'set_sym',
            nativeToScVal('hello', { type: 'symbol' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_sym')
        assert.deepEqual(entry.methodArgs, ['hello'])
        assert.deepEqual(entry.returnValue, 'NONE')
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                },
                temporary: { MY_SYM: 'hello' },
                persistent: { MY_SYM: 'hello' },
            },
        })
    })

    it('call #9: Setter.set_bytes(0xbeef)', async () => {
        const txHash = await callContract('set_bytes', nativeToScVal(beef))
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_bytes')
        assert.deepEqual(entry.methodArgs, [beef])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                },
                temporary: { MY_BYTES: beef },
                persistent: { MY_BYTES: beef },
            },
        })
    })

    it('call #10: Setter.set_bytes32(...)', async () => {
        const txHash = await callContract('set_bytes32', nativeToScVal(bytes32))
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_bytes32')
        assert.deepEqual(entry.methodArgs, [bytes32])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                },
                temporary: { MY_BTES32: bytes32 },
                persistent: { MY_BTES32: bytes32 },
            },
        })
    })

    it('call #11: Setter.set_vec([[1i32, -2i32, 3i32]])', async () => {
        const txHash = await callContract(
            'set_vec',
            nativeToScVal([1, -2, 3], { type: 'i32' })
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_vec')
        assert.deepEqual(entry.methodArgs, [[1, -2, 3]])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                },
                temporary: { MY_VEC: [1, -2, 3] },
                persistent: { MY_VEC: [1, -2, 3] },
            },
        })
    })

    it('call #12: Setter.set_map([{2u32: 3i32, 4u32: 5i32}])', async () => {
        const txHash = await callContract(
            'set_map',
            nativeToScVal(
                { '2': 3, '4': 5 },
                { type: { '2': ['u32', 'i32'], '4': ['u32', 'i32'] } }
            )
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_map')
        assert.deepEqual(entry.methodArgs, [{ '2': 3, '4': 5 }])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: { MY_MAP: { '2': 3, '4': 5 } },
                persistent: { MY_MAP: { '2': 3, '4': 5 } },
            },
        })
    })

    it('call #13: Setter.set_address([GDIY...R4W4]', async () => {
        const txHash = await callContract(
            'set_address',
            nativeToScVal(
                Address.fromString(
                    'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4'
                )
            )
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_address')
        assert.deepEqual(entry.methodArgs, [
            'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
        ])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                },
                persistent: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                },
            },
        })
    })

    it('call #14: Setter.set_struct([{"a"sym: 1u32, "b"sym: -100i128}])', async () => {
        const txHash = await callContract(
            'set_struct',
            nativeToScVal(
                { a: 1, b: -100n },
                { type: { a: ['symbol', 'u32'], b: ['symbol', 'i128'] } }
            )
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_struct')
        assert.deepEqual(entry.methodArgs, [{ a: 1, b: -100n }])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: { MY_STRUCT: { a: 1, b: -100n } },
                persistent: { MY_STRUCT: { a: 1, b: -100n } },
            },
        })
    })

    it('call #15: Setter.set_enum([["B"sym, -200i128]])', async () => {
        const txHash = await callContract(
            'set_enum',
            xdr.ScVal.scvVec([
                xdr.ScVal.scvSymbol('B'),
                nativeToScVal(-200, { type: 'i128' }),
            ])
        )
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'set_enum')
        assert.deepEqual(entry.methodArgs, [['B', -200n]])
        assert.deepEqual(entry.returnValue, null)
        assert.deepEqual(entry.oldFields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_ENUM', ['B', -200n]],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_ENUM: ['B', -200n],
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: { MY_ENUM: ['B', -200n] },
                persistent: { MY_ENUM: ['B', -200n] },
            },
        })
    })

    it('call #16: Setter.remove_bool()', async () => {
        const txHash = await callContract('remove_bool')
        const entry = await extractEntry(txHash)
        assert.isDefined(entry.timestamp)
        assert.isDefined(entry.height)
        assert.equal(entry.contractId, CONTRACT_ID)
        assert.isDefined(entry.txHash)
        assert.equal(entry.method, 'remove_bool')
        assert.deepEqual(entry.methodArgs, [])
        assert.deepEqual(entry.returnValue, true)
        assert.deepEqual(entry.oldFields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BOOL', true],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_ENUM', ['B', -200n]],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.fields.toArray(), [
            [
                'MY_ADDR',
                'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
            ],
            ['MY_BTES32', bytes32],
            ['MY_BYTES', beef],
            ['MY_ENUM', ['B', -200n]],
            ['MY_I128', -42n],
            ['MY_I32', -42],
            ['MY_I64', -42n],
            ['MY_MAP', { '2': 3, '4': 5 }],
            ['MY_STRUCT', { a: 1, b: -100n }],
            ['MY_SYM', 'hello'],
            ['MY_U128', 42n],
            ['MY_U32', 42],
            ['MY_U64', 42n],
            ['MY_VEC', [1, -2, 3]],
        ])
        assert.deepEqual(entry.oldStorage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_BOOL: true,
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_ENUM: ['B', -200n],
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: { MY_BOOL: true },
                persistent: { MY_BOOL: true },
            },
        })
        assert.deepEqual(entry.storage.toJS(), {
            [CONTRACT_ID]: {
                instance: {
                    MY_ADDR:
                        'GDIY6AQQ75WMD4W46EYB7O6UYMHOCGQHLAQGQTKHDX4J2DYQCHVCR4W4',
                    MY_U32: 42,
                    MY_I32: -42,
                    MY_U64: 42n,
                    MY_I64: -42n,
                    MY_U128: 42n,
                    MY_I128: -42n,
                    MY_ENUM: ['B', -200n],
                    MY_STRUCT: { a: 1, b: -100n },
                    MY_SYM: 'hello',
                    MY_BYTES: beef,
                    MY_BTES32: bytes32,
                    MY_VEC: [1, -2, 3],
                    MY_MAP: { '2': 3, '4': 5 },
                },
                temporary: {},
                persistent: {},
            },
        })
    })
})
