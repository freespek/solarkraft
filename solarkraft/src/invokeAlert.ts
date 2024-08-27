import {
    Contract,
    SorobanRpc,
    TransactionBuilder,
    Networks,
    BASE_FEE,
    xdr,
    Keypair,
    scValToNative,
} from '@stellar/stellar-sdk'
import { Api } from '@stellar/stellar-sdk/rpc'
import { VerificationStatus } from './fetcher/storage.js'

/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

const AlertMethodName = 'emit_and_store_violation'

/**
 * When we have obtained a `VerificationStatus` for a given monitor, we can submit it to the
 * alert contract via the Soroban rpc.
 *
 * adapted from https://developers.stellar.org/docs/learn/smart-contract-internals/contract-interactions/stellar-transaction
 */
export async function invokeAlert(
    sorobanRpcServer: string,
    sourceKeypair: Keypair,
    networkType: Networks,
    alertContractId: string,
    txHash: string,
    verificationStatus: VerificationStatus
): Promise<VerificationStatus> {
    const alertContract = new Contract(alertContractId)
    const server = new SorobanRpc.Server(sorobanRpcServer)

    // We have to build the method params from the JS ones
    const txHashAsScVal = xdr.ScVal.scvString(txHash)
    // Enums are equivalent to their u32 values
    const verificationStatusAsScVal = xdr.ScVal.scvU32(verificationStatus)

    const sourceAccount = await server.getAccount(sourceKeypair.publicKey())

    const builtTransaction = new TransactionBuilder(sourceAccount, {
        fee: BASE_FEE,
        networkPassphrase: networkType,
    })
        .addOperation(
            alertContract.call(
                AlertMethodName,
                txHashAsScVal,
                verificationStatusAsScVal
            )
        )
        // This transaction will be valid for the next 30 seconds
        .setTimeout(30)
        .build()

    // We use the RPC server to "prepare" the transaction. This simulating the
    // transaction, discovering the storage footprint, and updating the
    // transaction to include that footprint. If you know the footprint ahead of
    // time, you could manually use `addFootprint` and skip this step.
    const preparedTransaction =
        await server.prepareTransaction(builtTransaction)

    // Sign the transaction with the source account's keypair.
    preparedTransaction.sign(sourceKeypair)

    console.log(
        `Signed prepared transaction for alert contract ${alertContractId}`
    )

    // Submit the transaction to the Soroban-RPC server. The RPC server will
    // then submit the transaction into the network for us. Then we will have to
    // wait, polling `getTransaction` until the transaction completes.
    try {
        const sendResponse = await server.sendTransaction(preparedTransaction)

        if (sendResponse.status === 'PENDING') {
            let getResponse = await server.getTransaction(sendResponse.hash)
            // Poll `getTransaction` until the status is not "NOT_FOUND"
            while (getResponse.status === Api.GetTransactionStatus.NOT_FOUND) {
                // See if the transaction is complete
                getResponse = await server.getTransaction(sendResponse.hash)
                // Wait one second
                await new Promise((resolve) => setTimeout(resolve, 1000))
            }

            if (getResponse.status === Api.GetTransactionStatus.SUCCESS) {
                // Find the return value from the contract and return it
                const returnValue = getResponse.returnValue
                console.log(`Transaction successful`)

                return scValToNative(returnValue) as VerificationStatus
            } else {
                throw `Transaction failed: ${getResponse.resultXdr}`
            }
        } else {
            throw sendResponse.errorResult
        }
    } catch (err) {
        // Catch and report any errors we've thrown
        console.log('Sending transaction failed')
        console.log(JSON.stringify(err))

        return VerificationStatus.Unknown
    }
}
