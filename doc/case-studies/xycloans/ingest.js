#!/usr/bin/env node
/**
 * Ingest a counterexample produced by Apalache and produce the corresponding
 * command for stellar-cli.
 *
 * In this case study, we write the script manually.  In the future, this could
 * be automated. Alternatively, we could execute the counterexample with
 * js-stellar-sdk. However, we believe that the command line interface offers us
 * more flexibility.
 *
 * Igor Konnov, 2024
 */

const fs = require('fs')
const assert = require('assert')
const { execSync } = require('child_process')

network = 'testnet'

// Since stellar-cli does not let us sign a transaction by supplying a public key,
// we have to extract account ids. Shall we add a command to solarkraft?
function readOrFindAccounts() {
    const accountsFile = 'accounts.json'
    if (!fs.existsSync(accountsFile)) {
        execSync('solarkraft accounts')
    }
    try {
        return JSON.parse(fs.readFileSync(accountsFile, 'utf8'))
    } catch (err) {
        console.error(`Error reading ${accountsFile}: ${err.message}`)
        process.exit(1)
    }
}

// check that we have at least two arguments
const args = process.argv.slice(2)
if (args.length < 2) {
  console.log('Usage: ingest.js state.json trace.json')
  console.log('  state.json is the aggregated state, as produced by solarkraft aggregate')
  console.log('  trace.json is the ITF trace, as produced by Apalache')
  process.exit(1)
}

// read the state and the trace from the JSON files
let state
let trace
try {
    state = JSON.parse(fs.readFileSync(args[0], 'utf8'))
    trace = JSON.parse(fs.readFileSync(args[1], 'utf8'))
} catch (err) {
    console.error(`Error reading the input files: ${err.message}`)
    process.exit(1)
}

const call = trace.states[1].last_tx.call
const callType = call.tag
assert(callType !== undefined, 'traces.states[1].last_tx.call.tag is undefined')

const accounts = readOrFindAccounts()

// produce the arguments for the xycloans transaction
let signer
let callArgs
switch (callType) {
    case 'Deposit': {
        signer = accounts[call.value.from]
        const amount = call.value.amount["#bigint"]
        callArgs = `deposit --from ${call.value.from} --amount ${amount}`
        break
    }

    case 'Borrow': {
        signer = accounts[call.value.receiver_id]
        const amount = call.value.amount["#bigint"]
        callArgs = `borrow --receiver_id ${call.value.receiver_id} --amount ${amount}`
        break
    }

    case 'UpdateFeeRewards':
        signer = accounts[call.value.addr]
        callArgs = `update_fee_rewards --addr ${signer}`
        break

    case 'WithdrawMatured':
        signer = accounts[call.value.addr]
        callArgs = `withdraw_matured --addr ${signer}`
        break

    case 'Withdraw':
        signer = accounts[call.value.addr]
        const amount = call.value.amount["#bigint"]
        callArgs = `withdraw --addr ${signer} --amount ${amount}`
        break

    default:
        console.error(`Unknown call type: ${callType}`)
        process.exit(1)
}

assert(signer !== undefined, 'signer is undefined')

// produce the command for stellar-cli
const cmd =
    `stellar contract invoke --id ${state.contractId} --source ${signer} --network ${network} -- ${callArgs}`
console.log(cmd)