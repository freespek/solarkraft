#!/usr/bin/env node
/**
 * Injest a counterexample produced by Apalache and produce the corresponding
 * command for stellar-cli.
 *
 * In this case study, we write the script manually.  In the future, this could
 * be automated. Alternatively, we could execute the counterexample with
 * stellar-sdk. However, we believe that the command line interface offers us
 * more flexibility.
 *
 * Igor Konnov, 2024
 */

const fs = require('fs')
const assert = require('assert')

network = 'testnet'

// check that we have at least two arguments
const args = process.argv.slice(2)
if (args.length < 2) {
  console.log('Usage: ingest.js state.json trace.json')
  console.log('  state.json is the aggregated state, as produced by solarkraft aggregate')
  console.log('  trace.json is the ITF trace, as produced by Apalache')
  process.exit(1)
}

// read the state and the trace from the JSON files
const state = JSON.parse(fs.readFileSync(args[0], 'utf8'))
const trace = JSON.parse(fs.readFileSync(args[1], 'utf8'))

const call = trace.states[1].last_tx.call
const callType = call.tag
assert(callType !== undefined, 'traces.states[1].last_tx.call.tag is undefined')

// produce the arguments for the xycloans transaction
let signer
let callArgs
switch (callType) {
    case 'Deposit': {
        signer = call.value.from
        const amount = call.value.amount["#bigint"]
        callArgs = `deposit --from ${call.value.from} --amount ${amount}`
        break
    }

    case 'Borrow': {
        signer = call.value.receiver_id
        const amount = call.value.amount["#bigint"]
        callArgs = `borrow --receiver_id ${call.value.receiver_id} --amount ${amount}`
        break
    }

    case 'UpdateFeeRewards':
        signer = call.value.addr
        callArgs = `deposit --addr ${signer}`
        break

    default:
        console.error(`Unknown call type: ${callType}`)
        process.exit(1)
}

// produce the command for stellar-cli
const cmd =
    `stellar contract invoke --id ${state.contractId} --source ${signer} --network ${network} -- ${callArgs}`
console.log(cmd)