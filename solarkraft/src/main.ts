#!/usr/bin/env node

/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

import yargs from 'yargs'
import { version } from './version.js'
import { fetch } from './fetch.js'
import { verify } from './verify.js'
import { list } from './list.js'
import { SOLARKRAFT_DEFAULT_HOME } from './globals.js'
import { aggregate } from './aggregate.js'
import { extractAccounts } from './accounts.js'

// The default options present in every command
const defaultOpts = (yargs: any) =>
    yargs
        .option('color', {
            desc: 'color output',
            type: 'boolean',
            default: true,
        })
        .option('home', {
            desc: 'Solarkraft home directory (or project directory)',
            type: 'string',
            default: SOLARKRAFT_DEFAULT_HOME,
        })

// fetch: transaction extractor
const fetchCmd = {
    command: ['fetch'],
    desc: 'fetch Soroban transactions from Stellar',
    builder: (yargs: any) =>
        defaultOpts(yargs)
            .option('id', {
                desc: 'Contract id',
                type: 'string',
                require: true,
            })
            .option('typemap', {
                desc: 'File containing contract method type annotations',
                type: 'string',
                require: false,
            })
            .option('horizon', {
                desc: 'URL of a Horizon endpoint',
                type: 'string',
                default: 'https://horizon-testnet.stellar.org',
            })
            .option('rpc', {
                desc: 'URL of a Soroban RPC endpoint',
                type: 'string',
                default: 'https://soroban-testnet.stellar.org',
            })
            .option('height', {
                desc: 'The height to start with (a negative value -n goes from the latest block - n)',
                type: 'number',
                default: -10,
            })
            .option('timeout', {
                desc: 'Fetcher timeout in seconds (when 0, fetch indefinitely long)',
                type: 'number',
                default: 0,
            }),
    handler: fetch,
}

// aggregate: state aggregator
const aggregateCmd = {
    command: ['aggregate'],
    desc: 'aggregate the fetched Soroban transactions to compute the full contract state',
    builder: (yargs: any) =>
        defaultOpts(yargs)
            .option('id', {
                desc: 'Contract id',
                type: 'string',
                require: true,
            })
            .option('out', {
                desc: 'The name of the file to output the state',
                type: 'string',
                require: false,
                default: 'state.json',
            })
            .option('heightTo', {
                desc: 'The maximum height (ledger) to aggregate up to',
                type: 'number',
                require: false,
                default: Infinity,
            })
            .option('verbose', {
                desc: 'Print verbose output',
                type: 'string',
                require: false,
                default: false,
            }),
    handler: aggregate,
}

// verify: transaction verifier
const verifyCmd = {
    command: ['verify'],
    desc: 'verify a previously fetched transaction',
    builder: (yargs: any) =>
        defaultOpts(yargs)
            .option('txHash', {
                desc: 'Transaction hash',
                type: 'string',
                demandOption: true,
            })
            .option('monitor', {
                desc: 'Monitors to check against',
                type: 'array',
                demandOption: true,
            })
            .option('alert', {
                desc: 'Alert contract ID. Will not alert if this parameter is not provided.',
                type: 'string',
                require: false,
            }),
    handler: verify,
}

// list: show the fetched and verified transactions
const listCmd = {
    command: ['list'],
    desc: 'list the fetched and verified transactions',
    builder: (yargs: any) =>
        defaultOpts(yargs).option('id', {
            desc: 'Contract id',
            type: 'string',
            default: '',
            require: false,
        }),
    handler: list,
}

// accounts: construct an accounts mapping
const accountsCmd = {
    command: ['accounts'],
    desc: 'construct an accounts mapping, needed for input generation',
    builder: (yargs: any) =>
        defaultOpts(yargs)
            .option('out', {
                desc: 'The name of the file to output the accounts mapping to',
                type: 'string',
                require: false,
                default: 'accounts.json',
            }),
    handler: extractAccounts,
}

function main() {
    return yargs(process.argv.slice(2))
        .command(fetchCmd)
        .command(aggregateCmd)
        .command(verifyCmd)
        .command(listCmd)
        .command(accountsCmd)
        .demandCommand(1)
        .version(version)
        .strict()
        .parse()
}

main()
