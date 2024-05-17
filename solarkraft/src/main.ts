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
import { join } from 'node:path'
import { homedir } from 'node:os'

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
            default: join(homedir(), '.solarkraft'),
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
            .option('rpc', {
                desc: 'URL of a Horizon endpoint',
                type: 'string',
                default: 'https://horizon-testnet.stellar.org',
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
            .option('state', {
                // TODO(#38): read state from fetcher output
                desc: 'ITF file encoding ledger state',
                type: 'string',
                demandOption: true,
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

function main() {
    return yargs(process.argv.slice(2))
        .command(fetchCmd)
        .command(verifyCmd)
        .command(listCmd)
        .demandCommand(1)
        .version(version)
        .strict()
        .parse()
}

main()
