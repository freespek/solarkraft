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

// The default options present in every command
const defaultOpts = (yargs: any) =>
    yargs.option('color', {
        desc: 'color output',
        type: 'boolean',
        default: true,
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
                default: '123',
            })
            .option('rpc', {
                desc: 'URL of the Stellar RPC',
                type: 'string',
                default: 'http://localhost:8000',
            })
            .option('height', {
                desc: 'The height to start with (a negative value -n goes from the latest block - n)',
                type: 'number',
                default: -10,
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
                desc: 'Monitor to check against',
                type: 'string',
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
    builder: (yargs: any) => defaultOpts(yargs),
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
