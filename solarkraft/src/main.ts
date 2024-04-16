#!/usr/bin/env node

/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */

import yargs from 'yargs'
import { version } from './version.js'

// The default options present in every command
const defaultOpts = (yargs: any) =>
    yargs.option('color', {
      desc: 'color output',
      type: 'boolean',
      default: true,
    })

// transaction extractor
const txExtractorCmd = {
    command: ['txs'],
    desc: 'extract transactions',
    builder: (yargs: any) =>
      defaultOpts(yargs)
        .option('id', {
          desc: 'Contract id',
          type: 'string',
          default: '123',
        }),
    handler: onTxExtractor,
}

// call the transaction extractor here
function onTxExtractor (args: any) {
    console.log(`Mock TX Extractor(id: ${args.id})`)
}

function main() {
    return yargs(process.argv.slice(2))
        .command(txExtractorCmd)
        .demandCommand(1)
        .version(version)
        .strict()
        .parse()
}

main()
