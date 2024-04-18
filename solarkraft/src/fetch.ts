/**
 * @license
 * [Apache-2.0](https://github.com/freespek/solarkraft/blob/main/LICENSE)
 */
/**
 * Fetch transactions from the ledger
 * @param args the arguments parsed by yargs
 */
export function fetch(args: any) {
    console.log(
        `*** WARNING: THIS IS A MOCK. NOTHING IS IMPLEMENTED YET. ***\n`
    )
    console.log(`Target contract: ${args.id}...`)
    console.log(`Fetching fresh transactions from: ${args.rpc}...`)
    // read the latest height cached from the latest invocation of fetch
    const cachedHeight = 1000
    // fetch the actual height from the RPC endpoint
    const currentHeight = 12345
    let startHeight =
        args.height < 0 ? currentHeight + args.height : args.height
    startHeight = Math.max(startHeight, cachedHeight)
    console.log(`| ledger | cached | start |`)
    console.log(`| ${currentHeight}  | ${cachedHeight}   | ${startHeight} |\n`)
    // fetch the transactions that involve that target contract
    console.log(
        `TX b6efc58ab03db82b5b2fa44b69ff89b64e54af5e6e5266dbdd70fc57d2dc583e at 51291021`
    )
    console.log(
        `TX d669f322d1011a3726301535f5451ef4398d40ad150b79845fb9a5fc781092cf at 51291024`
    )
    console.log(
        `TX cf96fc2bb266912f8063c6091a70a680498bbe41e71132814f765186926e4f80 at 51291018`
    )
}
