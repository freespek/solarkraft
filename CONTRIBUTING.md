# Contributing

This page documents our development process.

## 1. Project layout

 - [solarkraft](./solarkraft/) contains the source code of the Solarkraft package
 - [ContractExamples](./ContractExamples/) contains Soroban smart contracts that we use for testing
 - [doc](./doc/) contains general documentation
 - [assets](./assets/) contains project assets such as the project logo

## 2. Solarkraft dev environment

Solarkraft is written in [TypeScript][]. It uses the standard development tooling:

 - [npm][] is the package manager
 - [tsc][] is the TypeScript compiler
 - [NodeJS][] is the runtime environment
 - [MochaJS][] and [ChaiJS][] are the testing framework
 - [eslint][] is the code linter
 - [prettier][] is the code formatter
 - [husky] is the hook manager that runs basic tests on git commits

## 3. Basic development commands

1. On the first run, install the required npm packages:

   ```sh
   npm i
   ```

1. Compile the project:

   ```sh
   npm run compile
   ```

1. Run the unit tests:

   ```sh
   npm run test
   ```

1. Install a local version (once):

   ```sh
   npm link
   ```

1. Run the command-line interface:

   ```sh
   solarkraft
   ```

## 4. Deployment

We are still discovering an optimal setup. The Soroban instructions are given in
[#10](https://github.com/freespek/solarkraft/pull/10). Further, Soroban does not
seem to build well on MacOS, owing to [this
issue](https://discord.com/channels/1179099813879492721/1196869246429429960/1229764850591469649).

To work around the above problem, we are using [VSCode dev containers][]:

> This simply takes the Rust dev container from Microsoft and installs soroban-cli and the appropriate wasm target.
>
> If the quickstart Docker image is run outside the container, its RPC endpoint is available as
> http://host.docker.internal:8000/soroban/rpc.

Further, see [Dockerfile](.devcontainer/Dockerfile).



[TypeScript]: https://www.typescriptlang.org/
[npm]: https://www.npmjs.com/
[tsc]: https://www.typescriptlang.org/docs/handbook/compiler-options.html
[NodeJS]: https://nodejs.org/en
[eslint]: https://eslint.org/
[prettier]: https://prettier.io/
[MochaJS]: https://mochajs.org/
[ChaiJS]: https://www.chaijs.com/
[husky]: https://typicode.github.io/husky/
[VSCode dev containers]: https://code.visualstudio.com/docs/devcontainers/containers