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

 ### 2.1 Dev containers

To easily set up your dev environment, we provide VSCode [dev containers][].

There is one for Solarkraft development in [`./solarkraft`](./solarkraft/.devcontainer/), and one for Soroban development in [`./ContractExamples`](./ContractExamples/.devcontainer/).

To use the dev containers:

0. Install [Docker](https://www.docker.com/).
1. Open VSCode in the respective directory (e.g., `cd solarkraft/ && code .`).
2. Install the [`Dev Containers` extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) by Microsoft (VSCode may also prompt you to do this).
3. Build and open the container by selecting **Dev Containers: Reopen in Container** in the VSCode command palette (`Ctrl-Shift-P`, or `Cmd-Shift-P` on macOS).


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

To work around these problems, you can use our dev containers (see above), to get a reproducible dev environment.


[dev containers]: https://code.visualstudio.com/docs/devcontainers/containers
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