# Alternative monitor for Timelock using reverse reasoning

----

_Andrey Kuprianov, 2024_

In this example we are looking at the [Timelock][] contract, the same that was used for the [SCF 24 submission example][]. Compared to _direct_ reasoning applied in the submission example (stucturing of specification according to methods: if a method is executed, then those should be its effects), we are going to apply an alternative structure, which we may call _hybrid_, where we combine direct specifications for methods with _reverse_ reasoning (start with the observed effects, and go back to the causes).


## Structuring monitor specifications

Before diving into the concrete timelock example, let's explore a bit of a theory of what we want to achieve with runtime monitors. Eventually, runtime monitors are going to be deployed on the live blockchain, and they should serve two purposes:

- **Prevent safety violations**: bad things, such as your token balance being stolen, should not happen. This is the primary goal of runtime monitors: react preventively, and abort unwanted executions.
- **Detect liveness violations**: good things should be able to happen! E.g. you, as an account owner, should be able to withdraw your own balance. If a legitimate transaction keeps reverting, that's also a bug, not less severe than someone stealing your tokens.
- **Warn about unexpected behaviors**: same as code, specs are not perfect. If a spec author overlooked some behaviors, and they manifest themselves on the live blockchain, this may mean anything: from simple spec incompleteness, to an exploit being executed. Monitors can be configured to either issue a simple warning, or to prevent such behaviors altogether.

The problem we've observed with the specification approaches previously is that the specs of _what_ the method should do can easily be much larger than the actual implementation; compare e.g. this [ERC-721 Certora spec][] with the [ERC-721 implementation][] (don't forget to exclude comments when comparing).

So monitors should be able to specify both safety and liveness properties, and do it _compactly_. For that we impose a certain structure to the direct reasoning (cause -> effect), as well as apply the reverse reasoning (effect -> cause).

### Structured direct reasoning

Here we reason from the cause (method invocation) to the effect, but apply a structure which closely mimics in formal semantics what we expect to see when we program smart contracts. The essence of the structure is in the picture below:

![Direct monitor specs](./MonitorSpecs-Direct.png)

- `MustFail_i` is a condition under which the method is expected to fail. If _any_ of those conditions hold, the monitor fires, and checks that the method does indeed fail;
- `MustSucceed_i` is a condition, under which the method is expected to succeed, _provided that_ none of the `MustFail_i` conditions fired. Each `MustSucceed_i` condition represents a separate happy path in the method invocation;
- `MustAchieve_i` is a condition over past and next state variables, which specifies the effect that the method invocation should achieve (e.g. the tokens should be transferred). _All_ of `MustAchieve_i` should hold if the method is executed successfully.


In the above, `Must<Fail|Succeed|Achieve>` is a prefix, which tells the monitor system how to interpret this predicate. The complete pattern for predicate names with these prefixes is as follows:

```
Must<Fail|Succeed|Achieve>_<Method>_<ConditionDescription>
```

All predicates which refer to the same `<Method>` will be grouped, to create together one _method monitor_. Interpreted formally, the monitor should do the following when `<Method>` is invoked:

1. If any of `MustFail_i` conditions fire, check that method invocation reverts (otherwise, issue a warning / revert if configured to do so)
2. If none of `MustFail_i` conditions fired, but method invocation reverted, issue a warning (incomplete spec)
3. If none of  `MustFail_i` fired, and one of `MustSucceed_i` conditions fired, check that method invocation succeeds (otherwise, issue a warning)
3. If none of  `MustFail_i` fired, and none of `MustSucceed_i` conditions fired, but method invocation succeeded, issue a warning of an incomplete spec (or revert if configured to do so)
4. If method invocation succeeds, check that all of `MustAchieve_i` conditions hold on the pre- and post-states of the method invocation (otherwise, issue a warning / revert if configured to do so)




[Timelock]: https://github.com/stellar/soroban-examples/blob/v20.0.0/timelock/src/lib.rs
[SCF 24 submission example]: ../../scf24/example/README.md
[ERC-721 Certora spec]: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/255e27e6d22934ddaf00c7f279039142d725382d/certora/specs/ERC721.spec
[ERC-721 implementation]: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/255e27e6d22934ddaf00c7f279039142d725382d/contracts/token/ERC721/ERC721.sol