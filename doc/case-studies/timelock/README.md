# Hybrid Timelock Monitor

_Andrey Kuprianov, 2024_

------

In this example we are looking at the [Timelock contract][], the same that was used for the [SCF 24 submission example][]. Compared to _direct_ reasoning applied in the submission example (stucturing of specification according to methods: if a method is executed, then those should be its effects), we are going to apply an alternative structure, which we may call _hybrid_, where we combine direct specifications for methods with _reverse_ reasoning (start with the observed effects, and go back to the causes).


_**NB**: Before diving into this concrete example, we recommend to take a look at the general theory outlined in [Direct and Reverse Monitor Specifications][]._

Assuming you familiarized yourself with the hybrid monitor specification approach, go ahead and compare:

- Direct monitor specs in the [SCF 24 submission example][]
- [Timelock monitor spec][] written using the hybrid approach

Let's go over the spec together here. (please note that this spec is not even a completely valid TLA+ yet, as e.g. many definitions need to be filled in from the contract code; this is tbd.)

### Direct monitor for the `deposit` method

The [deposit method](https://github.com/stellar/soroban-examples/blob/186443aab0bf8b7c2673428c38708bf38cb772ab/timelock/src/lib.rs#L57-L91) allows a user to send certain amount of token to this contracts, and to specify up to 10 claimants any of whom should be able to claim the funds when the specified timing condition fulfills. `MustFail` predicates in the spec closely follow the assertions in the code. Notice though that `MustFail_deposit_NotEnoughBalance` is not an assertion in the code, but a precondition which arises from usage of an external token contract. Nevertheless, the monitor system will force us to be complete (otherwise it will warn us about an unexpectedly reverted transaction).


```tla 
MustFail_deposit_TooManyClaimants == 
    claimants.len > 10

MustFail_deposit_Unauthorized == 
    ~authorized(from)

\* This property would not be originally conceived 
\* if looking solely at the timelock contract source
MustFail_deposit_NotEnoughBalance == 
    token.balance(from) < amount

\* Balance is externally relevant; initialized flag is not
\* What matters for users is that balance is not overwritten
MustFail_deposit_AlreadyInitialized == 
    exists(balance)

\* The above failure conditions exhaust the precondition of deposit method
\* The default success condition is not needed, but we may provide it
MustPass_deposit_Default = TRUE

MustHold_deposit_BalanceRecordCreated ==
    exists(balance')

MustHold_deposit_BalanceRecordCorrect ==
    /\ balance'.token = token
    /\ balance'.amount = amount
    /\ balance'.time_bound = time_bound
    /\ balance'.claimants = claimants

MustHold_deposit_TokenTransferred ==
    token.transferred(from, this, amount)
```


### Direct monitor for the `claim` method


The [claim method](https://github.com/stellar/soroban-examples/blob/186443aab0bf8b7c2673428c38708bf38cb772ab/timelock/src/lib.rs#L93-L121) allows a user to claim the funds deposited previously into the contract, provided all conditions are fulfilled. Again `MustFail` predicates in the spec closely follow the assertions in the code. Notice that `MustPass` predicates allow us to separately specify two distinct happy paths for `claim`, namely when the time bound is given as `Before` and as `After`.


```tla
MustFail_claim_Unauthorized == 
    ~authorized(claimant)

MustFail_claim_NoBalanceRecord == 
    ~exists(balance)

MustFail_claim_NotClaimant == 
    claimant \notin claimants

\* One success condition: correctly claimed before time bound
MustPass_claim_BeforeTimeBount
    /\ time_bound.kind = "Before" 
    /\ env.ledger.timestamp <= balance.time_bound.timestamp

\* Another success condition: correctly claimed after time bound
MustPass_claim_AfterTimeBount
    /\ time_bound.kind = "After" 
    /\ env.ledger.timestamp >= balance.time_bound.timestamp

MustHold_claim_TokenTransferred ==
    balance.token.transferred(this, claimant, balance.amount)

MustHold_deposit_BalanceRecordRemoved ==
    ~exists(balance')
```

### Balance record effect monitor

We employ an effect monitor for the balance record, because we want to make sure that all side effects wrt. this critical state component are correctly accounted for. This effect monitor fires when either the balance record is created or destroyed, or when its content is modified; only the `deposit` and `claim` methods are allowed to change the balance record, thus guarding from possible unintended consequences upon system evolution in the future.


```tla
\* This trigger fires when the balance record is created or destroyed
\* Notice that it doesn't track the record content
MonitorTrigger_Balance_RecordChanged ==
    exists(balance) /= exists(balance)'

\* This trigger fires when the balance record content Achieves
\* Notice that it will panic (won't fire) if the record doesn't exist
MonitorTrigger_Balance_ContentChanged ==
    balance /= balance'

\* Only deposit and claim methods are allowed to alter balances
MonitorEffect_Balance_Changed ==
    \/ method = "deposit"
    \/ method = "claim"
```

Notice that in the above three TLA+ fragments, changes to the deposit record are scattered across them. If we are concered about that fact, we could delete the predicates `MustHold_deposit_BalanceRecordCreated`, `MustHold_deposit_BalanceRecordCorrect`, and `MustHold_deposit_BalanceRecordRemoved`, and instead concentrate all management of the balance record in one place like this:


```tla
MonitorEffect_Balance_Changed ==
    \/ /\ method = "deposit"
       /\ ~exists(balance)
       /\ exists(balance')
       /\ balance'.token = token
       /\ balance'.amount = amount
       /\ balance'.time_bound = time_bound
       /\ balance'.claimants = claimants
    \/ /\ method = "claim"
       /\ exists(balance)
       /\ ~exists(balance')
```

The combination of `deposit` and `claim` method monitors with the balance record effect monitor will still ensure the correct behavior wrt. to the balance record.


### Token balance effect monitor

This final part of the new monitor spec ensures that only the `claim` method is allowed to reduce the token balance of the Timelock contract, again guarding from side effects, either unintentional or malicious:

```tla
\* This trigger fires when the token balance of this contract is reduced
\* Notice that it will panic (won't fire) if balance record doesn't exist
MonitorTrigger_TokenBalance_Reduced ==
    token_balance(balance.token, this)' <
    token_balance(balance.token, this) 

\* Only claim method is allowed to reduce this contract token balance
MonitorEffect_TokenBalance_Reduced ==
    method = "claim"
```

This is it for the monitor spec of the Timelock contract. We hope you are convinced that the new hybrid style of writing monitor specs is beneficial in terms of clarity, conciseness, and completeness. Please let us know what you think; e.g. feel free to open an issue on the repo.


[Timelock contract]: https://github.com/stellar/soroban-examples/blob/v20.0.0/timelock/src/lib.rs
[SCF 24 submission example]: ../../scf24/example/README.md
[Direct and Reverse Monitor Specifications]: ../../monitor-specs.md
[ERC-721 Certora spec]: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/255e27e6d22934ddaf00c7f279039142d725382d/certora/specs/ERC721.spec
[ERC-721 implementation]: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/255e27e6d22934ddaf00c7f279039142d725382d/contracts/token/ERC721/ERC721.sol
[Timelock monitor spec]: ./timelock_monitor.tla