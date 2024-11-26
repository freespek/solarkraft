--------------------------------- MODULE xycloans_types -----------------------
EXTENDS Variant

(*
    The relevant parts of the storage that is accessed by the contract.
    Note that the storage is partial. At any point in time, we only have
    access to the parts of the storage that are touched by the contract.

    @typeAlias: storage = {
        self_instance: {
            FeePerShareUniversal: Int,
            TokenId: Str
        },
        self_persistent: {
            Balance: Str -> Int,
            MaturedFeesParticular: Str -> Int,
            FeePerShareParticular: Str -> Int
        },
        token_persistent: {
            Balance: Str -> Int
        }
    };

    The environment of the XY Loans contract that should be
    produced by Solarkraft from the transaction metadata:

    @typeAlias: env = {
        current_contract_address: Str,
        storage: $storage,
        old_storage: $storage
    };

    An external contract call:

    @typeAlias: call =
          Create({ addr: Str })
        | Initialize({ token: Str })
        | Deposit({ from: Str, amount: Int })
        | Borrow({ receiver_id: Str, amount: Int })
        | UpdateFeeRewards({ addr: Str})
    ;

    Finally, a transaction is:

    @typeAlias: tx = {
        env: $env,
        call: $call,
        status: Bool
    };
 *)
xycloans_typedefs == TRUE

(* Boilerplate definitions for the method types (mostly generated with copilot) *)

\* @type: Str => $call;
Create(addr) == Variant("Create", [ addr |-> addr ])
\* @type: Str => $call;
Initialize(token) == Variant("Initialize", [ token |-> token ])
\* @type: $call => Bool;
IsInitialize(call) == VariantTag(call) = "Initialize"
\* @type: $call => { token: Str };
AsInitialize(call) == VariantGetUnsafe("Initialize", call)

\* @type: (Str, Int) => $call;
Deposit(from, amount) == Variant("Deposit", [ from |-> from, amount |-> amount ])
\* @type: $call => Bool;
IsDeposit(call) == VariantTag(call) = "Deposit"
\* @type: $call => { from: Str, amount: Int };
AsDeposit(call) == VariantGetUnsafe("Deposit", call)

\* @type: (Str, Int) => $call;
Borrow(receiver_id, amount) == Variant("Borrow", [ receiver_id |-> receiver_id, amount |-> amount ])
\* @type: $call => Bool;
IsBorrow(call) == VariantTag(call) = "Borrow"
\* @type: $call => { receiver_id: Str, amount: Int };
AsBorrow(call) == VariantGetUnsafe("Borrow", call)

\* @type: Str => $call;
UpdateFeeRewards(addr) == Variant("UpdateFeeRewards", [ addr |-> addr ])
\* @type: $call => Bool;
IsUpdateFeeRewards(call) == VariantTag(call) = "UpdateFeeRewards"
\* @type: $call => { addr: Str };
AsUpdateFeeRewards(call) == VariantGetUnsafe("UpdateFeeRewards", call)

===============================================================================