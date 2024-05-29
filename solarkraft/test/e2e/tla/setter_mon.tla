---- MODULE setter_mon ----

EXTENDS Apalache, Variants

VARIABLES
    \* @type: Bool;
    MY_BOOL,
    \* @type: Int;
    MY_U32,
    \* @type: Int;
    MY_I32,
    \* @type: Int;
    MY_U64,
    \* @type: Int;
    MY_I64,
    \* @type: Int;
    MY_U128,
    \* @type: Int;
    MY_I128,
    \* @type: Str;
    MY_SYM,
    \* @type: Str;
    MY_BYTES,
    \* @type: Str;
    MY_BTES32,
    \* @type: Str;
    MY_ADDR,
    \* @type: Seq(Int);
    MY_VEC,
    \* @type: Str -> Int;
    MY_MAP,
    \* @type: { a: Int, b: Int };
    MY_STRUCT,
    \* @type: A(Int) | B(Int);
    MY_ENUM

set_bool(env, v) ==
    /\ MY_BOOL = FALSE
    /\ MY_BOOL' = v
    /\ UNCHANGED <<MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_u32(env, v) ==
    /\ MY_U32 = 0
    /\ MY_U32' = v
    /\ UNCHANGED <<MY_BOOL, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_i32(env, v) ==
    /\ MY_I32 = 0
    /\ MY_I32' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_u64(env, v) ==
    /\ MY_U64 = 0
    /\ MY_U64' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_i64(env, v) ==
    /\ MY_I64 = 0
    /\ MY_I64' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_u128(env, v) ==
    /\ MY_U128 = 0
    /\ MY_U128' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_i128(env, v) ==
    /\ MY_I128 = 0
    /\ MY_I128' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_sym(env, v) ==
    /\ MY_SYM = ""
    /\ MY_SYM' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_bytes(env, v) ==
    /\ MY_BYTES = "00"
    /\ MY_BYTES' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_bytes32(env, v) ==
    /\ MY_BTES32 = "fded3f55dec47250a52a8c0bb7038e72fa6ffaae33562f77cd2b629ef7fd424d"
    /\ MY_BTES32' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_address(env, v) ==
    /\ MY_ADDR = "CCLCX5GS3NRUHDLKFBTHWT5CD5US5BUNWCX6H2BN3RKXMVUZMYRXJLBT"
    /\ MY_ADDR' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_VEC, MY_MAP, MY_STRUCT, MY_ENUM>>

set_vec(env, v) ==
    /\ MY_VEC = <<>>
    /\ MY_VEC' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_MAP, MY_STRUCT, MY_ENUM>>

set_map(env, v) ==
    /\ MY_MAP = [x \in {} |-> 0]
    /\ MY_MAP' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_STRUCT, MY_ENUM>>

set_struct(env, v) ==
    /\ MY_STRUCT = [ a |-> 0, b |-> 0 ]
    /\ MY_STRUCT' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_ENUM>>

set_enum(env, v) ==
    /\ MY_ENUM = Variant("A", 0)
    /\ MY_ENUM' = v
    /\ UNCHANGED <<MY_BOOL, MY_U32, MY_I32, MY_U64, MY_I64, MY_U128, MY_I128, MY_SYM, MY_BYTES, MY_BTES32, MY_ADDR, MY_VEC, MY_MAP, MY_STRUCT>>
=============================
