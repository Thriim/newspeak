open UnrelState


type cst = Value of int32 | Max | Min
type t = { less : cst; up : cst }

val universe: t
val singleton: Int32.t -> t
val of_bounds: (Int32.t * Int32.t) -> t
val join: t -> t -> t
val widen: t -> t -> t
val contains: t -> t -> bool
val implies: (t * Simple.cmp * Int32.t) -> bool
val neg: t -> t
val add: t -> t -> t
val mul: t -> t -> t
val div: t -> t -> t
val is_safe_add: t -> t -> bool
val is_safe_mul: t -> t -> bool
val is_safe_div: t -> t -> bool
val guard: bop -> t -> t -> t
val to_string: t -> string


val add_cst: cst -> int32 -> cst
val sub_cst: cst -> int32 -> cst
