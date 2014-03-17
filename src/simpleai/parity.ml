open Simple

type t = Top | Even | Odd

let universe = Top

let singleton i =
  if Int32.rem i 2l = 0l then Even else Odd

let of_bounds (i1, i2) =
  let i1 = singleton i1 in
  let i2 = singleton i2 in
  if i1 = i2 then i1 else Top

let join i1 i2 =
 if i1 = i2 then i1 else Top

let widen = join

let contains i1 i2 =
  match i1, i2 with
  | Top, _ -> true
  | _ -> i1 = i2

let implies (t, cmp, value) =
  match t, cmp with
  | Top, _ -> true
  | _, Equals -> singleton value = t
  | _, _ -> false

let neg t = t

let add i1 i2 =
  match i1, i2 with
  | Even, Even | Odd, Odd -> Even
  | Odd, Even | Even, Odd -> Odd
  | _ -> Top

let mul i1 i2 =
  match i1, i2 with
  | Even, _ | _, Even -> Even
  | Odd, Odd -> Odd
  | _ -> Top

let div = mul

let is_safe_add _ _ = true
let is_safe_div _ _ = true
let is_safe_mul _ _ = true

let guard op c x =
  let open UnrelState in
  match op with
  | EQ -> if c = x || c = Top then c else raise Emptyset
  | NEQ -> if c <> x then c else raise Emptyset
  | _ -> c

let to_string = function
  | Even -> "even"
  | Odd -> "odd"
  | Top -> "T"
