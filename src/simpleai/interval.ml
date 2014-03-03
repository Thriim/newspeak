open UnrelState

type cst = Value of int32 | Max | Min
type t = { less : cst; up : cst }

let universe = { less = Min; up = Max }

let singleton i =
  { less = Value i; up = Value i }

let of_bounds (l, u) =
  { less = Value l; up = Value u }

let int32_max i1 i2 =
  if Int32.compare i1 i2 >= 0 then i1 else i2

let int32_min i1 i2 =
  if Int32.compare i1 i2 >= 0 then i2 else i1

let join i1 i2 =
  let less = match i1.less, i2.less with
    | Min, _ | _, Min -> Min
    | Max, i | i, Max -> i
    | Value i1, Value i2 -> Value (int32_min i1 i2)
  in
  let up = match i1.up, i2.up with
    | Max, _ | _, Max -> Max
    | Min, i | i, Min -> i
    | Value i1, Value i2 -> Value (int32_max i1 i2)
  in
  { less; up }

let widen i1 i2 =
  let less = match i1.less, i2.less with
    | Value v1, Value v2 when Int32.compare v1 v2 <= 0 -> Value v1
    | _ -> Min in
  let up = match i1.up, i2.up with
    | Value v1, Value v2 when Int32.compare v1 v2 >= 0 -> Value v1
    | _ -> Max in
  { less; up }

let infeq i1 i2 =
  match i1, i2 with
  | i1, i2 when i1 = i2 -> true
  | Min, _ | _, Max -> true
  | _, Min | Max, _ -> false
  | Value i1, Value i2 -> i1 < i2

let contains i1 i2 =
  infeq i1.less i2.less && infeq i2.less i1.up && infeq i2.up i1.up

let intersects i1 i2 =
  infeq i1.up i2.less

let f_of_cmp cmp =
  let open Simple in
  match cmp with
  | Equals -> (=)
  | IsLess -> (<)

let implies (t, cmp, value) =
  let open Simple in
  let implies' v = match v, cmp with
    | Min, _ | Max, Equals -> false
    | Max, IsLess -> true
    | Value v, _ ->
      let cmp = f_of_cmp cmp in
      cmp (Int32.compare v value) 0 in
  implies' t.less && implies' t.up

let neg v =
  let inv v = match v with
    | Max -> Min
    | Min -> Max
    | Value v -> Value (Int32.neg v) in
  let up = inv v.less in
  let less = inv v.up in
  { less; up }

let is_safe_add' i1 i2 =
  match i1, i2 with
  | Value v1, Value v2 ->
    let res = Int32.add v1 v2 in
    (Int64.compare
       (Int64.add (Int64.of_int32 v1) (Int64.of_int32 v2))
       (Int64.of_int32 res)) == 0
  | _, _ -> false

let is_safe_add i1 i2 =
  is_safe_add' i1.less i2.less && is_safe_add' i1.up i2.up

let add (i1 : t) (i2 : t) =
  let less = match i1.less, i2.less with
    | Max, _ | _, Max -> Max (* Possibly bottom *)
    | _ , Min | Min, _ -> Min
    | Value v1, Value v2 ->
      if is_safe_add' i1.up i2.up then Value (Int32.add v1 v2) else Min in
  let up = match i1.up, i2.up with
    | Min, _ | _, Min -> Min (* Possibly bottom *)
    | Max, _ | _, Max -> Max
    | Value v1, Value v2 ->
      if is_safe_add' i1.up i2.up then Value (Int32.add v1 v2) else Max in
  { less; up }

(* let guard op i1 i2 = *)
(*   let cmp = match op with *)
(*     | LTE -> (>) | EQ -> (<>) | GT -> (<=) *)
(*     | LT -> (>=) | GTE -> (<) | NEQ -> (=) in *)
(*   let less = *)
(*     match op, i1.less, i2.less with *)
(*     | _, Value v1, Value v2 when cmp (Int32.compare v1 v2) 0 -> raise Emptyset *)
(*     | _, _, _ -> i2.less in *)
(*   let up = *)
(*     match i1.up, i2.up with *)
(*     | Value v1, Value v2 when cmp (Int32.compare v1 v2) 0 -> raise Emptyset *)
(*     | _, _ -> i2.up in *)
(*   { less; up } *)

let is_bottom i =
  match i.less, i.up with
  | Max, Min -> true
  | Value v1, Value v2 when Int32.compare v1 v2 < 0 -> true
  | _ -> false

let bottom = { less = Max; up = Min }

let intersect i1 i2 = { less = i1.up; up = i2.less }

let guard op c x =
  match (op, c, x) with
  | EQ, c, x ->
    if contains c x then c
    else if contains x c then x
    else if is_bottom @@ intersect c x then raise Emptyset
    else intersect c x
  | NEQ, c, x ->
    if not @@ contains c x then x else if not @@ contains x c then c
    else raise Emptyset
  | LTE, c, x ->
    begin
      match c.up, x.less with
      | Max, Min | Max, Value _ | Value _, Min -> raise Emptyset
      (* | Value v1, Value v2 when (Int32.compare v1 v2) > 0 -> raise Emptyset *)
      | _, _ -> begin
          match c.up, x.up with
          | Value v1, Value v2 when Int32.compare v1 v2 > 0 -> raise Emptyset
          | _ -> join c x
        end
    end
  | LT, c, x ->
    begin
      match c.up, x.less with
      | Max, Min | Max, Value _ | Value _, Min -> raise Emptyset
      (* | Value v1, Value v2 when (Int32.compare v1 v2) > 0 -> raise Emptyset *)
      | _, _ -> begin
          match c.up, x.up with
          | Value v1, Value v2 when Int32.compare v1 v2 >= 0 -> raise Emptyset
          | _ -> join c x
        end
    end
  | GTE, c, x ->
    begin
      match c.less, x.up with
      | Min, Max | Min, Value _ | Value _, Max -> raise Emptyset
      (* | Value v1, Value v2 when (Int32.compare v1 v2) > 0 -> raise Emptyset *)
      | _, _ -> begin
          match c.less, x.less with
          | Value v1, Value v2 when Int32.compare v1 v2 < 0 -> raise Emptyset
          | _ -> join c x
        end
    end
  | GT, c, x ->
    begin
      match c.less, x.up with
      | Min, Max | Min, Value _ | Value _, Max -> raise Emptyset
      (* | Value v1, Value v2 when (Int32.compare v1 v2) > 0 -> raise Emptyset *)
      | _, _ -> begin
          match c.less, x.less with
          | Value v1, Value v2 when Int32.compare v1 v2 <= 0 -> raise Emptyset
          | _ -> join c x
        end
    end

let to_string v =
  let to_string' v =
    match v with
    | Min -> "Min"
    | Max -> "Max"
    | Value v -> Int32.to_string v in
  Format.sprintf "[%s; %s]" (to_string' v.less) (to_string' v.up)
