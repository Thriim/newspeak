

module P = Parity
module I = Interval

type t = P.t * I.t

let reduce p (i: I.t) =
  let open P in
  let open I in
  match p, i.less, i.up with
  | Top, Value (v1), Value (v2) ->
    if P.singleton v1 = P.singleton v2 then
      P.singleton v1, i
    else  p, i
  | _, Value (v1), Value (v2) ->
    if P.singleton v1 = P.singleton v2 && P.singleton v1 = p then
      p, i
    else if P.singleton v1 = p then
      p, { less = i.less; up = I.add_cst i.up (-1l)  }
    else if P.singleton v2 = p then
      p, { up = i.up; less = I.add_cst i.less 1l }
    else Top, i
  | _, Value v, _ ->
    if P.singleton v = p then p, i
    else p, { less = I.add_cst i.less 1l; up = i.up }
  | _, _, Value v ->
    if P.singleton v = p then p, i
    else p, { up = I.add_cst i.up (-1l); less = i.less }
  | _ -> p, i

let universe = P.universe, I.universe

let singleton v = P.singleton v, I.singleton v

let of_bounds b = P.of_bounds b, I.of_bounds b


let join (p1, i1) (p2, i2) =
  reduce (P.join p1 p2) (I.join i1 i2)

let guard op (p1, i1) (p2, i2) =
  reduce (P.guard op p1 p2) (I.guard op i1 i2)

let neg (p, i) =
  reduce(P.neg p) (I.neg i)

let add (p1, i1) (p2, i2) =
  reduce (P.add p1 p2) (I.add i1 i2)

let mul (p1, i1) (p2, i2) =
  reduce (P.mul p1 p2) (I.mul i1 i2)

let div (p1, i1) (p2, i2) =
  reduce (P.div p1 p2) (I.div i1 i2)

let is_safe_add (p1, i1) (p2, i2) =
  P.is_safe_add p1 p2 && I.is_safe_add i1 i2

let is_safe_mul (p1, i1) (p2, i2) =
  P.is_safe_mul p1 p2 && I.is_safe_mul i1 i2

let is_safe_div (p1, i1) (p2, i2) =
  P.is_safe_div p1 p2 && I.is_safe_div i1 i2

let implies _ = assert false

let contains (p1, i1) (p2, i2) =
  P.contains p1 p2 && I.contains i1 i2

let widen (p1, i1) (p2, i2) =
  reduce (P.widen p1 p2) (I.widen i1 i2)


let to_string (p, i) = Format.sprintf "(%s, %s)" (P.to_string p) (I.to_string i)
