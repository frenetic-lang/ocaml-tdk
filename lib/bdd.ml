open S

module Make(V:HashCmp) = struct
  module C = struct
    type t = bool

    let hash x = if x then 1 else 0

    let compare x y =
      match x, y with
      | true , false -> -1
      | false, true  ->  1
      | _    , _     ->  0

    let to_string x = if x then "true" else "false"
  end

  module R = struct
    include C

    let one = true
    let zero = false

    let sum x y = x || y
    let prod x y = x && y
  end

  module B = Vcr.Make(V)(C)(R)

  type t = B.t
  type v = B.v
  type r = B.r

  let const = B.const
  (* NOTE: This is done to ensure the unique representation of BDDs *)
  let atom (v,c) t f = if c then B.atom (v, true) t f else B.atom (v, true) f t

  let restrict = B.restrict
  let peek = B.peek
  let support = B.support

  let sum = B.sum
  let prod = B.prod
  let map_r = B.map_r

  let fold = B.fold
  let destruct = B.destruct
  let iter = B.iter

  let equal = B.equal
  let to_string = B.to_string
  let to_dot = B.to_dot

  let var v = atom (v, true) true false
  let neg t = map_r (fun r -> not r) t

  exception Short_circuit

  let tautology t =
    try
      iter ~order:`Post
        (fun r -> if not r then raise Short_circuit else ())
        (fun _ _ _ -> ())
        t;
      true
    with Short_circuit -> false

  let falsehood t =
    try
      iter ~order:`Post
        (fun r -> if r then raise Short_circuit else ())
        (fun _ _ _ -> ())
        t;
      true
    with Short_circuit -> false

end
