open OUnit
open Printf

open Tdk

module V1 = struct
  type t = unit

  let compare () () = 0
  let hash () = 0
  let to_string () = "unit"
end

module V2 = struct
  type t = X | Y

  let compare = Pervasives.compare
  let hash = function | X -> 0 | Y -> 1
  let to_string = function | X -> "X" | Y -> "Y"
end

module C = struct
  type t = Int32.t

  let compare = Pervasives.compare
  let equal a b = compare a b = 0
  let hash a = Int32.to_int a

  let to_string = Int32.to_string
end

module R = struct
  include C

  let zero = 0l
  let one = 1l
  let sum = Int32.add
  let prod = Int32.mul
end

let one_variable () =
  let module F1 = Vcr.Make(V1)(C)(R) in
  let domain = [0l; 1l; 2l; 3l; 4l; 5l] in
  let mk_t f =
    List.fold_left (fun t x ->
      F1.(sum t (atom ((), x) (f x) 0l)))
    (F1.const 0l) domain
  in
  let agree t f =
    List.for_all (fun x ->
      match F1.(peek (restrict ((), x) t)) with
      | None    -> false
      | Some(v) -> C.compare (f x) v = 0)
    domain
  in
  let f = fun x -> x in
  let t = mk_t f in
  "`f(x) = x` for x in {1, 2, 3, 4, 5}"
    @? (agree t f);
  let f = fun x -> Int32.mul x x in
  let t = F1.(prod t t) in
  "`f(x) = x^2` for x in {1, 2, 3, 4, 5}"
    @? (agree t f);
  let f = fun x -> Int32.(add (mul x x) 3l) in
  let t = F1.(sum t (const 3l)) in
  "`f(x) = x^2 + 3` for x in {1, 2, 3, 4, 5}"
    @? (agree t f)

let two_variable () =
  let module F2 = Vcr.Make(V2)(C)(R) in
  let domain = [0l; 1l; 2l; 3l; 4l; 5l] in
  let mk_t f =
    List.fold_left (fun t x ->
      let cx = F2.atom (V2.X, x) 1l 0l in
      List.fold_left (fun t y ->
        let cy = F2.atom (V2.Y, y) (f x y) 0l in
        F2.(sum t (prod cx cy)))
      t domain)
    (F2.const 0l) domain
  in
  let agree t f =
    List.for_all (fun x ->
      List.for_all (fun y ->
        let t' = F2.(restrict (V2.Y, y) (restrict (V2.X, x) t)) in
        match F2.peek t' with
        | None    -> false
        | Some(v) -> C.compare (f x y) v = 0)
      domain)
    domain
  in
  let f = fun x y -> x in
  let t = mk_t f in
  "`f(x, y) = x` for x, y in {1, 2, 3, 4, 5}"
    @? (agree t f);
  let f = fun x y -> y in
  let t = mk_t f in
  "`f(x, y) = y` for x, y in {1, 2, 3, 4, 5}"
    @? (agree t f);
  let f = fun x y -> Int32.mul x x in
  let t' = mk_t f in
  "`f(x, y) = x^2` for x, y in {1, 2, 3, 4, 5}"
    @? (agree t' f);
  let f = fun x y -> Int32.(add (mul x x) y) in
  let t = F2.sum t' t in
  "`f(x, y) = x^2 + y` for x, y in {1, 2, 3, 4, 5}"
    @? (agree t f);
  let f = fun x y -> Int32.(add (mul x x) y) in
  let t = mk_t f in
  "`f(x, y) = x^2 + y` for x, y in {1, 2, 3, 4, 5}"
    @? (agree t f)

let disjoint () =
  let module F1 = Vcr.Make(V1)(C)(R) in
  let f = F1.atom ((), 0l) 1l 0l in
  let g = F1.atom ((), 1l) 1l 0l in
  "diagrams with disjoint domains are zero"
    @? F1.(equal (prod f g) (const 0l))

let rec was_successful =
  function
    | [] -> true
    | RSuccess _::t
    | RSkip _::t ->
        was_successful t
    | RFailure _::_
    | RError _::_
    | RTodo _::_ ->
        false

let _ =
  let suites = [
    "disjoint" >:: disjoint;
    "one-variable" >:: one_variable;
    "two-variable" >:: two_variable
  ] in
  let verbose = ref false in
  let set_verbose _ = verbose := true in
  Arg.parse
    [("-verbose", Arg.Unit set_verbose, "Run the test in verbose mode.");]
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    ("Usage: " ^ Sys.argv.(0) ^ " [-verbose]");
  if not
    (List.for_all
       (fun suite -> was_successful (run_test_tt ~verbose:!verbose suite))
       suites)
  then exit 1
