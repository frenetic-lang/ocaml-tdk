open OUnit
open Printf

open Tdk

module B = Bdd.Make(struct
  type t = Int32.t

  let compare = Int32.compare
  let equal a b = compare a b = 0
  let hash a = Int32.to_int a

  let to_string = Int32.to_string
end)

let impl a b = B.(sum b (neg a))

let tautologies () =
  let open B in
  "`const true` is a tautology"         @? (tautology (const true));
  "`neg (const false)` is a tautology"  @? (tautology (neg (const false)));
  let a = var 0l in
  let b = var 1l in
  let c = var 2l in
  "((a /\\ b) -> c) with b = false is a tautology"
    @? (tautology (restrict [(1l, false)] (impl (prod a b) c)));
  "((a /\\ b) -> c) -> (a -> b -> c) is a tautology"
    @? (tautology (impl (impl (prod a b) c)
                        (impl a (impl b c))))

let falsehoods () =
  let open B in
  "`const false` is a falsehood"        @? (falsehood (const false));
  "`neg (const true)` is a falsehood"   @? (falsehood (neg (const true)));
  let a = var 0l in
  "(a /\\ neg a) is a falsehood" @? (falsehood (prod a (neg a)))

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
    "Tautologies" >:: tautologies;
    "Falsehoods"  >:: falsehoods
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
