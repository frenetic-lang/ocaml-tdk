# tdk - The Decision Kit

The decision kit is a collection of data structures that useful for
representing functions, relations, and other combinatorial objects. All these
data strctures are based on a generalization of binary decision diagrams.

[![Build Status](https://travis-ci.org/frenetic-lang/ocaml-tdk.png)](https://travis-ci.org/frenetic-lang/ocaml-tdk)

## Installation

Tdk has no dependencies. To install the library, simply clone the repository,
build it and install it using the following commands:

    make && make install

Alternatively, you can install tdk using [OPAM][]:

[OPAM]: http://opam.ocaml.org/

    opam install tdk

For building and running the tests during development, you will need to install
the `oUnit` package and reconfigure the build process to enable tests:

    opam install oUnit
    ./configure --enable-tests
    make && make test

## Features

The library supports three data structures:

  * `Vlr` - a Variable-Lattice-Result diagram for representing functions over
    variables that are assigned values in a lattice, producing a result with an
    algebraic structure.
  * `Vcr` - a Variable-Constant-Result diagram for representing functions
    over variables that are assigned values in a total ordering, producing
    results with an algebraic structure.
  * `Bdd` - a Binary Decision Diagram for representing boolean-valued functions
    over boolean variables.

Each of these data structures is implemented as a functor. Here's an example of
how to instantiate and use the `Bdd` functor for variables represented as
`Int32.t`s:

```ocaml
module B = Tdk.Bdd.Make(struct
  type t = Int32.t

  let compare = Int32.compare
  let hash a = Int32.to_int a

  let to_string = Int32.to_string
end)

let impl a b = B.(sum b (neg a))

let a = B.var 0l
let b = B.var 1l
let c = B.var 2l

(* `((a /\ b) -> c) -> (a -> b -> c)` is a tautology *)
assert B.(tautology (impl (impl (prod a b) c)
                          (impl a (impl b c))))
```

## Cultural Note

> Yall take the PC way, let ya CD's play  
> I rock a 120 Minute TDK  
> Hey! Looking for a way to the hype  
> "Welcome to the underground!" Shit, that's just a day in the life

&mdash; Cashmere the Pro, *Filthy Nasty by Cunninlynguists*

## License

BSD3, see LICENSE file for its text.
