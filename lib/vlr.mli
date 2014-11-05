open S

(** Variable-Lattice-Result *)
module Make(V:HashCmp)(L:Lattice)(R:Result) : DD
  with type v = V.t * L.t
   and type r = R.t
