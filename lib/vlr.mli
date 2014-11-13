open S

(** Variable-Lattice-Result

    This module implements a variant of a binary decision diagrams. Rather than
    representing boolean-valued functions over boolean variables, this data
    structure represents functions that take on values in a semi-ring, and whose
    variables are assigned values from a lattice, i.e., that are partially
    ordered. *)
module Make(V:HashCmp)(L:Lattice)(R:Result) : Diagram
  with type v = V.t * L.t
   and type r = R.t
