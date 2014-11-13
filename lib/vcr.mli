open S

(** Variable-Constant-Result
    This module implements a variant of a binary decision diagrams. Rather than
    representing boolean-valued functions over boolean variables, this data
    structure represents functions that take on values in a semi-ring, and whose
    variables are assigned values that are totally ordered.

    For example, using the module one can represent int-valued functions over n
    integer variables. *)
module Make(V:HashCmp)(C:HashCmp)(R:Result) : Diagram
  with type v = V.t * C.t
   and type r = R.t
