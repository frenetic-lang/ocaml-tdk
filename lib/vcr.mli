open S

(** Variable-Constant-Result *)
module Make(V:HashCmp)(C:HashCmp)(R:Result) : DD
  with type v = V.t * C.t
   and type r = R.t
