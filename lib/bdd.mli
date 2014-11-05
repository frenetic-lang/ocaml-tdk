open S

(** Binary decision diagram. *)
module Make(V:HashCmp) : sig
  include DD
    with type v = V.t * bool
     and type r = bool

  val var : V.t -> t
  (** [var v] is equivalent to [atom (v, true) true false)] *)

  val neg : t -> t
  (** [neg t] returns a diagram representing the negation of [t] *)

  val tautology : t -> bool
  (** [tautology t] returns [true] if all paths in the diagram lead to [true]
      leaf nodes. In that case, the diagram will in fact be represented by a
      leaf node holding the value [true]. *)

  val falsehood : t -> bool
  (** [falsehood t] returns [true] if all paths in the diagram lead to [false]
      leaf nodes. In that case, the diagram will in fact be represented by a
      leaf node holding the value [false]. *)

end
