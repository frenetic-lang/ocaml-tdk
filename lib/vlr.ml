open S

module Make(V:HashCmp)(L:Lattice)(R:Result) = struct
  type v = V.t * L.t
  type r = R.t

  type d
    = Leaf   of r
    | Branch of V.t * L.t * t * t
  and t
    = { id : int; d : d }
  (* A tree structure representing the decision diagram. The [Leaf] variant
   * represents a constant function. The [Branch(v, l, t, f)] represents an
   * if-then-else. When variable [v] takes on the value [l], then [t] should
   * hold. Otherwise, [f] should hold.
   *
   * [Branch] nodes appear in an order determined first by the total order on
   * the [V.t] value with with ties broken by the total order on [L.t]. The
   * least such pair should appear at the root of the diagram, with each child
   * nodes being strictly greater than their parent node. This invariant is
   * important both for efficiency and correctness.
   * *)

  let equal x y =
    x.id = y.id

  let rec to_string t = match t.d with
    | Leaf r             -> R.to_string r
    | Branch(v, l, t, f) -> Printf.sprintf "B(%s = %s, %s, %s)"
      (V.to_string v) (L.to_string l) (to_string t) (to_string f)

  type this_t = t

  (* This module implements a cache of decision diagrams using a weak hash
   * table. This is used to implement sharing of sub-diagrams, which will reduce
   * overall memory useage.
   *
   * NOTE: Code outside of this submodule should not construct a value of type
   * [t] directly. Instead, the code should construct a value of type [d] and
   * then call [M.get manager d], which will return a value of type [t]. If no
   * node exists in the cache, then it will be returned. Otherwise, a new
   * structure will be allocated with a fresh identifier. *)
  module M = struct
    module Table = Hashtbl.Make(struct
      type t = this_t

      let hash t =
        match t.d with
        | Leaf r ->
          (R.hash r) lsl 1
        | Branch(v, l, t, f) ->
          (1021 * (V.hash v) + 1031 * (L.hash l) + 1033 * t.id + 1039 * f.id) lor 0x1

      let equal a b =
        match a.d, b.d with
        | Leaf r1, Leaf r2 -> R.compare r1 r2 = 0
        | Branch(vx, lx, tx, fx), Branch(vy, ly, ty, fy) ->
          V.compare vx vy = 0 && tx.id = ty.id && fx.id = fy.id
            && L.compare lx ly = 0
        | _, _ -> false
    end)

    type t = { table : this_t Table.t; mutable sym : int }

    let create size = { table = Table.create size; sym = 1 }
    let clear t = Table.clear t.table

    let gensym t =
      let s = t.sym in
      t.sym <- t.sym + 1;
      s

    let get t d =
      try Table.find t.table { id = 0; d }
      with Not_found ->
        Table.add t.table { id = gensym t; d };
        { id = gensym t; d }

    let remove t d =
      Table.remove t.table { id = 0; d }
  end

  let manager = M.create 10

  let mk_leaf r =
    M.get manager (Leaf r)

  let mk_branch v l t f =
    (* When the ids of the diagrams are equal, then the diagram will take on the
       same value regardless of variable assignment. The node that's being
       constructed can therefore be eliminated and replaced with one of the
       sub-diagrams, which are identical.

       If the ids are distinct, then the node has to be constructed and assigned
       a new id. *)
    if equal t f then begin
      t
    end else
      M.get manager (Branch(v, l, t, f))

  let rec fold g h t = match t.d with
    | Leaf r -> g r
    | Branch(v, l, t, f) ->
      h (v, l) (fold g h t) (fold g h f)

  let rec iter ?(order=`Pre) g h t = match t.d with
    | Leaf r -> g r
    | Branch(v, l, t, f) ->
      match order with
      | `Pre ->
        h (v, l) t f;
        iter ~order g h t;
        iter ~order g h f
      | `Post ->
        iter ~order g h t;
        iter ~order g h f;
        h (v, l) t f

  let const r = mk_leaf r
  let atom (v, l) t f = mk_branch v l (const t) (const f)

  let restrict lst =
    let rec loop xs u =
      match xs, u.d with
      | []          , _
      | _           , Leaf _ -> u
      | (v,l) :: xs', Branch(v', l', t, f) ->
        match V.compare v v' with
        |  0 -> if L.subset_eq l l' then loop xs' t else loop xs f
        | -1 -> loop xs' u
        |  1 -> mk_branch v' l' (loop xs t) (loop xs f)
        |  _ -> assert false
    in
    loop (List.sort (fun (u, _) (v, _) -> V.compare u v) lst)

  let peek t = match t.d with
    | Leaf r   -> Some r
    | Branch _ -> None

  let rec map_r g = fold
    (fun r          -> const (g r))
    (fun (v, l) t f -> mk_branch v l t f)

  let rec prod x y =
    match x.d, y.d with
    | Leaf r, _      ->
      if R.(compare r zero) = 0 then x
      else if R.(compare r one) = 0 then y
      else map_r (R.prod r) y
    | _     , Leaf r ->
      if R.(compare zero r) = 0 then y
      else if R.(compare one r) = 0 then x
      else map_r (fun x -> R.prod x r) x
    | Branch(vx, lx, tx, fx), Branch(vy, ly, ty, fy) ->
      begin match V.compare vx vy with
      |  0 ->
        begin match L.meet ~tight:true lx ly with
        | Some(l) -> mk_branch vx l (prod tx ty) (prod fx fy)
        | None    ->
          begin match L.compare lx ly with
          |  0 -> assert false
          | -1 -> mk_branch vx lx (prod tx (restrict [(vx, lx)] y)) (prod fx y)
          |  1 -> mk_branch vy ly (prod (restrict [(vy, ly)] x) ty) (prod x fy)
          |  _ -> assert false
          end
        end
      | -1 -> mk_branch vx lx (prod tx y) (prod fx y)
      |  1 -> mk_branch vy ly (prod x ty) (prod x fy)
      |  _ -> assert false
      end

  let rec sum x y =
    match x.d, y.d with
    | Leaf r, _      ->
      if R.(compare r zero) = 0 then y
      else map_r (R.sum r) y
    | _     , Leaf r ->
      if R.(compare zero r) = 0 then x
      else map_r (fun x -> R.sum x r) x
    | Branch(vx, lx, tx, fx), Branch(vy, ly, ty, fy) ->
      begin match V.compare vx vy with
      |  0 ->
        begin match L.join ~tight:true lx ly with
        | Some(l) -> mk_branch vx l (sum tx ty) (sum fx fy)
        | None    ->
          begin match L.compare lx ly with
          |  0 -> assert false
          | -1 -> mk_branch vx lx (sum tx (restrict [(vx, lx)] y)) (sum fx y)
          |  1 -> mk_branch vy ly (sum (restrict [(vy, ly)] x) ty) (sum x fy)
          |  _ -> assert false
          end
        end
      | -1 -> mk_branch vx lx (sum tx y) (sum fx y)
      |  1 -> mk_branch vy ly (sum x ty) (sum x fy)
      |  _ -> assert false
      end

  let rec support t =
    (* XXX(seliopou): keep track of diagram size and use that to initialize the
     * hashtable appropriately. *)
    let s = Hashtbl.create ~random:true 10 in
    iter (fun _ -> ()) (fun v _ _ -> Hashtbl.replace s v ()) t;
    Hashtbl.fold (fun v () acc -> v :: acc) s []

end
