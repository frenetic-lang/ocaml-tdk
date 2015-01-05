open S

module type TABLE = sig
  val clear : unit -> unit
  type value
  val get : value -> int
  val unget : int -> value
end

module type TABLE_VALUE = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
end

module PersistentTable (Value : TABLE_VALUE) : TABLE
  with type value = Value.t = struct

  module T = Hashtbl.Make (Value)
  (* TODO(arjun): Since these are allocated contiguously, it would be
     better to use a growable array ArrayList<Int> *)
  module U = Hashtbl.Make(struct
    type t = int
    let hash n = n
    let equal x y = x = y
  end)

  type value = Value.t

  let tbl : int T.t = T.create 100
  let untbl : value U.t = U.create 100

  let idx = ref 0

  let clear () =
    T.clear tbl;
    U.clear untbl;
    idx := 0

  let gensym () =
    let r = !idx in
    idx := !idx + 1;
    r

  let get (v : value) =
    try
      T.find tbl v
    with Not_found ->
      begin
        let n = gensym () in
        T.add tbl v n;
        U.add untbl n v;
        n
      end

  let unget (idx : int) : value = U.find untbl idx

end

module Make(V:HashCmp)(L:Lattice)(R:Result) = struct
  type v = V.t * L.t
  type r = R.t

  type d
    = Leaf of r
    | Branch of V.t * L.t * int * int

  type t = int
  module T = PersistentTable(struct
      type t = d

      let hash t = match t with
        | Leaf r ->
          (R.hash r) lsl 1
        | Branch(v, l, t, f) ->
          (1021 * (V.hash v) + 1031 * (L.hash l) + 1033 * t + 1039 * f) lor 0x1

      let equal a b = match a, b with
        | Leaf r1, Leaf r2 -> R.compare r1 r2 = 0
        | Branch(vx, lx, tx, fx), Branch(vy, ly, ty, fy) ->
          V.compare vx vy = 0 && tx = ty && fx = fy
            && L.compare lx ly = 0
        | _, _ -> false
    end)

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

  let equal x y = x = y (* comparing ints *)

  let rec to_string t = "to_string broken" (* match T.get t with
    | Leaf r             -> R.to_string r
    | Branch(v, l, t, f) -> Printf.sprintf "B(%s = %s, %s, %s)"
      (V.to_string v) (L.to_string l) (to_string t)
      (to_string (T.get f))
 *)
  let clear_cache () = T.clear ()

  let mk_leaf r = T.get (Leaf r)


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
      T.get (Branch(v, l, t, f))

  let rec fold g h t = match T.unget t with
    | Leaf r -> g r
    | Branch(v, l, t, f) ->
      h (v, l) (fold g h t) (fold g h f)

  let const r = mk_leaf r
  let atom (v, l) t f = mk_branch v l (const t) (const f)

  let node_min t1 t2 = match (t1, t2) with
  | Leaf _, Leaf _ -> (t1, t2) (* constants at same rank since they can't be ordered *)
  | Leaf _, _ -> (t2, t1)
  | _, Leaf _ -> (t1, t2)
  | Branch (v1, l1, _, _), Branch (v2, l2, _, _) -> match V.compare v1 v2 with
    | -1 -> (t1, t2)
    | 1 -> (t2, t1)
    | 0 -> if L.subset_eq l1 l2 then
             (t1, t2)
           else if L.subset_eq l2 l1 then
             (t2, t1)
           else
             (* The Spiros case. I don't think it matters which we pick *)
             (t1, t2)
    | _ -> assert false

  (* TODO(arjun): This would be easier to implement if variables were explicitly
     ranked *)
  let make_cutoff (cutoff : t) : t -> bool -> t = match T.unget cutoff with
    | Leaf _ -> fun d _ -> d
    | Branch (x, v, _, _) -> fun node dir ->
        match T.unget node with
        | Leaf _ -> node
        | Branch (x', v', tru, fls) ->
          match V.compare x x' with
          | -1 -> node (* we haven't reached a decision on x' yet *)
          | 1 -> assert false (* should have picked min *)
          | 0 -> begin match L.subset_eq v v', L.subset_eq v' v with
            (* identical, just like a BDD *)
            | (true, true) -> if dir then tru else fls
            (* v < v', so if x \in v then x \in v' too
                          if x \notin v, then we can't refine *)
            | (true, false) -> if dir then tru else node
            (* v' < v, so if x \notin v then x \notin v'
                          if x \in v then we can't refine *)
            | (false, true) -> if dir then node else fls
            (* incomparable, so knowing x \in v or x \notin v doesn't let
              us refine at all *)
            | (false, false) -> node
            end
          | _ -> assert false

  module H = Core.Std.Hashtbl.Poly

  let apply2 f u1 u2 =
    let tbl : (int * int, int) H.t = H.create () in
    let rec apply2 u v =
      H.find_or_add tbl (u, v) ~default:(fun () -> apply2' u v)
    and apply2' u1 u2 = match (T.unget u1, T.unget u2) with
      | Leaf c1, Leaf c2 -> mk_leaf (f c1 c2)
      | t1, t2->
        let (min_t, _) = node_min t1 t2 in
        let cutoff = make_cutoff (T.get min_t) in
        match min_t with
        | Leaf _ -> assert false (* if this was the min, then we should be at base case *)
        | Branch (x, v, _, _) ->
          mk_branch x v
            (apply2 (cutoff u1 true) (cutoff u2 true))
            (apply2 (cutoff u1 false) (cutoff u2 false))
    in apply2 u1 u2

  let rec apply3 f u1 u2 u3 = match (T.unget u1, T.unget u2, T.unget u3) with
    | Leaf c1, Leaf c2, Leaf c3 -> mk_leaf (f c1 c2 c3)
    | t1, t2, t3 ->
      let (min_t, _) = node_min t2 t3 in
      let (min_t, _) = node_min t1 min_t in
      let cutoff = make_cutoff (T.get min_t) in
      match min_t with
      | Leaf _ -> assert false (* if this was the min, then we should be at base case *)
      | Branch (x, v, _, _) ->
        mk_branch x v
          (apply3 f (cutoff u1 true) (cutoff u2 true) (cutoff u3 true))
          (apply3 f (cutoff u1 false) (cutoff u2 false) (cutoff u3 false))

  let rec map_values f u = match T.unget u with
    | Leaf c -> mk_leaf (f c)
    | Branch (x, v, tru, fls) ->
      mk_branch x v (map_values f tru) (map_values f fls)

  let restrict lst =
    let rec loop xs u =
      match xs, T.unget u with
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

  let peek t = match T.unget t with
    | Leaf r   -> Some r
    | Branch _ -> None

  let rec map_r g = fold
    (fun r          -> const (g r))
    (fun (v, l) t f -> mk_branch v l t f)

  let rec prod x y =
    match T.unget x, T.unget y with
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

  let sum_generalized f x y =
    let tbl : (int * int, int) H.t = H.create () in
    let rec sum x y =
      H.find_or_add tbl (x, y) ~default:(fun () -> sum' x y)
    and sum' x y =
      match T.unget x, T.unget y with
      | Leaf r, _      ->
        if R.(compare r zero) = 0 then y
        else map_r (f r) y
      | _     , Leaf r ->
        if R.(compare zero r) = 0 then x
        else map_r (fun x -> f x r) x
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
    in sum x y

  let sum = sum_generalized R.sum


  let compressed_size (node : t) : int =
    let open Core.Std in
    let rec f (node : t) (seen : Int.Set.t) =
      if Int.Set.mem seen node then
        (0, seen)
      else
        match T.unget node with
        | Leaf _ -> (1, Int.Set.add seen node)
        | Branch (_, _, hi, lo) ->
          (* Due to variable-ordering, there is no need to add node.id to seen
             in the recursive calls *)
          let (hi_size, seen) = f hi seen in
          let (lo_size, seen) = f lo seen in
          (1 + hi_size + lo_size, Int.Set.add seen node) in
    let (size, _) = f node Int.Set.empty in
    size

  let rec uncompressed_size (node : t) : int = match T.unget node with
    | Leaf _ -> 1
    | Branch (_, _, hi, lo) -> 1 + uncompressed_size hi + uncompressed_size lo

  module VH = Hashtbl.Make(struct
    type t = v

    let equal (v1, l1) (v2, l2) =
      V.compare v1 v2 = 0 && L.compare l1 l2 = 0

    let hash (v, l) =
      191 * (V.hash v) + 877 * (L.hash l)
  end)

  let to_dot t =
    let open Format in
    let buf = Buffer.create 200 in
    let fmt = formatter_of_buffer buf in
    let seen = Hashtbl.create ~random:true 20 in
    let rank = VH.create 20 in
    pp_set_margin fmt (1 lsl 29);
    fprintf fmt "digraph tdk {@\n";
    let rec loop t =
      if not (Hashtbl.mem seen t) then begin
        Hashtbl.add seen t ();
        match T.unget t with
        | Leaf r ->
          fprintf fmt "%d [shape=box label=\"%s\"];@\n" t (R.to_string r)
        | Branch(v, l, a, b) ->
          begin
            try Hashtbl.add (VH.find rank (v, l)) t ()
            with Not_found ->
              let s = Hashtbl.create ~random:true 10 in
              Hashtbl.add s t ();
              VH.add rank (v, l) s
          end;
          fprintf fmt "%d [label=\"%s = %s\"];@\n"
            t (V.to_string v) (L.to_string l);
          fprintf fmt "%d -> %d;@\n" t a;
          fprintf fmt "%d -> %d [style=\"dashed\"];@\n" t b;
          loop a;
          loop b
      end
    in
    loop t;
    VH.iter
      (fun _ s ->
         fprintf fmt "{rank=same; ";
         Hashtbl.iter (fun x () -> fprintf fmt "%d " x) s;
         fprintf fmt ";}@\n")
      rank;
    fprintf fmt "}@.";
    Buffer.contents buf

end
