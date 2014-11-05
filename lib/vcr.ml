open S

module Make(V:HashCmp)(C:HashCmp)(R:Result) = struct
  module L = struct
    include C

    let subset_eq a b =
      C.compare a b = 0

    let meet ?tight a b =
      if subset_eq a b then Some(a) else None

    let join ?tight a b =
      if subset_eq a b then Some(a) else None
  end

  include Vlr.Make(V)(L)(R)
end
