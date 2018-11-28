Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope list.

Section Digraph.
  Variables (ChnT: Set)
            (chn_dec: forall c1 c2: ChnT, {c1 = c2} + {c1 <> c2}).
  
  (* NOTE: each object or queue is represented as a vertex. *)
  Definition vertices := list IdxT.

  (* NOTE: each channel id ([edge_chn]) should be unique through the entire graph.
   * See [WfDigraph] below for details. *)
  Record edge :=
    { edge_from: option IdxT;
      edge_chn: ChnT;
      edge_to: option IdxT
    }.

  Definition createEdge (v1: IdxT) (c: ChnT) (v2: IdxT) :=
    Build_edge (Some v1) c (Some v2).
  
  Definition edge_dec: forall e1 e2:edge, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
    - apply (option_dec eq_nat_dec).
    - apply (option_dec eq_nat_dec).
  Defined.

  Definition edge_eq (e1 e2: edge): bool :=
    if edge_dec e1 e2 then true else false.
  
  Definition edges := list edge.

  Record digraph :=
    { dg_vs: vertices;
      dg_es: edges
    }.

  Definition emptyDigraph :=
    {| dg_vs := nil; dg_es := nil |}.
  
  Definition WfDigraph (dg: digraph) :=
    NoDup (dg_vs dg) /\
    NoDup (map edge_chn (dg_es dg)).

  Definition singleton (v: IdxT) :=
    {| dg_vs := [v]; dg_es := nil |}.
  
  Definition connect (dg1: digraph) (ces: edges) (dg2: digraph) :=
    {| dg_vs := dg_vs dg1 ++ dg_vs dg2;
       dg_es := dg_es dg1 ++ dg_es dg2 ++ ces |}.

  Fixpoint connectMany (dg: digraph) (conns: list (edges * digraph)) :=
    match conns with
    | nil => dg
    | conn :: conns' =>
      connectMany (connect dg (fst conn) (snd conn)) conns'
    end.

  Definition isEdgeOf (e: edge) (from to: option IdxT) :=
    if option_dec eq_nat_dec (edge_from e) from
    then if option_dec eq_nat_dec (edge_to e) to
         then true
         else false
    else false.

  Definition edgesOf (di: digraph) (from to: option IdxT) :=
    filter (fun e => isEdgeOf e from to) (dg_es di).

End Digraph.

Section DTree.

  Inductive DTree :=
  | Leaf: DTree
  | Node: IdxT -> list ((list IdxT (* upward edges *) *
                         list IdxT (* downward edges *)) *
                        DTree (* child *)) -> DTree.

  Definition rootOf (gtr: DTree): option IdxT :=
    match gtr with
    | Leaf => None
    | Node root _ => Some root
    end.

  Definition childrenOf (gtr: DTree): list DTree :=
    match gtr with
    | Leaf => nil
    | Node _ cs => map snd cs
    end.

  (* Fixpoint flatten (gtr: DTree): list DTree := *)
  (*   match gtr with *)
  (*   | Leaf => nil *)
  (*   | Node root cs => *)
  (*     Node root cs :: List.concat (map (fun udc => flatten (snd udc)) cs) *)
  (*   end. *)

  (* Fixpoint childrenOfIdx' (fls: list DTree) (pidx: IdxT): list DTree := *)
  (*   match fls with *)
  (*   | nil => nil *)
  (*   | fl :: fls' => *)
  (*     if option_dec eq_nat_dec (rootOf fl) (Some pidx) *)
  (*     then childrenOf fl *)
  (*     else childrenOfIdx' fls' pidx *)
  (*   end. *)

  (* Definition childrenOfIdx (gtr: DTree) (pidx: IdxT): list DTree := *)
  (*   childrenOfIdx' (flatten gtr) pidx. *)

  (* Definition childrenIndsOfIdx (gtr: DTree) (pidx: IdxT): list IdxT := *)
  (*   oll (map rootOf (childrenOfIdx gtr pidx)). *)

  (* Fixpoint parentOfIdx' (fls: list DTree) (cidx: IdxT): option DTree := *)
  (*   match fls with *)
  (*   | nil => None *)
  (*   | fl :: fls' => *)
  (*     if in_dec (option_dec eq_nat_dec) (Some cidx) (map rootOf (childrenOf fl)) *)
  (*     then Some fl *)
  (*     else parentOfIdx' fls' cidx *)
  (*   end. *)

  (* Definition parentOfIdx (gtr: DTree) (cidx: IdxT): option DTree := *)
  (*   parentOfIdx' (flatten gtr) cidx. *)

  (* Definition parentIdxOfIdx (gtr: DTree) (cidx: IdxT): option IdxT := *)
  (*   (parentOfIdx gtr cidx) >>=[None] (fun ptr => rootOf ptr). *)

  Inductive Dir := DUp | DDown.
  Definition DChn := (Dir * IdxT)%type.

  Definition dchn_dec: forall c1 c2: DChn, {c1 = c2} + {c1 <> c2}.
  Proof.
    repeat decide equality.
  Defined.
  
  Definition edgesPC (pidx: IdxT) (cidx: option IdxT) (updowns: (list IdxT * list IdxT)) :=
    (map (fun eidx => Build_edge cidx (DUp, eidx) (Some pidx)) (fst updowns))
      ++ (map (fun eidx => Build_edge (Some pidx) (DDown, eidx) cidx) (snd updowns)).
  
  Fixpoint topoOfT (gtr: DTree): digraph DChn :=
    match gtr with
    | Leaf => emptyDigraph DChn
    | Node root cs =>
      connectMany
        (singleton DChn root)
        (map (fun eec =>
                (edgesPC root (rootOf (snd eec)) (fst eec),
                 topoOfT (snd eec))) cs)
    end.

  Variable (gtr: DTree).

  Local Notation topo := (topoOfT gtr).

  Definition EdgeIn (e: edge DChn) :=
    In e (dg_es topo).

  Definition isUpEdge (e: edge DChn) :=
    match fst e.(edge_chn) with
    | DUp => true
    | DDown => false
    end.

  Definition isDownEdge (e: edge DChn) :=
    match fst e.(edge_chn) with
    | DUp => false
    | DDown => true
    end.

  Definition upEdgesFrom (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_from) (Some oidx)
              then isUpEdge e
              else false) (dg_es topo).

  Definition upEdgesTo (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_to) (Some oidx)
              then isUpEdge e
              else false) (dg_es topo).

  Definition downEdgesFrom (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_from) (Some oidx)
              then isDownEdge e
              else false) (dg_es topo).

  Definition downEdgesTo (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_to) (Some oidx)
              then isDownEdge e
              else false) (dg_es topo).
  
End DTree.

Close Scope list.

