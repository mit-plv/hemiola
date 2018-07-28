Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

Section VertexParam.

  Section Digraph.
    
    (* NOTE: each object or queue is represented as a vertex. *)
    Definition vertices := list IdxT.

    Record edge :=
      { edge_from: option IdxT;
        edge_chn: IdxT;
        edge_to: option IdxT
      }.

    Definition createEdge (v1: IdxT) (c: IdxT) (v2: IdxT) :=
      Build_edge (Some v1) c (Some v2).
    
    Definition edge_dec: forall e1 e2:edge, {e1 = e2} + {e1 <> e2}.
    Proof.
      repeat decide equality.
    Defined.
    
    Definition edges := list edge.

    Record digraph :=
      { dg_vs: vertices;
        dg_es: edges
      }.

    (* Definition WfDigraph (dg: digraph) := *)
    (*   NoDup (dg_vs dg) /\ NoDup (dg_es dg). *)

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
        
  End Digraph.

  (** Tree structure where the corresponding digraph is indexed. *)
  Section GTree.

    (* Inductive GTree: digraph -> Type := *)
    (* | Node: *)
    (*     forall (root: IdxT) *)
    (*            (tcs: list {dg: digraph & GTree dg}) *)
    (*            (gcs: list (edges * digraph)), *)
    (*       map (@projT1 _ _) tcs = map snd gcs -> *)
    (*       GTree (connectMany (singleton root) gcs). *)

    Inductive GTree :=
    | Node: IdxT -> list (edges * GTree) -> GTree.

    Definition rootOf (gtr: GTree) :=
      match gtr with
      | Node root _ => root
      end.
    
    Fixpoint digraphOfT (gtr: GTree) :=
      match gtr with
      | Node root cs =>
        connectMany
          (singleton root)
          (map (fun et => (fst et, digraphOfT (snd et))) cs)
      end.

    (* Each edge is pointing its parent. *) 
    Fixpoint topoOfT (gtr: GTree) :=
      match gtr with
      | Node root cs =>
        connectMany
          (singleton root)
          (map (fun et =>
                  ([Build_edge (Some (rootOf (snd et))) 0 (Some root)],
                   topoOfT (snd et))) cs)
      end.

    Definition getParent (gtr: GTree) (cur: IdxT): option IdxT :=
      let topo := topoOfT gtr in
      hd_error (oll (map (fun e =>
                            if option_dec eq_nat_dec (edge_from e) (Some cur)
                            then edge_to e
                            else None) (dg_es topo))).

    Definition isParent (gtr: GTree) (cur parent: IdxT) :=
      if option_dec eq_nat_dec (getParent gtr cur) (Some parent)
      then true else false.

  End GTree.

End VertexParam.

