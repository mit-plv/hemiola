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
    
    (** A highest level TODO: reflect transactional behaviors to
     * digraph paths and reason about them. 
     *
     * An [Atomic] step --> exists a path
     *
     * A complete lock --> cut
     * --> no paths passing that IdxT
     * --> each path belongs to either one of two categories.
     *
     * A "half" lock --> nothing to say? Correctness not by locks
     * and topology; instead by pre/postcondition reasoning.
     *)
    Inductive Multipath (dg: digraph):
      edges (* initial edges *) ->
      edges (* all involved edges *) ->
      vertices (* all involved vertices *) ->
      edges (* end edges *) -> Prop :=
    | MultipathNil: forall es, Multipath dg es es nil es
    | MultipathDiv:
        forall ies es vs ees e des,
          Multipath dg ies es vs ees ->
          In e ees -> edge_to e <> None ->
          des <> nil -> NoDup (map edge_to des) ->
          Forall (fun de => edge_from de = edge_to e) des ->
          Multipath dg ies (es ++ des) (vs ++ o2l (edge_to e))
                    (removeOnce edge_dec e ees ++ des)
    | MultipathCons:
        forall ies es vs ees e ces,
          Multipath dg ies es vs ees ->
          SubList ces ees -> edge_from e <> None ->
          ces <> nil -> NoDup (map edge_from ces) ->
          Forall (fun ce => edge_to ce = edge_from e) ces ->
          Multipath dg ies (es ++ [e])
                    (oapp vs (map edge_from ces))
                    (removeL edge_dec ees ces ++ [e]).
    
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

    (* Definition TreeWfOInds (tr: Tree) := NoDup (trOIndsOf tr). *)

    (* Fixpoint trIterate (f: Tree -> bool) (tr: Tree) := *)
    (*   if f tr *)
    (*   then Some tr *)
    (*   else match tr with *)
    (*        | Node i chd => *)
    (*          (fix trIterateL (trs: list Tree) := *)
    (*             match trs with *)
    (*             | nil => None *)
    (*             | tr :: trs' => *)
    (*               if f tr then Some tr else trIterateL trs' *)
    (*             end) chd *)
    (*        end. *)

    (* Fixpoint getThis (tr: Tree) (idx: IdxT): option Tree := *)
    (*   trIterate (fun tr => *)
    (*                if trCurOIdxOf tr ==n idx *)
    (*                then true else false) tr. *)

    (* Fixpoint getParent (tr: Tree) (idx: IdxT): option Tree := *)
    (*   trIterate (fun tr => *)
    (*                if idx ?<n (map trCurOIdxOf (trChildrenOf tr)) *)
    (*                then true else false) tr. *)

    (* Definition chnsFromTo (chns: Channels) (from to: IdxT): Channels := *)
    (*   filter (fun chn => *)
    (*             if chn_from chn ==n from then *)
    (*               if chn_to chn ==n to then true *)
    (*               else false *)
    (*             else false) chns. *)

    (* Definition chnsFromParent (ctr: CTree) (this: IdxT): list IdxT := *)
    (*   match getParent (ctr_tr ctr) this with *)
    (*   | Some ptr => map chn_midx (chnsFromTo (ctr_chns ctr) (trCurOIdxOf ptr) this) *)
    (*   | None => nil *)
    (*   end. *)

    (* Definition isFromParent (ctr: CTree) (this: IdxT) (midx: IdxT): bool := *)
    (*   if in_dec eq_nat_dec midx (chnsFromParent ctr this) *)
    (*   then true *)
    (*   else false. *)
    
    (* Definition chnsFromChildren (ctr: CTree) (this: IdxT): list IdxT := *)
    (*   match getThis (ctr_tr ctr) this with *)
    (*   | Some (Node _ chd) => *)
    (*     concat (map (fun c => map chn_midx (chnsFromTo (ctr_chns ctr) (trCurOIdxOf c) this)) chd) *)
    (*   | None => nil *)
    (*   end. *)
    
    (* Definition isFromChild (ctr: CTree) (this: IdxT) (midx: IdxT): bool := *)
    (*   if in_dec eq_nat_dec midx (chnsFromChildren ctr this) *)
    (*   then true *)
    (*   else false. *)

    (* (** Forwardings *) *)

    (* Definition getParentFwds (tr: Tree) (this: IdxT): list (IdxT * list IdxT) := *)
    (*   match getThis tr this with *)
    (*   | Some ttr => *)
    (*     match getParent tr this with *)
    (*     | Some ptr => (trCurOIdxOf ptr, removeL eq_nat_dec (trOIndsOf tr) (trOIndsOf ttr)) :: nil *)
    (*     | None => nil *)
    (*     end *)
    (*   | None => nil *)
    (*   end. *)

    (* Definition getChildrenFwds (tr: Tree) (fch this: IdxT): list (IdxT * list IdxT) := *)
    (*   match getThis tr this with *)
    (*   | Some ttr => *)
    (*     match ttr with *)
    (*     | Node _ chd => *)
    (*       filter (fun ii => if fst ii ==n fch then false else true) *)
    (*              (map (fun c => (trCurOIdxOf c, trOIndsOf c)) chd) *)
    (*     end *)
    (*   | None => nil *)
    (*   end. *)

    (* Definition getFwds (tr: Tree) (fch this: IdxT): list (IdxT * list IdxT) := *)
    (*   getParentFwds tr this ++ getChildrenFwds tr fch this. *)

  End GTree.

End VertexParam.
  
(*! TODO: move to some other file like TopologyFacts.v *)
(* Require Import Serial. *)

(** TODO: what is the digraph for a given [System]? 
 * Definitely a tree structure is required to figure out parent-child relation
 * during defining a protocol.
 *)
(* Lemma atomic_multipath: *)
(*   forall sys st1 hst st2, *)
(*     steps step_m sys st1 hst st2 -> *)
(*     forall inits ins outs eouts, *)
(*       Atomic inits ins hst outs eouts -> *)
(*       Multipath dg (idsOf inits) *)

(*! Moving ends here. *)

