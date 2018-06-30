Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

Section Digraph.

  Definition vertex := IdxT.
  Definition vertices := list vertex.

  Definition channel := IdxT.
  Definition channels := list channel.
  
  Definition edge := (channel * (vertex * vertex))%type.
  Definition edgeChn (e: edge) := fst e.
  Definition edgeFrom (e: edge) := fst (snd e).
  Definition edgeTo (e: edge) := snd (snd e).

  Definition edges := list edge.

  Record digraph :=
    { dg_vs: vertices; dg_es: edges }.

  (** A highest level TODO: reflect transactional behaviors to
   * digraph paths and reason about them. 
   *
   * An [Atomic] step --> exists a path
   *
   * A complete lock --> cut
   * --> no paths passing that vertex
   * --> each path belongs to either one of two categories.
   *
   * A "half" lock --> nothing to say? Correctness not by locks
   * and topology; instead by pre/postcondition reasoning.
   *)

  Definition Bipartite (dg: digraph) (vs1 vs2: vertices) (cs: channels) :=
    forall v1 v2,
      In v1 vs1 -> In v2 vs2 ->
      exists c, In c cs /\
                In (c, (v1, v2)) (dg_es dg).
  
  Inductive Multipath (dg: digraph):
    vertex (* initial vertex *) ->
    vertices (* all involved vertices *) -> 
    channels (* all involved channels *) ->
    vertices (* end vertices *) -> Prop :=
  | MultipathNil: forall v, Multipath dg v [v] nil [v]
  | MultipathCons:
      forall iv vs cs ends es ncs nes,
        Multipath dg iv vs cs ends ->
        es <> nil ->
        SubList es ends ->
        Bipartite dg es nes ncs ->
        Multipath dg iv (vs ++ nes) (cs ++ ncs)
                  (removeL eq_nat_dec ends es ++ nes).

End Digraph.

(** Tree structure with (possibly-)multiple channels between nodes. *)
Section CTree.

  (* Structure definitions *)

  Inductive Tree :=
  | Node: IdxT -> list Tree -> Tree.

  Record Channel :=
    { chn_midx: IdxT;
      chn_from: IdxT;
      chn_to: IdxT
    }.

  Definition Channels := list Channel.

  Record CTree :=
    { ctr_tr: Tree;
      ctr_chns: Channels
    }.

  (* Utilities *)

  Fixpoint trOIndsOf (tr: Tree) :=
    match tr with
    | Node i chd =>
      i :: concat (map trOIndsOf chd)
    end.

  Definition trCurOIdxOf (tr: Tree) :=
    match tr with
    | Node i _ => i
    end.

  Definition trChildrenOf (tr: Tree) :=
    match tr with
    | Node _ chd => chd
    end.

  Definition TreeWfOInds (tr: Tree) := NoDup (trOIndsOf tr).

  Fixpoint trIterate (f: Tree -> bool) (tr: Tree) :=
    if f tr
    then Some tr
    else match tr with
         | Node i chd =>
           (fix trIterateL (trs: list Tree) :=
              match trs with
              | nil => None
              | tr :: trs' =>
                if f tr then Some tr else trIterateL trs'
              end) chd
         end.

  Fixpoint getThis (tr: Tree) (idx: IdxT): option Tree :=
    trIterate (fun tr =>
                 if trCurOIdxOf tr ==n idx
                 then true else false) tr.

  Fixpoint getParent (tr: Tree) (idx: IdxT): option Tree :=
    trIterate (fun tr =>
                 if idx ?<n (map trCurOIdxOf (trChildrenOf tr))
                 then true else false) tr.

  Definition chnsFromTo (chns: Channels) (from to: IdxT): Channels :=
    filter (fun chn =>
              if chn_from chn ==n from then
                if chn_to chn ==n to then true
                else false
              else false) chns.

  Definition chnsFromParent (ctr: CTree) (this: IdxT): list IdxT :=
    match getParent (ctr_tr ctr) this with
    | Some ptr => map chn_midx (chnsFromTo (ctr_chns ctr) (trCurOIdxOf ptr) this)
    | None => nil
    end.

  Definition isFromParent (ctr: CTree) (this: IdxT) (midx: IdxT): bool :=
    if in_dec eq_nat_dec midx (chnsFromParent ctr this)
    then true
    else false.
  
  Definition chnsFromChildren (ctr: CTree) (this: IdxT): list IdxT :=
    match getThis (ctr_tr ctr) this with
    | Some (Node _ chd) =>
      concat (map (fun c => map chn_midx (chnsFromTo (ctr_chns ctr) (trCurOIdxOf c) this)) chd)
    | None => nil
    end.
  
  Definition isFromChild (ctr: CTree) (this: IdxT) (midx: IdxT): bool :=
    if in_dec eq_nat_dec midx (chnsFromChildren ctr this)
    then true
    else false.

  (** Forwardings *)

  Definition getParentFwds (tr: Tree) (this: IdxT): list (IdxT * list IdxT) :=
    match getThis tr this with
    | Some ttr =>
      match getParent tr this with
      | Some ptr => (trCurOIdxOf ptr, removeL eq_nat_dec (trOIndsOf tr) (trOIndsOf ttr)) :: nil
      | None => nil
      end
    | None => nil
    end.

  Definition getChildrenFwds (tr: Tree) (fch this: IdxT): list (IdxT * list IdxT) :=
    match getThis tr this with
    | Some ttr =>
      match ttr with
      | Node _ chd =>
        filter (fun ii => if fst ii ==n fch then false else true)
               (map (fun c => (trCurOIdxOf c, trOIndsOf c)) chd)
      end
    | None => nil
    end.

  Definition getFwds (tr: Tree) (fch this: IdxT): list (IdxT * list IdxT) :=
    getParentFwds tr this ++ getChildrenFwds tr fch this.

End CTree.

