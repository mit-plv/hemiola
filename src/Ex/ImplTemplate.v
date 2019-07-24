Require Import List FMap Omega.
Require Import Common Index Topology Syntax.
Require Import RqRsTopo.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Inductive tree :=
| Node: list tree -> tree.

Section tree_ind_l.
  Variables (P: tree -> Prop)
            (f: forall l, Forall P l -> P (Node l)).

  Fixpoint tree_ind_l (t: tree): P t :=
    match t with
    | Node sts =>
      f (list_ind (Forall P) (Forall_nil P)
                  (fun st _ IHl => Forall_cons st (tree_ind_l st) IHl)
                  sts)
    end.

End tree_ind_l.

Definition rqUpIdx: nat := 0.
Definition rsUpIdx: nat := 1.
Definition downIdx: nat := 2.

Section IncMap.
  Context {A B: Type}.
  Variable f: A -> IdxT -> B.

  Fixpoint incMap (avs: list A) (baseIdx: IdxT) (ext: nat): list B :=
    match avs with
    | nil => nil
    | av :: avs' =>
      f av (baseIdx~>ext) :: incMap avs' baseIdx (S ext)
    end.

  Lemma incMap_In:
    forall al base ext b,
      In b (incMap al base ext) ->
      exists a ofs,
        nth_error al ofs = Some a /\ b = f a (base~>(ext + ofs)).
  Proof.
    induction al; simpl; intros; [exfalso; auto|].
    destruct H; subst.
    - exists a, 0; split; [reflexivity|].
      rewrite Nat.add_0_r; reflexivity.
    - specialize (IHal _ _ _ H).
      destruct IHal as [pa [ofs ?]]; dest; subst.
      exists pa, (S ofs); split; [assumption|].
      rewrite Nat.add_succ_r; reflexivity.
  Qed.

  Lemma incMap_nth_error:
    forall al base ext n b,
      nth_error (incMap al base ext) n = Some b ->
      exists a, nth_error al n = Some a /\ b = f a (base~>(ext + n)).
  Proof.
    induction al; simpl; intros; [destruct n; discriminate|].
    destruct n.
    - inv H; exists a; rewrite Nat.add_0_r; auto.
    - specialize (IHal _ _ _ _ H).
      destruct IHal as [na [? ?]]; subst.
      exists na; split; [assumption|].
      rewrite Nat.add_succ_r; reflexivity.
  Qed.

End IncMap.

(* NOTE: [c_li_indices] contains the root which is a main memory.
 * In order to access the main memory index, just use [rootOf].
 *
 * [tree] is general enough to represent memory structures that have an LLC
 * (last-level cache) just before the main memory. In this case the root will
 * have a single child that reflects to the LLC.
 *)
Record CIfc :=
  { c_li_indices: list IdxT;
    c_l1_indices: list IdxT;
    c_minds: list IdxT;
    c_merqs: list IdxT;
    c_merss: list IdxT
  }.

Definition emptyCIfc :=
  {| c_li_indices := nil; c_l1_indices := nil;
     c_minds := nil; c_merqs := nil; c_merss := nil |}.

Definition mergeCIfc (ci1 ci2: CIfc) :=
  {| c_li_indices := ci1.(c_li_indices) ++ ci2.(c_li_indices);
     c_l1_indices := ci1.(c_l1_indices) ++ ci2.(c_l1_indices);
     c_minds := ci1.(c_minds) ++ ci2.(c_minds);
     c_merqs := ci1.(c_merqs) ++ ci2.(c_merqs);
     c_merss := ci1.(c_merss) ++ ci2.(c_merss) |}.

Definition l1ExtOf (idx: IdxT): IdxT :=
  idx~>0.

Definition singletonDNode (idx: IdxT): DTree * CIfc :=
  let eidx := l1ExtOf idx in
  (DNode {| dmc_me := idx;
            dmc_ups := [idx~>rqUpIdx; idx~>rsUpIdx];
            dmc_downs := [idx~>downIdx] |}
         [DNode {| dmc_me := eidx;
                   dmc_ups := [eidx~>rqUpIdx; eidx~>rsUpIdx];
                   dmc_downs := [eidx~>downIdx] |} nil],
   {| c_li_indices := nil;
      c_l1_indices := [idx];
      c_minds := [idx~>rqUpIdx; idx~>rsUpIdx; idx~>downIdx];
      c_merqs := [eidx~>rqUpIdx];
      c_merss := [eidx~>downIdx] |}).

(** TODO: move to [ListSupport.v] *)
Definition nil_dec {A}: forall l: list A, {l = nil} + {l <> nil}.
Proof.
  intros; destruct l; [left; reflexivity|right; discriminate].
Defined.

Fixpoint tree2Topo (tr: tree) (curIdx: IdxT): DTree * CIfc :=
  match tr with
  | Node ctrs =>
    if nil_dec ctrs then singletonDNode curIdx
    else
      let stp := incMap tree2Topo ctrs curIdx 0 in
      let strs := map fst stp in
      let sci := fold_left mergeCIfc (map snd stp) emptyCIfc in
      (DNode {| dmc_me := curIdx;
                dmc_ups := [curIdx~>rqUpIdx; curIdx~>rsUpIdx];
                dmc_downs := [curIdx~>downIdx] |} strs,
       mergeCIfc
         {| c_li_indices := [curIdx];
            c_l1_indices := nil;
            c_minds := [curIdx~>rqUpIdx; curIdx~>rsUpIdx; curIdx~>downIdx];
            c_merqs := nil;
            c_merss := nil |}
         sci)
  end.

(* Eval compute in (tree2Topo (Node [Node [Node nil; Node nil]; *)
(*                                     Node [Node nil; Node nil]]) 0). *)

Definition rqUpFrom (cidx: IdxT): IdxT :=
  cidx~>rqUpIdx.
Definition rsUpFrom (cidx: IdxT): IdxT :=
  cidx~>rsUpIdx.
Definition downTo (cidx: IdxT): IdxT :=
  cidx~>downIdx.

(** TODO: use [None] when silent transactions are supported. *)
Definition addSilentUpRq (orq: ORq Msg) (mrss : list IdxT): ORq Msg :=
  orq +[upRq <- {| rqi_msg := {| msg_id := 0;
                                 msg_type := false;
                                 msg_value := VUnit |};
                   rqi_minds_rss := mrss;
                   rqi_midx_rsb := 0 |}].

