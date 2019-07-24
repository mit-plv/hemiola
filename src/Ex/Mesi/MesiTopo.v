Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector ListSupport Syntax Topology Semantics.
Require Import RqRsLang.

Require Import Ex.Spec Ex.SpecSv Ex.ImplTemplate Ex.Mesi.
Require Import Ex.Mesi.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** TODO: move to [RqRsLang.v] *)
Lemma initORqs_GoodORqsInit: forall oinds, GoodORqsInit (initORqs oinds).
Proof.
  red; intros.
  unfold initORqs.
  remember (M.empty (M.t (RqInfo Msg))) as m.
  assert (forall oidx, m@[oidx] >>=[True] (fun orq => orq = []))
    by (intros; subst; mred).
  clear Heqm.
  generalize dependent m.
  induction oinds; simpl; intros; [auto|].
  apply IHoinds.
  intros.
  mred; auto.
Qed.

(** TODO: move to [ListSupport.v] *)
Lemma collect_forall:
  forall {A B} P (f: A -> list B) al,
    (forall a, In a al -> Forall P (f a)) ->
    Forall P (collect f al).
Proof.
  induction al; intros; [constructor|].
  simpl; apply Forall_app.
  - apply H; left; reflexivity.
  - apply IHal; intros.
    apply H; right; assumption.
Qed.

Lemma collect_In:
  forall {A B} (f: A -> list B) al b,
    In b (collect f al) ->
    exists a, In a al /\ In b (f a).
Proof.
  induction al; intros; [dest_in|].
  simpl in H; apply in_app_or in H; destruct H.
  - eexists; split; [left; reflexivity|assumption].
  - specialize (IHal _ H).
    destruct IHal as [na [? ?]].
    eexists; split; [right; eassumption|assumption].
Qed.

Lemma collect_NoDup:
  forall {A B} (f: A -> list B) al,
    (forall a, In a al -> NoDup (f a)) ->
    (forall n1 n2 a1 a2,
        n1 <> n2 ->
        nth_error al n1 = Some a1 ->
        nth_error al n2 = Some a2 ->
        DisjList (f a1) (f a2)) ->
    NoDup (collect f al).
Proof.
  induction al; simpl; intros; [constructor|].
  apply NoDup_DisjList; auto.
  - apply IHal; auto.
    intros; apply H0 with (n1:= S n1) (n2:= S n2); auto.
  - clear -H0.
    assert (forall n na, nth_error al n = Some na ->
                         DisjList (f a) (f na)).
    { intros; apply H0 with (n1:= 0) (n2:= S n); auto. }
    assert (forall n1 n2 a1 a2,
               n1 <> n2 ->
               nth_error al n1 = Some a1 ->
               nth_error al n2 = Some a2 -> DisjList (f a1) (f a2)).
    { intros; apply H0 with (n1:= S n1) (n2:= S n2); auto. }
    clear H0.
    
    induction al; simpl; intros; [apply DisjList_nil_2|].
    apply DisjList_comm, DisjList_app_4; apply DisjList_comm.
    + apply H with (n:= 0); reflexivity.
    + apply IHal.
      * intros; apply H with (n:= S n); assumption.
      * intros; apply H1 with (n1:= S n1) (n2:= S n2); auto.
Qed.

Lemma incMap_In:
  forall {A B} (f: A -> IdxT -> B) al base ext b,
    In b (incMap f al base ext) ->
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
  forall {A B} (f: A -> IdxT -> B) al base ext n b,
    nth_error (incMap f al base ext) n = Some b ->
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

Lemma app_eq_compare:
  forall {A} (l m n o: list A),
    l ++ m = n ++ o ->
    exists p, (l = n ++ p /\ o = p ++ m) \/
              (n = l ++ p /\ m = p ++ o).
Proof.
  induction l; simpl; intros.
  - subst; eexists; right; eauto.
  - destruct n as [|b n].
    + simpl in *; subst.
      eexists; left; eauto.
    + simpl in H; inv H.
      specialize (IHl _ _ _ H2).
      destruct IHl as [p ?]; destruct H; dest; subst; [|eauto].
      eexists; left; split; reflexivity.
Qed.

Lemma nth_error_map_iff:
  forall {A B} (f: A -> B) (l: list A) (n: nat) (b: B),
    nth_error (map f l) n = Some b ->
    exists a, f a = b /\ nth_error l n = Some a.
Proof.
  induction l; simpl; intros; [destruct n; discriminate|].
  destruct n; [inv H; eauto|eauto].
Qed.

Lemma DisjList_spec_1:
  forall {A} (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
         (l1 l2: list A),
    (forall a, In a l1 -> ~ In a l2) ->
    DisjList l1 l2.
Proof.
  intros; red; intros.
  destruct (in_dec eq_dec e l1); auto.
Qed.

Lemma DisjList_spec_2:
  forall {A} (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
         (l1 l2: list A),
    (forall a, In a l2 -> ~ In a l1) ->
    DisjList l1 l2.
Proof.
  intros; red; intros.
  destruct (in_dec eq_dec e l2); auto.
Qed.
  
Lemma DisjList_map:
  forall {A B} (f: A -> B) (l1 l2: list A),
    DisjList (map f l1) (map f l2) ->
    DisjList l1 l2.
Proof.
  unfold DisjList; intros.
  specialize (H (f e)); destruct H.
  - left; intro Hx; elim H; apply in_map; assumption.
  - right; intro Hx; elim H; apply in_map; assumption.
Qed.

(** TODO: move to [Index.v] *)
Definition IdxPrefix (i1 i2: IdxT) :=
  exists ri, i2 = ri ++ i1.
Infix "~<" := IdxPrefix (at level 8).

Definition IdxDisj (i1 i2: IdxT) :=
  ~ IdxPrefix i1 i2 /\ ~ IdxPrefix i2 i1.
Infix "~*~" := IdxDisj (at level 8).

Definition IndsDisj (is1 is2: list IdxT) :=
  forall i1 i2, In i1 is1 -> In i2 is2 -> i1 ~*~ i2.

Lemma extendIdx_not_IdxPrefix:
  forall i e, ~ i~>e ~< i.
Proof.
  unfold extendIdx, IdxPrefix; intros.
  intro Hx; dest.
  replace (x ++ e :: i) with ((x ++ [e]) ++ i) in H
    by (rewrite <-app_assoc; reflexivity).
  remember (x ++ [e]) as l.
  assert (l <> nil) by (intro Hx; subst; destruct x; discriminate).
  clear Heql x e.
  generalize dependent l.
  induction i; simpl; intros.
  - rewrite app_nil_r in H; auto.
  - destruct l; [auto|].
    inv H.
    eapply IHi with (l:= l ++ [n]).
    + rewrite <-app_assoc; assumption.
    + destruct l; discriminate.
Qed.

Lemma IdxPrefix_refl: forall i, i ~< i.
Proof.
  unfold IdxPrefix; intros.
  exists nil; reflexivity.
Qed.

Lemma IdxPrefix_trans:
  forall i1 i2, i1 ~< i2 -> forall i3, i2 ~< i3 -> i1 ~< i3.
Proof.
  unfold IdxPrefix; intros; dest; subst.
  eexists; rewrite app_assoc; reflexivity.
Qed.

Lemma IdxPrefix_common:
  forall i1 i2 i, i1 ~< i -> i2 ~< i -> i1 ~< i2 \/ i2 ~< i1.
Proof.
  unfold IdxPrefix; intros; dest; subst.
  apply app_eq_compare in H0.
  destruct H0 as [p ?]; destruct H; dest; subst; eauto.
Qed.

Lemma IdxPrefix_disj_1:
  forall i1 i2, i1 ~*~ i2 -> forall ei1, i1 ~< ei1 -> ei1 ~*~ i2.
Proof.
  unfold IdxDisj; intros; dest.
  split.
  - intro Hx; elim H.
    eapply IdxPrefix_trans; eauto.
  - intro Hx.
    pose proof (IdxPrefix_common H0 Hx).
    destruct H2; auto.
Qed.

Lemma IdxPrefix_disj_2:
  forall i1 i2, i1 ~*~ i2 -> forall ei2, i2 ~< ei2 -> i1 ~*~ ei2.
Proof.
  unfold IdxDisj; intros; dest.
  split.
  - intro Hx.
    pose proof (IdxPrefix_common H0 Hx).
    destruct H2; auto.
  - intro Hx; elim H1.
    eapply IdxPrefix_trans; eauto.
Qed.

Lemma IdxDisj_not_eq:
  forall i1 i2, i1 ~*~ i2 -> i1 <> i2.
Proof.
  intros; intro Hx; subst.
  red in H; dest.
  elim H; apply IdxPrefix_refl.
Qed.

Lemma extendIdx_IdxDisj:
  forall bidx ext1 ext2,
    ext1 <> ext2 -> bidx~>ext1 ~*~ bidx~>ext2.
Proof.
  unfold extendIdx, IdxDisj, IdxPrefix; intros.
  split; intro; dest.
  - destruct x; [inv H0; auto|].
    apply (f_equal (@List.length _)) in H0.
    rewrite app_length in H0; simpl in H0.
    omega.
  - destruct x; [inv H0; auto|].
    apply (f_equal (@List.length _)) in H0.
    rewrite app_length in H0; simpl in H0.
    omega.
Qed.

Lemma IdxDisj_base_IndsDisj:
  forall bidx1 bidx2,
    bidx1 ~*~ bidx2 ->
    forall inds1 inds2,
      Forall (fun idx => bidx1 ~< idx) inds1 ->
      Forall (fun idx => bidx2 ~< idx) inds2 ->
      IndsDisj inds1 inds2.
Proof.
  intros.
  rewrite Forall_forall in H0, H1.
  red; intros.
  specialize (H0 _ H2); specialize (H1 _ H3).
  eapply IdxPrefix_disj_1; [|eassumption].
  eapply IdxPrefix_disj_2; [|eassumption].
  assumption.
Qed.

Lemma IndsDisj_DisjList:
  forall inds1 inds2, IndsDisj inds1 inds2 -> DisjList inds1 inds2.
Proof.
  unfold IndsDisj, DisjList; intros.
  destruct (in_dec idx_dec e inds1); [|auto].
  destruct (in_dec idx_dec e inds2); [|auto].
  specialize (H _ _ i i0).
  exfalso; eapply IdxDisj_not_eq; eauto.
Qed.

(** TODO: move to [ImplTemplate.v] *)
Lemma singletonDNode_inds_prefix_base:
  forall bidx,
    Forall (fun idx => bidx ~< idx)
           (indsOf (fst (singletonDNode bidx))).
Proof.
  intros; simpl.
  repeat constructor.
  - apply IdxPrefix_refl.
  - exists [0]; reflexivity.
Qed.

Lemma singletonDNode_chns_prefix_base:
  forall bidx,
    Forall (fun idx => bidx ~< idx /\ List.length bidx < List.length idx)
           (chnsOf (fst (singletonDNode bidx))).
Proof.
  intros; simpl.
  repeat constructor;
    try (eexists [_]; reflexivity);
    try (eexists [_; _]; reflexivity).
Qed.

Lemma tree2Topo_inds_prefix_base:
  forall tr bidx,
    Forall (fun idx => bidx ~< idx)
           (indsOf (fst (tree2Topo tr bidx))).
Proof.
  induction tr using tree_ind_l.
  intros; simpl.
  destruct l.
  - apply singletonDNode_inds_prefix_base.
  - inv H.
    simpl; constructor.
    + apply IdxPrefix_refl.
    + apply Forall_app.
      * specialize (H2 bidx~>0).
        eapply Forall_impl; [|eassumption].
        simpl; intros.
        eapply IdxPrefix_trans; [|eassumption].
        exists [0]; reflexivity.
      * apply collect_forall.
        intros dstr ?.
        apply in_map_iff in H.
        destruct H as [[dtr sifc] [? ?]]; simpl in *; subst.
        apply incMap_In in H0.
        destruct H0 as [str [ofs ?]]; dest.
        apply nth_error_In in H.
        rewrite Forall_forall in H3; specialize (H3 _ H bidx~>(1 + ofs)).
        rewrite <-H0 in H3; simpl in H3.
        eapply Forall_impl; [|eassumption].
        simpl; intros.
        eapply IdxPrefix_trans; [|eassumption].
        eexists [_]; reflexivity.
Qed.

Lemma tree2Topo_chns_prefix_base:
  forall tr bidx,
    Forall (fun idx => bidx ~< idx /\ List.length bidx < List.length idx)
           (chnsOf (fst (tree2Topo tr bidx))).
Proof.
  induction tr using tree_ind_l.
  intros; simpl.
  destruct l.
  - apply singletonDNode_chns_prefix_base.
  - inv H.
    simpl; repeat constructor.
    1-3: (eexists [_]; reflexivity).
    apply Forall_app.
    + specialize (H2 bidx~>0).
      eapply Forall_impl; [|eassumption].
      simpl; intros; dest.
      split; [|omega].
      eapply IdxPrefix_trans; [|eassumption].
      exists [0]; reflexivity.
    + apply collect_forall.
      intros dstr ?.
      apply in_map_iff in H.
      destruct H as [[dtr sifc] [? ?]]; simpl in *; subst.
      apply incMap_In in H0.
      destruct H0 as [str [ofs ?]]; dest.
      apply nth_error_In in H.
      rewrite Forall_forall in H3; specialize (H3 _ H bidx~>(1 + ofs)).
      rewrite <-H0 in H3; simpl in H3.
      eapply Forall_impl; [|eassumption].
      simpl; intros; dest.
      split; [|omega].
      eapply IdxPrefix_trans; [|eassumption].
      eexists [_]; reflexivity.
Qed.

Lemma tree2Topo_disj_inds:
  forall tr1 bidx1 tr2 bidx2,
    bidx1 ~*~ bidx2 ->
    DisjList (indsOf (fst (tree2Topo tr1 bidx1)))
             (indsOf (fst (tree2Topo tr2 bidx2))).
Proof.
  intros.
  apply IndsDisj_DisjList.
  eapply IdxDisj_base_IndsDisj; [eassumption|..];
    apply tree2Topo_inds_prefix_base.
Qed.

Lemma tree2Topo_disj_chns:
  forall tr1 bidx1 tr2 bidx2,
    bidx1 ~*~ bidx2 ->
    DisjList (chnsOf (fst (tree2Topo tr1 bidx1)))
             (chnsOf (fst (tree2Topo tr2 bidx2))).
Proof.
  intros.
  apply IndsDisj_DisjList.
  eapply IdxDisj_base_IndsDisj; [eassumption|..].
  - eapply Forall_impl; [|apply tree2Topo_chns_prefix_base].
    simpl; intros; dest; auto.
  - eapply Forall_impl; [|apply tree2Topo_chns_prefix_base].
    simpl; intros; dest; auto.
Qed.

Lemma l1ExtOf_not_eq:
  forall bidx, l1ExtOf bidx <> bidx.
Proof.
  intros; induction bidx; [discriminate|].
  intro Hx; inv Hx; auto.
Qed.

Lemma singletonDNode_WfDTree:
  forall bidx, WfDTree (fst (singletonDNode bidx)).
Proof.
  intros; split.
  - red; simpl.
    repeat constructor; intro Hx; dest_in.
    unfold l1ExtOf, extendIdx in H.
    eapply l1ExtOf_not_eq; eauto.
  - red; simpl.
    match goal with
    | |- NoDup (?i1 :: ?i2 :: ?i3 :: ?inds) =>
      change (i1 :: i2 :: i3 :: inds) with ([i1; i2; i3] ++ inds)
    end.
    apply NoDup_DisjList.
    + solve_NoDup.
    + solve_NoDup.
    + match goal with
      | |- DisjList ?ll _ =>
        let e := fresh "e" in
        red; intro e; destruct (in_dec idx_dec e ll); [right|auto]; dest_in;
          intro Hx; dest_in; try discriminate
      end.
      * inv H; eapply l1ExtOf_not_eq; eauto.
      * inv H0; eapply l1ExtOf_not_eq; eauto.
      * inv H; eapply l1ExtOf_not_eq; eauto.
Qed.

Lemma tree2Topo_WfDTree:
  forall tr bidx, WfDTree (fst (tree2Topo tr bidx)).
Proof.
  induction tr using tree_ind_l.
  intros; simpl.
  destruct l.
  - apply singletonDNode_WfDTree.
  - remember (t :: l) as strs; clear Heqstrs t l.
    simpl; split.
    + red; simpl.
      constructor.
      * intro Hx; apply collect_In in Hx.
        destruct Hx as [a [? ?]].
        apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
        simpl in *; subst.
        apply incMap_In in H2.
        destruct H2 as [str [ofs ?]]; dest; simpl in *.
        apply nth_error_In in H0.
        pose proof (tree2Topo_inds_prefix_base str bidx~>ofs).
        rewrite <-H2 in H3; simpl in H3.
        rewrite Forall_forall in H3; specialize (H3 _ H1).
        eapply extendIdx_not_IdxPrefix; eassumption.

      * apply collect_NoDup.
        { intros.
          apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
          simpl in *; subst.
          apply incMap_In in H1.
          destruct H1 as [str [extb ?]]; dest; simpl in *.
          apply nth_error_In in H0.
          rewrite Forall_forall in H; specialize (H _ H0 bidx~>extb).
          rewrite <-H1 in H.
          apply H.
        }
        { intros.
          apply nth_error_map_iff in H1; destruct H1 as [[dtr1 cifc1] [? ?]].
          apply nth_error_map_iff in H2; destruct H2 as [[dtr2 cifc2] [? ?]].
          simpl in *; subst.
          apply incMap_nth_error in H3; destruct H3 as [str1 [? ?]]. 
          apply incMap_nth_error in H4; destruct H4 as [str2 [? ?]].
          simpl in *.
          replace a1 with (fst (tree2Topo str1 bidx~>n1))
            by (rewrite <-H2; reflexivity).
          replace a2 with (fst (tree2Topo str2 bidx~>n2))
            by (rewrite <-H4; reflexivity).
          apply tree2Topo_disj_inds.
          apply extendIdx_IdxDisj; auto.
        }

    + red; simpl.
      match goal with
      | |- NoDup (?i1 :: ?i2 :: ?i3 :: ?inds) =>
        change (i1 :: i2 :: i3 :: inds) with ([i1; i2; i3] ++ inds)
      end.
      apply NoDup_DisjList.
      * solve_NoDup.
      * apply collect_NoDup.
        { intros.
          apply in_map_iff in H0; destruct H0 as [[dtr cifc] [? ?]].
          simpl in *; subst.
          apply incMap_In in H1.
          destruct H1 as [str [extb ?]]; dest; simpl in *.
          apply nth_error_In in H0.
          rewrite Forall_forall in H; specialize (H _ H0 bidx~>extb).
          rewrite <-H1 in H.
          apply H.
        }
        { intros.
          apply nth_error_map_iff in H1; destruct H1 as [[dtr1 cifc1] [? ?]].
          apply nth_error_map_iff in H2; destruct H2 as [[dtr2 cifc2] [? ?]].
          simpl in *; subst.
          apply incMap_nth_error in H3; destruct H3 as [str1 [? ?]]. 
          apply incMap_nth_error in H4; destruct H4 as [str2 [? ?]].
          simpl in *.
          replace a1 with (fst (tree2Topo str1 bidx~>n1))
            by (rewrite <-H2; reflexivity).
          replace a2 with (fst (tree2Topo str2 bidx~>n2))
            by (rewrite <-H4; reflexivity).
          apply tree2Topo_disj_chns.
          apply extendIdx_IdxDisj; auto.
        }
      * apply DisjList_map with (f:= @List.length _).
        apply (DisjList_spec_1 eq_nat_dec).
        intros.
        assert (a = S (List.length bidx)) by (dest_in; reflexivity).
        clear H0; subst.
        intro Hx; apply in_map_iff in Hx.
        destruct Hx as [idx ?]; dest.
        apply collect_In in H1; destruct H1 as [sdtr [? ?]].
        apply in_map_iff in H1; destruct H1 as [[dtr sifc] [? ?]].
        simpl in *; subst.
        apply incMap_In in H3; destruct H3 as [str [ofs [? ?]]].
        simpl in *.
        replace sdtr with (fst (tree2Topo str bidx~>ofs)) in H2
          by (rewrite <-H3; reflexivity).
        pose proof (tree2Topo_chns_prefix_base str bidx~>ofs).
        rewrite Forall_forall in H4; specialize (H4 _ H2); dest.
        simpl in H5; omega.
Qed.

Section System.
  Variable tr: tree.

  Local Definition topo := fst (tree2Topo tr 0).
  Local Definition cifc := snd (tree2Topo tr 0).

  Lemma mesi_impl_ORqsInit: GoodORqsInit (initsOf (impl tr)).
  Proof.
    apply initORqs_GoodORqsInit.
  Qed.

  Lemma mesi_topo_wf: WfDTree topo.
  Proof.
    apply tree2Topo_WfDTree.
  Qed.

End System.

