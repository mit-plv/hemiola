Require Import Bool PeanoNat Ascii List Lia.
Require Import Common.
Require Export Index ListSupport.

Set Implicit Arguments.

Local Open Scope list.

Lemma idsOf_app:
  forall {A} (ias1 ias2: list (Id A)),
    idsOf (ias1 ++ ias2) = idsOf ias1 ++ idsOf ias2.
Proof.
  intros; apply map_app.
Qed.

Lemma valsOf_app:
  forall {A} (ias1 ias2: list (Id A)),
    valsOf (ias1 ++ ias2) = valsOf ias1 ++ valsOf ias2.
Proof.
  intros; apply map_app.
Qed.

Lemma idsOf_NoDup:
  forall {A} (ias: list (Id A)),
    NoDup (idsOf ias) -> NoDup ias.
Proof.
  unfold idsOf; intros.
  eapply NoDup_map_inv; eauto.
Qed.

Lemma valsOf_NoDup:
  forall {A} (ias: list (Id A)),
    NoDup (valsOf ias) -> NoDup ias.
Proof.
  unfold valsOf; intros.
  eapply NoDup_map_inv; eauto.
Qed.

Lemma idsOf_NoDup_In_value_eq:
  forall {A} (ias: list (Id A)) i a1 a2,
    NoDup (idsOf ias) ->
    In (i, a1) ias -> In (i, a2) ias ->
    a1 = a2.
Proof.
  induction ias as [|[i a] ias]; simpl; intros; [exfalso; auto|].
  inv H.
  destruct H0.
  - inv H.
    destruct H1.
    + inv H; reflexivity.
    + elim H4; apply in_map_iff; exists (i0, a2); auto.
  - destruct H1.
    + inv H0; elim H4; apply in_map_iff; exists (i0, a1); auto.
    + eapply IHias; eauto.
Qed.

Lemma idsOf_DisjList:
  forall {A} (ias1 ias2: list (Id A)),
    DisjList (idsOf ias1) (idsOf ias2) ->
    DisjList ias1 ias2.
Proof.
  unfold DisjList; intros.
  destruct e as [idx a].
  specialize (H idx); destruct H.
  - left; intro Hx; elim H.
    eapply in_map with (f:= idOf) in Hx; auto.
  - right; intro Hx; elim H.
    eapply in_map with (f:= idOf) in Hx; auto.
Qed.

Lemma valsOf_DisjList:
  forall {A} (ias1 ias2: list (Id A)),
    DisjList (valsOf ias1) (valsOf ias2) ->
    DisjList ias1 ias2.
Proof.
  unfold DisjList; intros.
  destruct e as [idx a].
  specialize (H a); destruct H.
  - left; intro Hx; elim H.
    eapply in_map with (f:= valOf) in Hx; auto.
  - right; intro Hx; elim H.
    eapply in_map with (f:= valOf) in Hx; auto.
Qed.

Lemma removeOnce_idsOf_In:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il iv i,
    In i (idsOf (removeOnce (id_dec eq_dec) iv il)) ->
    In i (idsOf il).
Proof.
  induction il; simpl; intros; auto.
  destruct (id_dec eq_dec iv a); subst; auto.
  simpl in H; destruct H; subst; eauto.
Qed.

Lemma removeL_idsOf_In:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il2 il1 i,
    In i (idsOf (removeL (id_dec eq_dec) il1 il2)) ->
    In i (idsOf il1).
Proof.
  induction il2; simpl; intros; auto.
  eapply removeOnce_idsOf_In; eauto.
Qed.

Lemma removeOnce_idsOf_NoDup:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il iv,
    NoDup (idsOf il) ->
    NoDup (idsOf (removeOnce (id_dec eq_dec) iv il)).
Proof.
  induction il; simpl; intros; auto.
  inv H.
  destruct (id_dec eq_dec iv a); subst; auto.
  simpl; constructor; eauto.
  intro Hx; elim H2.
  eapply removeOnce_idsOf_In; eauto.
Qed.

Lemma removeL_idsOf_NoDup:
  forall {A} (eq_dec: forall x y: A, {x = y} + {x <> y}) il2 il1,
    NoDup (idsOf il1) ->
    NoDup (idsOf (removeL (id_dec eq_dec) il1 il2)).
Proof.
  induction il2; simpl; intros; auto.
  eapply IHil2, removeOnce_idsOf_NoDup; eauto.
Qed.

Lemma liftInds_In:
  forall n ns,
    In (natToIdx n) (liftInds ns) ->
    In n ns.
Proof.
  induction ns; simpl; intros; auto.
  destruct H; auto.
  inv H; auto.
Qed.

Lemma liftInds_NoDup:
  forall inds,
    NoDup inds ->
    NoDup (liftInds inds).
Proof.
  induction inds; simpl; intros; [constructor|].
  inv H; constructor; auto.
  intro Hx; elim H2.
  apply liftInds_In; assumption.
Qed.

Lemma idx_DisjList_head:
  forall (inds1 inds2: list IdxT),
    DisjList (map idxHd inds1) (map idxHd inds2) ->
    DisjList inds1 inds2.
Proof.
  induction inds1; simpl; intros; [apply DisjList_nil_1|].
  apply DisjList_cons in H; dest.
  apply (DisjList_cons_inv idx_dec); auto.
  intro Hx; elim H.
  apply in_map; assumption.
Qed.

Lemma extendIdx_inv:
  forall ext idx1 idx2,
    extendIdx ext idx1 = extendIdx ext idx2 ->
    idx1 = idx2.
Proof.
  unfold extendIdx; intros.
  inv H; reflexivity.
Qed.

Lemma extendIdx_In:
  forall ext idx inds,
    In (extendIdx ext idx) (extendInds ext inds) ->
    In idx inds.
Proof.
  induction inds; simpl; intros; auto.
  destruct H; auto.
  apply extendIdx_inv in H; auto.
Qed.

Lemma extendIdx_NoDup:
  forall ext inds,
    NoDup inds -> NoDup (extendInds ext inds).
Proof.
  induction inds; simpl; intros; auto.
  inv H; constructor; auto.
  intro Hx; elim H2.
  eapply extendIdx_In; eauto.
Qed.

Lemma extendIdx_NoDup_inv:
  forall ext inds,
    NoDup (extendInds ext inds) -> NoDup inds.
Proof.
  induction inds; simpl; intros; auto.
  inv H; constructor; auto.
  intro Hx; elim H2.
  apply in_map; assumption.
Qed.

Lemma extendInds_idxHd_SubList:
  forall ext inds,
    SubList (map idxHd (extendInds ext inds)) [ext].
Proof.
  induction inds; simpl; intros; [apply SubList_nil|].
  apply SubList_cons.
  - left; reflexivity.
  - assumption.
Qed.

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

Lemma IdxDisj_comm:
  forall i1 i2, i1 ~*~ i2 -> i2 ~*~ i1.
Proof.
  unfold IdxDisj; intros; dest; auto.
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
    lia.
  - destruct x; [inv H0; auto|].
    apply (f_equal (@List.length _)) in H0.
    rewrite app_length in H0; simpl in H0.
    lia.
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

Lemma IndsDisj_app_1:
  forall il1 il2 il3,
    IndsDisj il1 il3 -> IndsDisj il2 il3 ->
    IndsDisj (il1 ++ il2) il3.
Proof.
  unfold IndsDisj; intros.
  apply in_app_or in H1; destruct H1; auto.
Qed.

Lemma IndsDisj_app_2:
  forall il1 il2 il3,
    IndsDisj il1 il2 -> IndsDisj il1 il3 ->
    IndsDisj il1 (il2 ++ il3).
Proof.
  unfold IndsDisj; intros.
  apply in_app_or in H2; destruct H2; auto.
Qed.

Lemma IndsDisj_SubList_1:
  forall sl1 l1 l2,
    IndsDisj l1 l2 -> SubList sl1 l1 -> IndsDisj sl1 l2.
Proof.
  unfold IndsDisj; intros; auto.
Qed.

Lemma IndsDisj_SubList_2:
  forall l1 sl2 l2,
    IndsDisj l1 l2 -> SubList sl2 l2 -> IndsDisj l1 sl2.
Proof.
  unfold IndsDisj; intros; auto.
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

Lemma idxPrefixR_prefix:
  forall pi i1 i2,
    idxPrefixR (pi ++ i1) (pi ++ i2) =
    idxPrefixR i1 i2.
Proof.
  induction pi; simpl; intros; [reflexivity|].
  find_if_inside; auto.
  elim n; reflexivity.
Qed.

Lemma IndsDisj_cons_inv_1:
  forall i il1 il2,
    IndsDisj (i :: il1) il2 -> IndsDisj il1 il2.
Proof.
  unfold IndsDisj; intros.
  apply H; auto.
  right; assumption.
Qed.

Lemma IndsDisj_cons_inv_2:
  forall i il1 il2,
    IndsDisj il1 (i :: il2) -> IndsDisj il1 il2.
Proof.
  unfold IndsDisj; intros.
  apply H; auto.
  right; assumption.
Qed.

Lemma IndsDisj_cons_hd_1:
  forall i il1 il2,
    IndsDisj (i :: il1) il2 ->
    forall j, In j il2 -> i ~*~ j.
Proof.
  unfold IndsDisj; intros.
  apply H; auto.
  left; reflexivity.
Qed.

Lemma IndsDisj_cons_hd_2:
  forall i il1 il2,
    IndsDisj il1 (i :: il2) ->
    forall j, In j il1 -> j ~*~ i.
Proof.
  unfold IndsDisj; intros.
  apply H; auto.
  left; reflexivity.
Qed.

Lemma idxPrefixR_IdxPrefix:
  forall i1 i2, idxPrefixR i1 i2 = true ->
                IdxPrefix (rev i1) (rev i2).
Proof.
  induction i1 as [|n1 i1]; simpl; intros;
    [eexists; rewrite app_nil_r; reflexivity|].
  destruct i2 as [|n2 i2]; [discriminate|].
  destruct (Nat.eq_dec n1 n2); subst; [|discriminate].
  simpl.
  specialize (IHi1 _ H).
  red in IHi1; dest; rewrite H0.
  eexists; rewrite app_assoc; reflexivity.
Qed.

Lemma IdxPrefix_idxPrefixR:
  forall i1 i2, IdxPrefix i1 i2 ->
                idxPrefixR (rev i1) (rev i2) = true.
Proof.
  induction i1 as [|n1 i1]; intros; [reflexivity|].
  destruct i2 as [|n2 i2];
    [red in H; dest; destruct x; discriminate|].
  red in H; dest; rewrite H.
  rewrite rev_app_distr; simpl.
  rewrite <-app_assoc.
  rewrite idxPrefixR_prefix.
  simpl; find_if_inside; auto.
Qed.

Lemma idxPrefix_IdxPrefix:
  forall i1 i2, idxPrefix i1 i2 = true -> IdxPrefix i1 i2.
Proof.
  intros.
  rewrite <-rev_involutive with (l:= i1).
  rewrite <-rev_involutive with (l:= i2).
  apply idxPrefixR_IdxPrefix; auto.
Qed.

Lemma IdxPrefix_idxPrefix:
  forall i1 i2, IdxPrefix i1 i2 -> idxPrefix i1 i2 = true.
Proof.
  intros; apply IdxPrefix_idxPrefixR; auto.
Qed.

Lemma inds_NoDup_prefix:
  forall (pi: IdxT) (il pil: list IdxT),
    pil = map (fun i => pi ++ i) il ->
    NoDup il -> NoDup pil.
Proof.
  induction il as [|i il]; simpl; intros; subst; [constructor|].
  inv H0.
  constructor; auto.
  intro Hx; apply in_map_iff in Hx.
  destruct Hx as [ri [? ?]].
  apply app_inv_head in H; subst; auto.
Qed.

Lemma IdxPrefix_prefix_red:
  forall (pi i1 i2: IdxT),
    (i1 ++ pi) ~< (i2 ++ pi) -> i1 ~< i2.
Proof.
  unfold IdxPrefix; intros.
  destruct H as [ri ?].
  rewrite app_assoc in H; apply app_inv_tail in H.
  subst; eauto.
Qed.

Lemma IdxPrefix_prefix_ext:
  forall (pi i1 i2: IdxT),
    i1 ~< i2 -> (i1 ++ pi) ~< (i2 ++ pi).
Proof.
  unfold IdxPrefix; intros.
  destruct H as [ri ?]; subst.
  rewrite <-app_assoc; eauto.
Qed.

Lemma NoPrefix_nil: NoPrefix nil.
Proof.
  red; intros; destruct n1; discriminate.
Qed.

Lemma NoPrefix_singleton: forall i, NoPrefix [i].
Proof.
  unfold NoPrefix; intros.
  destruct n1; simpl in *.
  - destruct n2; [exfalso; auto|].
    destruct n2; discriminate.
  - destruct n1; discriminate.
Qed.

Lemma NoPrefix_cons_inv:
  forall i il,
    NoPrefix (i :: il) -> NoPrefix il.
Proof.
  unfold NoPrefix; intros.
  eapply H with (n1:= S n1) (n2:= S n2); eauto.
Qed.

Lemma NoPrefix_cons_hd:
  forall i il,
    NoPrefix (i :: il) ->
    forall j,
      In j il -> i ~*~ j.
Proof.
  unfold NoPrefix; intros.
  apply In_nth_error in H0; destruct H0 as [n ?].
  eapply H with (n1:= O) (n2:= S n); eauto.
Qed.

Lemma NoPrefix_cons:
  forall i il,
    NoPrefix il ->
    (forall ai, In ai il -> i ~*~ ai) ->
    NoPrefix (i :: il).
Proof.
  induction il; simpl; intros.
  - red; intros.
    destruct n1 as [|[|]]; try discriminate.
    destruct n2 as [|[|]]; try discriminate.
    exfalso; auto.
  - red; intros.
    destruct n1 as [|n1]; simpl in H2.
    + inv H2.
      destruct n2 as [|n2]; [exfalso; auto|clear H1].
      simpl in H3.
      destruct n2 as [|n2]; simpl in H3.
      * inv H3; apply H0; left; reflexivity.
      * eapply IHil with (n1:= O) (n2:= S n2); eauto.
        apply NoPrefix_cons_inv in H; assumption.
    + destruct n2 as [|n2]; simpl in H3.
      * inv H3.
        apply nth_error_In in H2.
        apply IdxDisj_comm; apply H0; auto.
      * destruct n1 as [|n1]; simpl in H2.
        { inv H2; destruct n2 as [|n2]; [exfalso; auto|simpl in H3].
          eapply H with (n1:= O) (n2:= S n2); eauto.
        }
        { destruct n2 as [|n2]; simpl in H3.
          { inv H3; eapply H with (n1:= S n1) (n2:= O); eauto. }
          { eapply IHil with (n1:= S n1) (n2:= S n2); eauto.
            apply NoPrefix_cons_inv in H; assumption.
          }
        }
Qed.

Lemma NoPrefix_IndsDisj:
  forall il1 il2,
    NoPrefix il1 -> NoPrefix il2 ->
    IndsDisj il1 il2 ->
    NoPrefix (il1 ++ il2).
Proof.
  induction il1; simpl; intros; [assumption|].
  apply NoPrefix_cons.
  - apply IHil1.
    + eapply NoPrefix_cons_inv; eassumption.
    + assumption.
    + eapply IndsDisj_cons_inv_1; eassumption.
  - intros; apply in_app_or in H2; destruct H2.
    + eapply NoPrefix_cons_hd; eassumption.
    + eapply IndsDisj_cons_hd_1; eassumption.
Qed.

(** Some useful tactics about indices *)

Ltac solve_inds_NoDup_prefix :=
  eapply inds_NoDup_prefix;
  [repeat
     match goal with
     | |- _ :: _ = map _ ?l => is_evar l; instantiate (1:= _ :: _); simpl; f_equal
     | |- nil = map _ ?l => is_evar l; instantiate (1:= nil); reflexivity
     end|];
  solve_NoDup.

Ltac solve_inds_NoDup_pre :=
  repeat
    (repeat autounfold with RuleConds;
     repeat
       match goal with
       | [H: In _ (map _ _) |- _] => apply in_map_iff in H; dest; subst
       | [H: nth_error (map _ _) _ = Some _ |- _] =>
         apply map_nth_error_inv in H; dest; subst

       | |- context [List.map _ (_ ++ _)] => rewrite map_app
       | |- context [List.concat (List.map _ _)] => rewrite concat_map
                                                            
       | |- NoDup (_ ++ _) => apply NoDup_DisjList
       | |- NoDup (List.concat _) => apply concat_NoDup; intros
       | |- NoDup ((?pi ++ _) :: (?pi ++ _) :: _) => solve_inds_NoDup_prefix
       | |- NoDup ((_ ~> _) :: _) => solve_NoDup

       | |- DisjList (List.concat _) _ => apply DisjList_comm
       | |- DisjList _ (List.concat _) => apply concat_DisjList; intros
       end; simpl in * ).

Ltac solve_IndsDisj :=
  repeat
    match goal with
    | |- IndsDisj _ _ => red; intros; dest_in
    | |- _ ~*~ _ => split; intro
    | [H: _ ~< _ |- _] =>
      apply IdxPrefix_idxPrefix in H; unfold idxPrefix in H;
      repeat rewrite rev_app_distr in H; discriminate
    | [H: (_ ++ ?pi) ~< (_ ++ ?pi) |- _] =>
      apply IdxPrefix_prefix_red in H; auto
    end.

Ltac solve_inds_NoDup itac :=
  solve_inds_NoDup_pre;
  match goal with
  | |- DisjList _ _ => apply IndsDisj_DisjList
  end;
  itac;
  solve_IndsDisj.

