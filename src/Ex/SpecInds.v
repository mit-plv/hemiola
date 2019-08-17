Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector IndexSupport Syntax Semantics.
Require Import Topology RqRsLang.

Require Import Ex.Spec Ex.TopoTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Lemma NoPrefix_NoDup:
  forall inds, NoPrefix inds -> NoDup inds.
Proof.
  intros.
  apply NoDup_nth_error; intros.
  apply nth_error_Some in H0.
  destruct (nth_error inds i) eqn:Hi; [clear H0|exfalso; auto].
  apply eq_sym in H1.
  destruct (eq_nat_dec i j); [assumption|exfalso].
  specialize (H _ _ _ _ n Hi H1).
  destruct H.
  elim H.
  apply IdxPrefix_refl.
Qed.

Lemma extendIdx_IdxDisj_congr:
  forall bidx1 bidx2,
    bidx1 ~*~ bidx2 ->
    forall ext1 ext2,
      bidx1~>ext1 ~*~ bidx2~>ext2.
Proof.
  unfold IdxDisj, extendIdx; intros; dest.
  split.
  - intro Hx; elim H.
    red in Hx; dest.
    destruct x; simpl in *.
    + inv H1; apply IdxPrefix_refl.
    + inv H1; exists (x ++ [ext1]); rewrite <-app_assoc; reflexivity.
  - intro Hx; elim H0.
    red in Hx; dest.
    destruct x; simpl in *.
    + inv H1; apply IdxPrefix_refl.
    + inv H1; exists (x ++ [ext2]); rewrite <-app_assoc; reflexivity.
Qed.

Lemma NoPrefix_extendInds:
  forall inds,
    NoPrefix inds ->
    forall e, NoPrefix (extendInds e inds).
Proof.
  unfold NoPrefix, extendInds; intros.
  apply map_nth_error_inv in H1.
  apply map_nth_error_inv in H2; dest; subst.
  apply extendIdx_IdxDisj_congr.
  eapply H; eauto.
Qed.

Section System.
  Variable cinds: list IdxT.
  Hypothesis (Hcinds: NoPrefix cinds).

  Instance SpecOStateIfc: OStateIfc :=
    {| ost_sz := 1;
       ost_ty := [nat:Type]%vector |}.

  Definition specIdx: IdxT := 0.
  Definition specValueIdx: Fin.t 1 := Fin.F1.
  Definition specOStatesInit: OStates :=
    [specIdx <- hvcons 0 hvnil].
  Definition specORqsInit: ORqs Msg :=
    [specIdx <- []].

  Section PerChn.
    Variable eidx: IdxT.

    Definition specGetRq: Rule :=
      {| rule_idx := [0]~~eidx;
         rule_precond :=
           MsgsFrom [rqUpFrom eidx]
           /\oprec MsgIdsFrom [getRq]
           /\oprec RqAccepting;
         rule_trs :=
           fun ost orq mins =>
             (ost, orq,
              [(downTo eidx, {| msg_id := getRs;
                                msg_type := MRs;
                                msg_value := ost#[specValueIdx]
                             |})])
      |}.

    Definition specSetRq: Rule :=
      {| rule_idx := [1]~~eidx;
         rule_precond :=
           MsgsFrom [rqUpFrom eidx]
           /\oprec MsgIdsFrom [setRq]
           /\oprec RqAccepting;
         rule_trs :=
           fun (ost: OState) orq mins =>
             ((hd_error mins)
                >>=[ost] (fun idm =>
                            ost+#[specValueIdx <- msg_value (valOf idm)]),
              orq,
              [(downTo eidx, {| msg_id := setRs;
                                msg_type := MRs;
                                msg_value := O |})])
      |}.

  End PerChn.

  Definition specRulesI (eidx: IdxT): list Rule :=
    [specGetRq eidx; specSetRq eidx].

  Definition specRules (einds: list IdxT): list Rule :=
    List.concat (map (fun eidx => specRulesI eidx) einds).

  Hint Unfold specRulesI specRules: RuleConds.

  Ltac disc_child_inds_NoPrefix :=
    try match goal with
        | [Hnp: NoPrefix ?inds, H0: ?n1 <> ?n2,
           H1: nth_error ?inds ?n1 = Some _,
           H2: nth_error ?inds ?n2 = Some _ |- _] =>
          specialize (Hnp _ _ _ _ H0 H1 H2); destruct Hnp; auto
        end.

  Lemma specObj_rules_valid:
    NoDup (map rule_idx (specRules (extendInds 0 cinds))).
  Proof.
    apply NoPrefix_extendInds with (e:= 0) in Hcinds.
    solve_inds_NoDup disc_child_inds_NoPrefix.
  Qed.

  Definition specObj: Object :=
    {| obj_idx := specIdx;
       obj_rules := specRules (extendInds 0 cinds);
       obj_rules_valid := specObj_rules_valid
    |}.

  Definition specMerqs: list IdxT :=
    extendInds rqUpIdx (extendInds 0 cinds).

  Definition specMerss: list IdxT :=
    extendInds downIdx (extendInds 0 cinds).

  Lemma spec_msg_inds_valid:
    NoDup (specMerqs ++ specMerss).
  Proof.
    apply NoDup_DisjList.
    - do 2 apply extendIdx_NoDup.
      apply NoPrefix_NoDup; assumption.
    - do 2 apply extendIdx_NoDup.
      apply NoPrefix_NoDup; assumption.
    - apply idx_DisjList_head.
      eapply DisjList_SubList; [apply extendInds_idxHd_SubList|].
      eapply DisjList_comm, DisjList_SubList; [apply extendInds_idxHd_SubList|].
      solve_DisjList eq_nat_dec.
  Qed.

  Definition spec: System :=
    {| sys_objs := [specObj];
       sys_oinds_valid := ltac:(inds_valid_tac);
       sys_minds := nil;
       sys_merqs := specMerqs;
       sys_merss := specMerss;
       sys_msg_inds_valid := spec_msg_inds_valid;
       sys_oss_inits := specOStatesInit;
       sys_orqs_inits := specORqsInit
    |}.

End System.

Section Facts.

  Lemma specGetRq_in_specRules:
    forall oidx einds,
      In oidx einds ->
      In (specGetRq oidx) (specRules einds).
  Proof.
    induction einds; simpl; intros; auto.
    destruct H; subst; auto.
  Qed.

  Lemma specSetRq_in_specRules:
    forall oidx einds,
      In oidx einds ->
      In (specSetRq oidx) (specRules einds).
  Proof.
    induction einds; simpl; intros; auto.
    destruct H; subst; auto.
  Qed.

End Facts.
