Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** Ltacs to get conditions about [Rule]s. *)

Ltac red_obj_rule :=
  repeat
    match goal with
    | [H: step_m _ _ (RlblInt _ _ _ _) _ |- _] => inv H
    | [H: {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} =
          {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} |- _] => inv H
    | [H0: In ?obj1 (sys_objs ?sys),
       H1: In ?obj2 (sys_objs ?sys),
       H2: obj_idx ?obj1 = obj_idx ?obj2 |- _] =>
      pose proof (obj_same_id_in_system_same _ _ _ H0 H1 H2);
      subst; clear H0 H2
    | [H0: In ?rule1 (obj_rules ?obj),
       H1: In ?rule2 (obj_rules ?obj),
       H2: rule_idx ?obj1 = rule_idx ?obj2 |- _] =>
      pose proof (rule_same_id_in_object_same _ _ _ H0 H1 H2);
      subst; clear H0 H2
    end.

Ltac good_rqrs_rule_get rule :=
  match goal with
  | [H: GoodRqRsSys _ ?sys,
     Hobj: In ?obj (sys_objs ?sys),
     Hrule: In rule (obj_rules ?obj) |- _] =>
    let Hg := fresh "H" in
    pose proof H as Hg;
    red in Hg; rewrite Forall_forall in Hg;
    specialize (Hg _ Hobj);
    red in Hg; rewrite Forall_forall in Hg;
    specialize (Hg _ Hrule)
  end.

Ltac good_rqrs_rule_cases rule :=
  match goal with
  | [H: GoodRqRsRule _ _ _ rule |- _] =>
    destruct H as [|[|[|[|]]]]
  end.

Ltac good_rqUp_rsUp_get rqRule rsRule :=
  match goal with
  | [H: RqUpRsUpOkSys _ ?sys,
     HobjIn: In ?obj (sys_objs ?sys),
     HrqIn: In rqRule (obj_rules ?obj),
     Hrq: RqToUpRule _ _ rqRule,
     HrsIn: In rsRule (obj_rules ?obj),
     Hrs: RsToUpRule _ _ rsRule |- _] =>
    let Hr := fresh "H" in
    pose proof H as Hr;
    red in Hr; rewrite Forall_forall in Hr;
    specialize (Hr _ HobjIn);
    specialize (Hr _ _ HrqIn Hrq HrsIn Hrs)
  end.

Section RqRsDTree.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hsd: RqRsDTree dtr sys).

  Lemma rqEdgeUpFrom_Some:
    forall oidx rqUp,
      rqEdgeUpFrom dtr oidx = Some rqUp ->
      exists rsUp down pidx,
        rsEdgeUpFrom dtr oidx = Some rsUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx.
  Proof.
    unfold rqEdgeUpFrom, upEdgesFrom; intros.
    remember (parentChnsOf dtr oidx) as pchns.
    destruct pchns as [[[ups downs] pidx]|]; simpl in *; [|discriminate].
    unfold rsEdgeUpFrom, upEdgesFrom, edgeDownTo, downEdgesTo, parentIdxOf.
    destruct Hsd.
    apply eq_sym in Heqpchns.
    rewrite Heqpchns; simpl.
    apply H1 in Heqpchns.
    destruct Heqpchns as [rqUp' [rsUp [down ?]]]; dest; subst; simpl.
    repeat eexists.
  Qed.

  Lemma rsEdgeUpFrom_Some:
    forall oidx rsUp,
      rsEdgeUpFrom dtr oidx = Some rsUp ->
      exists rqUp down pidx,
        rsEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx.
  Proof.
    unfold rsEdgeUpFrom, upEdgesFrom; intros.
    remember (parentChnsOf dtr oidx) as pchns.
    destruct pchns as [[[ups downs] pidx]|]; simpl in *; [|discriminate].
    unfold rqEdgeUpFrom, upEdgesFrom, edgeDownTo, downEdgesTo, parentIdxOf.
    destruct Hsd.
    apply eq_sym in Heqpchns.
    rewrite Heqpchns; simpl.
    apply H1 in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp' [down ?]]]; dest; subst; simpl.
    repeat eexists.
  Qed.

  Lemma edgeDownTo_Some:
    forall oidx down,
      edgeDownTo dtr oidx = Some down ->
      exists rqUp rsUp pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        rsEdgeUpFrom dtr oidx = Some rsUp /\
        parentIdxOf dtr oidx = Some pidx.
  Proof.
    unfold edgeDownTo, downEdgesTo; intros.
    remember (parentChnsOf dtr oidx) as pchns.
    destruct pchns as [[[ups downs] pidx]|]; simpl in *; [|discriminate].
    unfold rqEdgeUpFrom, rsEdgeUpFrom, upEdgesFrom, parentIdxOf.
    destruct Hsd.
    apply eq_sym in Heqpchns.
    rewrite Heqpchns; simpl.
    apply H1 in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp [down' ?]]]; dest; subst; simpl.
    repeat eexists.
  Qed.

  Lemma parentIdxOf_Some:
    forall oidx pidx,
      parentIdxOf dtr oidx = Some pidx ->
      exists rqUp rsUp down,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        rsEdgeUpFrom dtr oidx = Some rsUp /\
        edgeDownTo dtr oidx = Some down.
  Proof.
    unfold parentIdxOf; intros.
    remember (parentChnsOf dtr oidx) as pchns.
    destruct pchns as [[[ups downs] pidx']|]; simpl in *; [|discriminate].
    inv H.
    unfold rqEdgeUpFrom, rsEdgeUpFrom, upEdgesFrom, edgeDownTo, downEdgesTo.
    destruct Hsd.
    apply eq_sym in Heqpchns.
    rewrite Heqpchns; simpl.
    apply H0 in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp [down ?]]]; dest; subst; simpl.
    repeat eexists.
  Qed.

  Lemma RqRsDownMatch_rq_rs:
    forall oidx rssFrom rqTos P,
      RqRsDownMatch dtr oidx rqTos rssFrom P ->
      forall down,
        In down rqTos ->
        exists cidx rsUp,
          P cidx /\
          parentIdxOf dtr cidx = Some oidx /\
          edgeDownTo dtr cidx = Some down /\
          rsEdgeUpFrom dtr cidx = Some rsUp /\
          In rsUp rssFrom.
  Proof.
    intros.
    red in H; dest; clear H.
    generalize dependent rssFrom.
    induction rqTos as [|rqTo rqTos]; simpl; intros.
    - destruct rssFrom; [|discriminate]; inv H0.
    - destruct rssFrom as [|rsFrom rssFrom]; [discriminate|].
      simpl; inv H1; inv H2.
      destruct H4 as [rcidx ?]; dest; simpl in *.
      destruct H0; subst.
      + eauto 8.
      + specialize (IHrqTos H0 _ H3 H5).
        destruct IHrqTos as [cidx [rsUp ?]]; dest.
        eauto 8.
  Qed.

  Lemma RqRsDownMatch_rs_rq:
    forall oidx rssFrom rqTos P,
      RqRsDownMatch dtr oidx rqTos rssFrom P ->
      forall rsUp,
        In rsUp rssFrom ->
        exists cidx down,
          P cidx /\
          parentIdxOf dtr cidx = Some oidx /\
          edgeDownTo dtr cidx = Some down /\
          rsEdgeUpFrom dtr cidx = Some rsUp /\
          In down rqTos.
  Proof.
    intros.
    red in H; dest; clear H.
    generalize dependent rssFrom.
    induction rqTos as [|rqTo rqTos]; simpl; intros.
    - destruct rssFrom; [|discriminate]; inv H0.
    - destruct rssFrom as [|rsFrom rssFrom]; [discriminate|].
      simpl; inv H1; inv H2.
      destruct H4 as [rcidx ?]; dest; simpl in *.
      destruct H0; subst.
      + eauto 8.
      + specialize (IHrqTos _ H3 H5 H0).
        destruct IHrqTos as [cidx [down ?]]; dest.
        eauto 8.
  Qed.
  
  Lemma rqrsDTree_rqEdgeUpFrom_sys_minds:
    forall oidx midx,
      rqEdgeUpFrom dtr oidx = Some midx ->
      In midx sys.(sys_minds).
  Proof.
    intros.
    unfold rqEdgeUpFrom, upEdgesFrom in H.
    remember (parentChnsOf dtr oidx) as pchns.
    destruct pchns as [[[ups downs] pidx']|]; simpl in *; [|discriminate].
    destruct Hsd.
    apply eq_sym in Heqpchns; apply H1 in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp [down ?]]]; dest; subst; simpl.
    simpl in H; inv H.
    apply H4; simpl; tauto.
  Qed.

  Lemma rqrsDTree_rsEdgeUpFrom_sys_minds:
    forall oidx midx,
      rsEdgeUpFrom dtr oidx = Some midx ->
      In midx sys.(sys_minds).
  Proof.
    intros.
    unfold rsEdgeUpFrom, upEdgesFrom in H.
    remember (parentChnsOf dtr oidx) as pchns.
    destruct pchns as [[[ups downs] pidx']|]; simpl in *; [|discriminate].
    destruct Hsd.
    apply eq_sym in Heqpchns; apply H1 in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp [down ?]]]; dest; subst; simpl.
    simpl in H; inv H.
    apply H4; simpl; tauto.
  Qed.

  Lemma rqrsDTree_edgeDownTo_sys_minds:
    forall oidx midx,
      edgeDownTo dtr oidx = Some midx ->
      In midx sys.(sys_minds).
  Proof.
    intros.
    unfold edgeDownTo, downEdgesTo in H.
    remember (parentChnsOf dtr oidx) as pchns.
    destruct pchns as [[[ups downs] pidx']|]; simpl in *; [|discriminate].
    destruct Hsd.
    apply eq_sym in Heqpchns; apply H1 in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp [down ?]]]; dest; subst; simpl.
    simpl in H; inv H.
    apply H5; simpl; tauto.
  Qed.

  Lemma rqrsDTree_rqUp_rqUp_not_eq:
    forall oidx1 oidx2 rqUp1 rqUp2,
      oidx1 <> oidx2 ->
      rqEdgeUpFrom dtr oidx1 = Some rqUp1 ->
      rqEdgeUpFrom dtr oidx2 = Some rqUp2 ->
      rqUp1 <> rqUp2.
  Proof.
    unfold rqEdgeUpFrom, upEdgesFrom; intros.
    destruct Hsd.
    remember (parentChnsOf dtr oidx1) as pchns1.
    destruct pchns1 as [[[ups1 downs1] pidx1]|]; [apply eq_sym in Heqpchns1|discriminate].
    remember (parentChnsOf dtr oidx2) as pchns2.
    destruct pchns2 as [[[ups2 downs2] pidx2]|]; [apply eq_sym in Heqpchns2|discriminate].
    simpl in *.
    pose proof (parentChnsOf_DisjList H2 H Heqpchns1 Heqpchns2).

    apply hd_error_In in H0.
    apply hd_error_In in H1.
    eapply DisjList_In_neq.
    - eassumption.
    - apply in_or_app; auto.
    - apply in_or_app; auto.
  Qed.

  Lemma rqrsDTree_rqUp_rsUp_not_eq:
    forall oidx1 oidx2 rqUp1 rsUp2,
      rqEdgeUpFrom dtr oidx1 = Some rqUp1 ->
      rsEdgeUpFrom dtr oidx2 = Some rsUp2 ->
      rqUp1 <> rsUp2.
  Proof.
    unfold rqEdgeUpFrom, rsEdgeUpFrom, upEdgesFrom; intros; destruct Hsd.
    destruct (eq_nat_dec oidx1 oidx2); subst.
    - remember (parentChnsOf dtr oidx2) as pchn.
      destruct pchn as [[[ups downs] pidx]|]; [|discriminate].
      apply eq_sym in Heqpchn; simpl in *.
      apply parentChnsOf_NoDup in Heqpchn; [|assumption].
      destruct ups as [|? ups]; [discriminate|simpl in H; inv H].
      destruct ups as [|? ups]; [discriminate|simpl in H0; inv H0].
      intro Hx; subst.
      inv Heqpchn; elim H3; simpl; tauto.
    - remember (parentChnsOf dtr oidx1) as pchns1.
      destruct pchns1 as [[[ups1 downs1] pidx1]|]; [apply eq_sym in Heqpchns1|discriminate].
      remember (parentChnsOf dtr oidx2) as pchns2.
      destruct pchns2 as [[[ups2 downs2] pidx2]|]; [apply eq_sym in Heqpchns2|discriminate].
      simpl in *.
      pose proof (parentChnsOf_DisjList H1 n Heqpchns1 Heqpchns2).
      apply hd_error_In in H.
      apply hd_error_In, tl_In in H0.
      eapply DisjList_In_neq.
      + eassumption.
      + apply in_or_app; auto.
      + apply in_or_app; auto.
  Qed.
  
  Lemma rqrsDTree_rqUp_down_not_eq:
    forall oidx1 oidx2 rqUp1 down2,
      rqEdgeUpFrom dtr oidx1 = Some rqUp1 ->
      edgeDownTo dtr oidx2 = Some down2 ->
      rqUp1 <> down2.
  Proof.
    unfold rqEdgeUpFrom, upEdgesFrom, edgeDownTo, downEdgesTo; intros; destruct Hsd.
    destruct (eq_nat_dec oidx1 oidx2); subst.
    - remember (parentChnsOf dtr oidx2) as pchn.
      destruct pchn as [[[ups downs] pidx]|]; [|discriminate].
      apply eq_sym in Heqpchn; simpl in *.
      apply parentChnsOf_NoDup in Heqpchn; [|assumption].
      destruct ups as [|? ups]; [discriminate|simpl in H; inv H].
      destruct downs as [|? downs]; [discriminate|simpl in H0; inv H0].
      intro Hx; subst.
      inv Heqpchn; elim H3.
      apply in_or_app; right; simpl; tauto.
    - remember (parentChnsOf dtr oidx1) as pchns1.
      destruct pchns1 as [[[ups1 downs1] pidx1]|]; [apply eq_sym in Heqpchns1|discriminate].
      remember (parentChnsOf dtr oidx2) as pchns2.
      destruct pchns2 as [[[ups2 downs2] pidx2]|]; [apply eq_sym in Heqpchns2|discriminate].
      simpl in *.
      pose proof (parentChnsOf_DisjList H1 n Heqpchns1 Heqpchns2).
      apply hd_error_In in H.
      apply hd_error_In in H0.
      eapply DisjList_In_neq.
      + eassumption.
      + apply in_or_app; auto.
      + apply in_or_app; auto.
  Qed.

  Lemma rqrsDTree_rsUp_rsUp_not_eq:
    forall oidx1 oidx2 rsUp1 rsUp2,
      oidx1 <> oidx2 ->
      rsEdgeUpFrom dtr oidx1 = Some rsUp1 ->
      rsEdgeUpFrom dtr oidx2 = Some rsUp2 ->
      rsUp1 <> rsUp2.
  Proof.
    unfold rsEdgeUpFrom, upEdgesFrom; intros.
    destruct Hsd.
    remember (parentChnsOf dtr oidx1) as pchns1.
    destruct pchns1 as [[[ups1 downs1] pidx1]|]; [apply eq_sym in Heqpchns1|discriminate].
    remember (parentChnsOf dtr oidx2) as pchns2.
    destruct pchns2 as [[[ups2 downs2] pidx2]|]; [apply eq_sym in Heqpchns2|discriminate].
    simpl in *.
    pose proof (parentChnsOf_DisjList H2 H Heqpchns1 Heqpchns2).

    apply hd_error_In, tl_In in H0.
    apply hd_error_In, tl_In in H1.
    eapply DisjList_In_neq.
    - eassumption.
    - apply in_or_app; auto.
    - apply in_or_app; auto.
  Qed.

  Lemma rqrsDTree_rsUp_down_not_eq:
    forall oidx1 oidx2 rsUp1 down2,
      rsEdgeUpFrom dtr oidx1 = Some rsUp1 ->
      edgeDownTo dtr oidx2 = Some down2 ->
      rsUp1 <> down2.
  Proof.
    unfold rsEdgeUpFrom, upEdgesFrom, edgeDownTo, downEdgesTo; intros; destruct Hsd.
    destruct (eq_nat_dec oidx1 oidx2); subst.
    - remember (parentChnsOf dtr oidx2) as pchn.
      destruct pchn as [[[ups downs] pidx]|]; [|discriminate].
      apply eq_sym in Heqpchn; simpl in *.
      apply parentChnsOf_NoDup in Heqpchn; [|assumption].
      destruct ups as [|? ups]; [discriminate|simpl in H; inv H].
      destruct ups as [|? ups]; [discriminate|simpl in H4; inv H4].
      destruct downs as [|? downs]; [discriminate|simpl in H0; inv H0].
      intro Hx; subst.
      inv Heqpchn; inv H4; elim H5.
      apply in_or_app; right; simpl; tauto.
    - remember (parentChnsOf dtr oidx1) as pchns1.
      destruct pchns1 as [[[ups1 downs1] pidx1]|]; [apply eq_sym in Heqpchns1|discriminate].
      remember (parentChnsOf dtr oidx2) as pchns2.
      destruct pchns2 as [[[ups2 downs2] pidx2]|]; [apply eq_sym in Heqpchns2|discriminate].
      simpl in *.
      pose proof (parentChnsOf_DisjList H1 n Heqpchns1 Heqpchns2).
      apply hd_error_In, tl_In in H.
      apply hd_error_In in H0.
      eapply DisjList_In_neq.
      + eassumption.
      + apply in_or_app; auto.
      + apply in_or_app; auto.
  Qed.

  Lemma rqrsDTree_down_down_not_eq:
    forall oidx1 oidx2 down1 down2,
      oidx1 <> oidx2 ->
      edgeDownTo dtr oidx1 = Some down1 ->
      edgeDownTo dtr oidx2 = Some down2 ->
      down1 <> down2.
  Proof.
    unfold edgeDownTo, downEdgesTo; intros.
    destruct Hsd.
    remember (parentChnsOf dtr oidx1) as pchns1.
    destruct pchns1 as [[[ups1 downs1] pidx1]|]; [apply eq_sym in Heqpchns1|discriminate].
    remember (parentChnsOf dtr oidx2) as pchns2.
    destruct pchns2 as [[[ups2 downs2] pidx2]|]; [apply eq_sym in Heqpchns2|discriminate].
    simpl in *.
    pose proof (parentChnsOf_DisjList H2 H Heqpchns1 Heqpchns2).

    apply hd_error_In in H0.
    apply hd_error_In in H1.
    eapply DisjList_In_neq.
    - eassumption.
    - apply in_or_app; auto.
    - apply in_or_app; auto.
  Qed.

  Lemma rqrsDTree_rqUp_ups_not_in:
    forall oidx1 oidx2 rqUp1 downs2 ups2 P,
      rqEdgeUpFrom dtr oidx1 = Some rqUp1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      ~ In rqUp1 ups2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rs_rq in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    elim (rqrsDTree_rqUp_rsUp_not_eq _ _ H H3); reflexivity.
  Qed.

  Lemma rqrsDTree_rsUp_ups_not_in:
    forall oidx rsUp1 downs2 ups2 P,
      rsEdgeUpFrom dtr oidx = Some rsUp1 ->
      RqRsDownMatch dtr oidx downs2 ups2 P ->
      ~ In rsUp1 ups2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rs_rq in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    destruct Hsd.
    apply parentIdxOf_not_eq in H1; [|assumption].
    elim (rqrsDTree_rsUp_rsUp_not_eq H1 H3 H); reflexivity.
  Qed.

  Lemma rqrsDTree_rsUp_ups_not_in_parent:
    forall oidx1 oidx2 rsUp1 downs2 ups2 P,
      rsEdgeUpFrom dtr oidx1 = Some rsUp1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      ~ In rsUp1 ups2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rs_rq in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    destruct Hsd.
    destruct (eq_nat_dec oidx1 cidx); subst.
    - elim H1; assumption.
    - elim (rqrsDTree_rsUp_rsUp_not_eq n H H4); reflexivity.
  Qed.

  Lemma rqrsDTree_down_ups_not_in:
    forall oidx1 oidx2 down1 downs2 ups2 P,
      edgeDownTo dtr oidx1 = Some down1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      ~ In down1 ups2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rs_rq in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    elim (rqrsDTree_rsUp_down_not_eq _ _ H3 H); reflexivity.
  Qed.
  
  Lemma rqrsDTree_rqUp_downs_not_in:
    forall oidx1 oidx2 rqUp1 downs2 ups2 P,
      rqEdgeUpFrom dtr oidx1 = Some rqUp1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      ~ In rqUp1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_rs in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    elim (rqrsDTree_rqUp_down_not_eq _ _ H H2); reflexivity.
  Qed.

  Lemma rqrsDTree_rsUp_downs_not_in:
    forall oidx1 oidx2 rsUp1 downs2 ups2 P,
      rsEdgeUpFrom dtr oidx1 = Some rsUp1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      ~ In rsUp1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_rs in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    elim (rqrsDTree_rsUp_down_not_eq _ _ H H2); reflexivity.
  Qed.

  Lemma rqrsDTree_down_downs_not_in:
    forall oidx down1 downs2 ups2 P,
      edgeDownTo dtr oidx = Some down1 ->
      RqRsDownMatch dtr oidx downs2 ups2 P ->
      ~ In down1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_rs in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    destruct Hsd.
    apply parentIdxOf_not_eq in H1; [|eassumption].
    elim (rqrsDTree_down_down_not_eq H1 H2 H); reflexivity.
  Qed.

  Lemma rqrsDTree_down_downs_not_in_parent:
    forall oidx1 oidx2 down1 downs2 ups2 P,
      edgeDownTo dtr oidx1 = Some down1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      ~ In down1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_rs in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    destruct Hsd.
    destruct (eq_nat_dec oidx1 cidx); subst.
    - elim H1; assumption.
    - elim (rqrsDTree_down_down_not_eq n H H3); reflexivity.
  Qed.

  Lemma rqrsDTree_down_downs_not_in_child_P:
    forall oidx1 oidx2 down1 downs2 ups2,
      edgeDownTo dtr oidx1 = Some down1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 (fun cidx => cidx <> oidx1) ->
      ~ In down1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_rs in H0; [|eassumption].
    destruct H0 as [cidx [down ?]]; dest.
    elim (rqrsDTree_down_down_not_eq H0 H2 H).
    elim H3; reflexivity.
  Qed.

  Lemma RqRsDownMatch_rqs_disj:
    forall oidx1 rqTos1 rssFrom1 P1
           oidx2 rqTos2 rssFrom2 P2,
      oidx1 <> oidx2 ->
      RqRsDownMatch dtr oidx1 rqTos1 rssFrom1 P1 ->
      RqRsDownMatch dtr oidx2 rqTos2 rssFrom2 P2 ->
      DisjList rqTos1 rqTos2.
  Proof.
    intros.
    red; intro midx.
    destruct (in_dec eq_nat_dec midx rqTos1) as [Heq1|]; auto.
    destruct (in_dec eq_nat_dec midx rqTos2) as [Heq2|]; auto.
    exfalso.
    eapply RqRsDownMatch_rq_rs in Heq1; [|eassumption].
    destruct Heq1 as [cidx1 [rsUp1 ?]]; dest.
    eapply RqRsDownMatch_rq_rs in Heq2; [|eassumption].
    destruct Heq2 as [cidx2 [rsUp2 ?]]; dest.
    destruct (eq_nat_dec cidx1 cidx2); subst.
    - rewrite H3 in H8; inv H8; auto.
    - elim (rqrsDTree_down_down_not_eq n H4 H9); reflexivity.
  Qed.

  Lemma RqRsDownMatch_rss_disj:
    forall oidx1 rqTos1 rssFrom1 P1
           oidx2 rqTos2 rssFrom2 P2,
      oidx1 <> oidx2 ->
      RqRsDownMatch dtr oidx1 rqTos1 rssFrom1 P1 ->
      RqRsDownMatch dtr oidx2 rqTos2 rssFrom2 P2 ->
      DisjList rssFrom1 rssFrom2.
  Proof.
    intros.
    red; intro midx.
    destruct (in_dec eq_nat_dec midx rssFrom1) as [Heq1|]; auto.
    destruct (in_dec eq_nat_dec midx rssFrom2) as [Heq2|]; auto.
    exfalso.
    eapply RqRsDownMatch_rs_rq in Heq1; [|eassumption].
    destruct Heq1 as [cidx1 [down1 ?]]; dest.
    eapply RqRsDownMatch_rs_rq in Heq2; [|eassumption].
    destruct Heq2 as [cidx2 [down2 ?]]; dest.
    destruct (eq_nat_dec cidx1 cidx2); subst.
    - rewrite H3 in H8; inv H8; auto.
    - elim (rqrsDTree_rsUp_rsUp_not_eq n H5 H10); reflexivity.
  Qed.
  
  Lemma rqrsDTree_down_downs_not_in_child:
    forall cidx oidx down rsUp downs ups P,
      parentIdxOf dtr cidx = Some oidx ->
      edgeDownTo dtr cidx = Some down ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      ~ In rsUp ups ->
      RqRsDownMatch dtr oidx downs ups P ->
      ~ In down downs.
  Proof.
    intros; intro Hx.
    elim H2; clear H2.
    eapply RqRsDownMatch_rq_rs in H3; eauto.
    destruct H3 as [rcidx [rrsUp ?]]; dest.
    destruct (eq_nat_dec cidx rcidx); subst.
    - rewrite H1 in H5; inv H5; assumption.
    - elim (rqrsDTree_down_down_not_eq n H0 H4); reflexivity.
  Qed.

  Lemma footprintUpOk_rs_eq:
    forall oidx rqFrom rqTo rsFrom1 rsbTo1 rsFrom2 rsbTo2,
      FootprintUpOk dtr oidx rqFrom rqTo rsFrom1 rsbTo1 ->
      FootprintUpOk dtr oidx rqFrom rqTo rsFrom2 rsbTo2 ->
      rsFrom1 = rsFrom2 /\ rsbTo1 = rsbTo2.
  Proof.
    unfold FootprintUpOk; intros.
    destruct H as [cidx1 ?]; destruct H0 as [cidx2 ?]; dest.
    destruct (eq_nat_dec cidx1 cidx2); subst.
    - rewrite H7 in H3; inv H3.
      rewrite H8 in H4; inv H4.
      auto.
    - exfalso.
      elim (rqrsDTree_rqUp_rqUp_not_eq n H5 H1); auto.
  Qed.

  Lemma RqRsDownMatch_rs_eq:
    forall oidx rqTos rssFrom1 rssFrom2 P1 P2,
      RqRsDownMatch dtr oidx rqTos rssFrom1 P1 ->
      RqRsDownMatch dtr oidx rqTos rssFrom2 P2 ->
      rssFrom1 = rssFrom2.
  Proof.
    unfold RqRsDownMatch; intros; dest.
    clear H H0.
    generalize dependent rssFrom1.
    generalize dependent rssFrom2.
    induction rqTos; simpl; intros.
    - destruct rssFrom1, rssFrom2; simpl in *; try discriminate.
      reflexivity.
    - destruct rssFrom1 as [|rsFrom1 rssFrom1]; [discriminate|].
      destruct rssFrom2 as [|rsFrom2 rssFrom2]; [discriminate|].
      simpl in *.
      inv H1; inv H2; inv H3; inv H4.
      destruct H5 as [cidx1 ?]; destruct H3 as [cidx2 ?]; dest.
      simpl in *.
      f_equal.
      + destruct (eq_nat_dec cidx1 cidx2); subst.
        * rewrite H10 in H5; inv H5; reflexivity.
        * exfalso.
          elim (rqrsDTree_down_down_not_eq n H9 H4); auto.
      + eapply IHrqTos; eauto.
  Qed.

  Lemma RqRsDownMatch_rq_not_nil:
    forall oidx rqTos rssFrom P,
      RqRsDownMatch dtr oidx rqTos rssFrom P ->
      rqTos <> nil.
  Proof.
    unfold RqRsDownMatch; intros; dest; assumption.
  Qed.
    
  Lemma RqRsDownMatch_rs_not_nil:
    forall oidx rqTos rssFrom P,
      RqRsDownMatch dtr oidx rqTos rssFrom P ->
      rssFrom <> nil.
  Proof.
    unfold RqRsDownMatch; intros; dest.
    destruct rssFrom; [|discriminate].
    destruct rqTos; auto.
    simpl in H0; discriminate.
  Qed.
  
  Lemma footprintUpDownOk_rs_eq:
    forall {oifc} (sys: System oifc) oidx rqFrom rqTos rssFrom1 rsbTo1 rssFrom2 rsbTo2,
      FootprintUpDownOk dtr sys oidx rqFrom rqTos rssFrom1 rsbTo1 ->
      FootprintUpDownOk dtr sys oidx rqFrom rqTos rssFrom2 rsbTo2 ->
      rssFrom1 = rssFrom2 /\ rsbTo1 = rsbTo2.
  Proof.
    unfold FootprintUpDownOk; intros.
    destruct H as [cidx1 [cobj1 ?]]; destruct H0 as [cidx2 [cobj2 ?]]; dest; subst.
    split.
    - eapply RqRsDownMatch_rs_eq; eauto.
    - destruct (eq_nat_dec (obj_idx cobj1) (obj_idx cobj2)).
      + rewrite e in H9; rewrite H9 in H4; inv H4; reflexivity.
      + exfalso.
        elim (rqrsDTree_rqUp_rqUp_not_eq n H8 H3); auto.
  Qed.

  Lemma footprintDownDownOk_rs_eq:
    forall oidx rqFrom rqTos rssFrom1 rsbTo1 rssFrom2 rsbTo2,
      FootprintDownDownOk dtr oidx rqFrom rqTos rssFrom1 rsbTo1 ->
      FootprintDownDownOk dtr oidx rqFrom rqTos rssFrom2 rsbTo2 ->
      rssFrom1 = rssFrom2 /\ rsbTo1 = rsbTo2.
  Proof.
    unfold FootprintDownDownOk; intros.
    dest; split.
    - eapply RqRsDownMatch_rs_eq; eauto.
    - rewrite H3 in H1; inv H1; reflexivity.
  Qed.
  
End RqRsDTree.

(** Ltacs for discharging conditions *)

Ltac disc_rule_custom := idtac.

Ltac disc_rule_conds_unit_rule_preds_red :=
  match goal with
  | [H: ImmDownRule _ _ _ |- _] => red in H; dest
  | [H: ImmUpRule _ _ _ |- _] => red in H; dest
  | [H: RqFwdRule _ _ _ _ |- _] => red in H; dest
  | [H: RqFwdRuleCommon _ |- _] => red in H; dest
  | [H: RqUpUp _ _ ?rule \/
        RqUpDown _ _ _ ?rule \/
        RqDownDown _ _ ?rule |- _] => destruct H as [|[|]]
  | [H: RqUpUp _ _ _ |- _] => red in H; dest
  | [H: RqUpDown _ _ _ _ |- _] => red in H; dest
  | [H: RqDownDown _ _ _ |- _] => red in H; dest
  | [H: RsBackRule _ |- _] => red in H; dest
  | [H: RsBackRuleCommon _ |- _] => red in H; dest
  | [H: RsDownDown ?rule \/ RsUp ?rule |- _] => destruct H
  | [H: RsDownDown ?rule |- _] => red in H; dest
  | [H: RsUp ?rule |- _] => red in H; dest
  | [H: RsDownRqDownRule _ _ _ _ |- _] => red in H; dest

  | [H: RqAccepting _ _ _ |- _] => red in H
  | [H: RsAccepting _ _ _ |- _] => red in H
  | [H: RqReleasing _ |- _] => red in H
  | [H: RsReleasing _ |- _] => red in H
  | [H: StateSilent _ |- _] => red in H

  | [H: FootprintReleasingUp _ |- _] => red in H; dest
  | [H: FootprintReleasingDown _ |- _] => red in H; dest
  | [H: FootprintingUp _ _ _ _ _ |- _] =>
    let rqi := fresh "rqi" in
    destruct H as [rqi ?]; dest
  | [H: FootprintingDown _ _ _ _ _ |- _] =>
    let rqi := fresh "rqi" in
    destruct H as [rqi ?]; dest
  | [H: FootprintingUpToDown _ _ _ |- _] =>
    let prqi := fresh "rqi" in
    let nrqi := fresh "rqi" in
    destruct H as [prqi [nrqi ?]]; dest
  | [H: FootprintedUp _ _ _ |- _] =>
    let rqi := fresh "rqi" in
    destruct H as [rqi ?]; dest
  | [H: FootprintedDown _ _ _ |- _] =>
    let rqi := fresh "rqi" in
    destruct H as [rqi ?]; dest

  | [H: FootprintSilent _ |- _] => red in H; dest
  | [H: FootprintUpSilent _ |- _] => red in H
  | [H: FootprintDownSilent _ |- _] => red in H
  | [H: DownLockFree _ _ _ |- _] => red in H
  | [H: DownLockFreeORq _ |- _] => red in H
  | [H: UpLockFree _ _ _ |- _] => red in H
  | [H: UpLockFreeORq _ |- _] => red in H

  | [H: FootprintReleasingUpPost _ _ _ _ _ _ |- _] =>
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    let rsm := fresh "rsm" in
    destruct H as [rssFrom [rsbTo [rsm ?]]]; dest
  | [H: FootprintReleasingDownPost _ _ _ _ _ _ |- _] =>
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    let rsm := fresh "rsm" in
    destruct H as [rssFrom [rsbTo [rsm ?]]]; dest
  | [H: ImmDownOk _ _ _ _ _ _ _ _ |- _] =>
    let cidx := fresh "cidx" in
    let rqFrom := fresh "rqFrom" in
    let rqm := fresh "rqm" in
    let rsTo := fresh "rsTo" in
    let rsm := fresh "rsm" in
    destruct H as [cidx [rqFrom [rqm [rsTo [rsm ?]]]]]; dest
  | [H: ImmUpOk _ _ _ _ _ _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqm := fresh "rqm" in
    let rsTo := fresh "rsTo" in
    let rsm := fresh "rsm" in
    destruct H as [rqFrom [rqm [rsTo [rsm ?]]]]; dest
  | [H: RqUpUpOk _ _ _ _ _ _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqfm := fresh "rqfm" in
    let rqTo := fresh "rqTo" in
    let rqtm := fresh "rqtm" in
    let rsFrom := fresh "rsFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rqFrom [rqfm [rqTo [rqtm [rsFrom [rsbTo ?]]]]]]; dest
  | [H: RqUpDownOk _ _ _ _ _ _ _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqfm := fresh "rqfm" in
    let rqTos := fresh "rqTos" in
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rqFrom [rqfm [rqTos [rssFrom [rsbTo ?]]]]]; dest
  | [H: RqDownDownOk _ _ _ _ _ _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqfm := fresh "rqfm" in
    let rqTos := fresh "rqTos" in
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rqFrom [rqfm [rqTos [rssFrom [rsbTo ?]]]]]; dest
  | [H: RsDownRqDownOk _ _ _ _ _ _ _ _ _ |- _] =>
    let rsFrom := fresh "rsFrom" in
    let rsm := fresh "rsm" in
    let rqTos := fresh "rqTos" in
    let rqOrig := fresh "rqOrig" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rsFrom [rsm [rqTos [rqOrig [rsbTo ?]]]]]; dest
  end.

Ltac disc_rule_conds_unit_rule_preds_inst :=
  match goal with
  | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
  | [H1: RulePrecSat ?rule _, H2: rule_precond ?rule _ _ _ |- _] =>
    pmarked2 H1 H2;
    let Hp := fresh "H" in
    pose proof (H1 _ _ _ H2) as Hp;
    pmark2 H1 H2
  | [H: (?nost, ?norq, ?routs) = rule_trs ?rule ?ost ?orq ?ins |- _] =>
    apply eq_sym in H
  | [H1: RulePostSat ?rule _, H2: rule_precond ?rule ?ost ?orq ?ins,
     H3: rule_trs ?rule ?ost ?orq ?ins = (?nost, ?norq, ?routs) |- _] =>
    pmarked2 H1 H3;
    let Hp := fresh "H" in
    pose proof (H1 _ _ _ H2 _ _ _ H3) as Hp;
    pmark2 H1 H3
  end.
           
Ltac disc_rule_conds_rule_preds_clear :=
  match goal with
  | [H: RulePrecSat _ _ |- _] => clear H
  | [H: RulePostSat _ _ |- _] => clear H
  end.

Ltac disc_rule_minds :=
  match goal with
  | [H1: parentIdxOf _ ?idx = Some _, H2: parentIdxOf _ ?idx = Some _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: rqEdgeUpFrom _ ?idx = Some _, H2: rqEdgeUpFrom _ ?idx = Some _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: rsEdgeUpFrom _ ?idx = Some _, H2: rsEdgeUpFrom _ ?idx = Some _ |- _] =>
    rewrite H1 in H2; inv H2
  | [H1: edgeDownTo _ ?idx = Some _, H2: edgeDownTo _ ?idx = Some _ |- _] =>
    rewrite H1 in H2; inv H2

  | [H: RqRsDTree _ _,
     H1: rqEdgeUpFrom _ ?idx1 = Some ?midx,
     H2: rqEdgeUpFrom _ ?idx2 = Some ?midx |- _] =>
    let Heq := fresh "Heq" in
    let Hneq := fresh "Hneq" in
    destruct (eq_nat_dec idx1 idx2) as [Heq|Hneq];
    [rewrite Heq in *; clear H2
    |elim (rqrsDTree_rqUp_rqUp_not_eq H Hneq H1 H2); reflexivity]
  | [H: RqRsDTree _ _,
     H1: rsEdgeUpFrom _ ?idx1 = Some ?midx,
     H2: rsEdgeUpFrom _ ?idx2 = Some ?midx |- _] =>
    let Heq := fresh "Heq" in
    let Hneq := fresh "Hneq" in
    destruct (eq_nat_dec idx1 idx2) as [Heq|Hneq];
    [rewrite Heq in *; clear H2
    |elim (rqrsDTree_rsUp_rsUp_not_eq H Hneq H1 H2); reflexivity]
  | [H: RqRsDTree _ _,
     H1: edgeDownTo _ ?idx1 = Some ?midx,
     H2: edgeDownTo _ ?idx2 = Some ?midx |- _] =>
    let Heq := fresh "Heq" in
    let Hneq := fresh "Hneq" in
    destruct (eq_nat_dec idx1 idx2) as [Heq|Hneq];
    [rewrite Heq in *; clear H2
    |elim (rqrsDTree_down_down_not_eq H Hneq H1 H2); reflexivity]
  end.

Ltac disc_rule_conds_unit_simpl :=
  match goal with
  | [H: Some _ = Some _ |- _] => inv H
  | [H: Some _ = None |- _] => discriminate
  | [H: None = Some _ |- _] => discriminate
  | [H1: ?t = None, H2: context[?t] |- _] => rewrite H1 in H2; simpl in H2
  | [H1: ?t = Some _, H2: context[?t] |- _] => rewrite H1 in H2; simpl in H2
  | [H1: None = ?t, H2: context[?t] |- _] => rewrite <-H1 in H2; simpl in H2
  | [H1: Some _ = ?t, H2: context[?t] |- _] => rewrite <-H1 in H2; simpl in H2
  | [H1: ?t = None |- context[?t]] => rewrite H1; simpl
  | [H1: ?t = Some _ |- context[?t]] => rewrite H1; simpl
  | [H1: None = ?t |- context[?t]] => rewrite <-H1; simpl
  | [H1: Some _ = ?t |- context[?t]] => rewrite <-H1; simpl

  | [H: Forall _ (_ :: _) |- _] => inv H
  | [H: Forall _ nil |- _] => clear H

  | [H: (_, _) = (_, _) |- _] => inv H
  | [H: idsOf ?ivs = _ :: nil |- _] =>
    destruct ivs; [discriminate|simpl in H; inv H]
  | [H: idsOf ?ivs = nil |- _] => destruct ivs; [|discriminate]
  | [H: _ :: nil = _ :: nil |- _] => inv H
  | [H: _ :: nil = idsOf ?ivs |- _] => apply eq_sym in H
  | [H: nil = idsOf ?ivs |- _] => apply eq_sym in H
  | [H: nil = nil |- _] => clear H

  | [H1: msg_type ?msg = MRq, H2: msg_type ?msg = MRs |- _] =>
    rewrite H1 in H2; discriminate
                                 
  | [H: rqi_msg _ = _ |- _] => rewrite H in *
  | [H: rqi_minds_rss _ = _ |- _] => rewrite H in *
  | [H: rqi_midx_rsb _ = _ |- _] => rewrite H in *
  end.

Ltac disc_rule_conds_rule_preds :=
  repeat
    (repeat disc_rule_conds_unit_rule_preds_red;
     repeat disc_rule_conds_unit_rule_preds_inst);
  repeat disc_rule_conds_rule_preds_clear;
  pmark_clear.

Ltac disc_rule_conds :=
  repeat
    (repeat disc_rule_conds_rule_preds;
     repeat disc_rule_minds;
     repeat disc_rule_conds_unit_simpl;
     try disc_rule_custom;
     simpl in *; subst; mred;
     try reflexivity; try eassumption).

Ltac solve_rule_conds :=
  repeat red;
  repeat
    (repeat
       match goal with
       | [ |- exists _, _] => eexists
       | [ |- _ /\ _] => split
       end;
     try reflexivity; try eassumption).

Definition rqsQ (msgs: MessagePool Msg) (midx: IdxT) :=
  filter (fun msg => msg.(msg_type) ==n MRq) (findQ midx msgs).

Definition rssQ (msgs: MessagePool Msg) (midx: IdxT) :=
  filter (fun msg => msg.(msg_type) ==n MRs) (findQ midx msgs).

Lemma findQ_length_zero:
  forall (msgs: MessagePool Msg) midx msg,
    length (findQ midx msgs) <= 1 ->
    FirstMP msgs midx msg ->
    findQ midx (deqMP midx msgs) = nil.
Proof.
  intros.
  apply findQ_In_deqMP_FirstMP in H0.
  unfold FirstMP, firstMP in *; simpl in *.
  destruct (findQ midx msgs); [discriminate|].
  inv H0.
  simpl in H.
  destruct (findQ _ _); [reflexivity|simpl in H; omega].
Qed.

Lemma findQ_length_zero_False:
  forall (msgs: MessagePool Msg) midx msg,
    findQ midx msgs = nil ->
    FirstMP msgs midx msg ->
    False.
Proof.
  unfold FirstMP, firstMP; simpl; intros.
  destruct (findQ midx msgs); discriminate.
Qed.

Lemma findQ_length_one:
  forall (msgs: MessagePool Msg) midx msg,
    length (findQ midx msgs) <= 1 ->
    FirstMP msgs midx msg ->
    length (findQ midx msgs) = 1.
Proof.
  intros.
  remember (findQ midx msgs) as q; destruct q.
  - exfalso; eapply FirstMP_findQ_False; eauto.
  - simpl in *; omega.
Qed.

Lemma rqsQ_length_zero:
  forall (msgs: MessagePool Msg) midx msg,
    length (rqsQ msgs midx) <= 1 ->
    FirstMP msgs midx msg ->
    msg_type msg = MRq ->
    rqsQ (deqMP midx msgs) midx = nil.
Proof.
  intros.
  apply findQ_In_deqMP_FirstMP in H0.
  unfold rqsQ, FirstMP, firstMP in *; simpl in *.
  destruct (findQ midx msgs); [discriminate|].
  inv H0.
  simpl in H; rewrite H1 in H; simpl in H.
  destruct (filter _ _); [reflexivity|simpl in H; omega].
Qed.

Lemma rqsQ_length_zero_False:
  forall msgs midx msg,
    rqsQ msgs midx = nil ->
    msg_type msg = MRq ->
    FirstMP msgs midx msg ->
    False.
Proof.
  unfold rqsQ, FirstMP, firstMP; simpl; intros.
  destruct (findQ midx msgs); [discriminate|].
  inv H1.
  simpl in H; rewrite H0 in H; simpl in H.
  discriminate.
Qed.

Lemma rqsQ_length_ge_one:
  forall msgs midx msg,
    msg_type msg = MRq ->
    InMP midx msg msgs ->
    length (rqsQ msgs midx) >= 1.
Proof.
  unfold rqsQ, InMP; intros.
  induction (findQ midx msgs); simpl; intros.
  - elim H0.
  - inv H0.
    + rewrite H; simpl; omega.
    + find_if_inside; simpl; [omega|auto].
Qed.

Lemma rqsQ_length_one:
  forall msgs midx msg,
    length (rqsQ msgs midx) <= 1 ->
    msg_type msg = MRq ->
    FirstMP msgs midx msg ->
    length (rqsQ msgs midx) = 1.
Proof.
  intros.
  apply FirstMP_InMP in H1.
  eapply rqsQ_length_ge_one in H1; [|assumption].
  omega.
Qed.

Lemma rssQ_length_zero:
  forall (msgs: MessagePool Msg) midx msg,
    length (rssQ msgs midx) <= 1 ->
    FirstMP msgs midx msg ->
    msg_type msg = MRs ->
    rssQ (deqMP midx msgs) midx = nil.
Proof.
  intros.
  apply findQ_In_deqMP_FirstMP in H0.
  unfold rssQ, FirstMP, firstMP in *; simpl in *.
  destruct (findQ midx msgs); [discriminate|].
  inv H0.
  simpl in H; rewrite H1 in H; simpl in H.
  destruct (filter _ _); [reflexivity|simpl in H; omega].
Qed.

Lemma rssQ_length_zero_False:
  forall msgs midx msg,
    rssQ msgs midx = nil ->
    msg_type msg = MRs ->
    FirstMP msgs midx msg ->
    False.
Proof.
  unfold rssQ, FirstMP, firstMP; simpl; intros.
  destruct (findQ midx msgs); [discriminate|].
  inv H1.
  simpl in H; rewrite H0 in H; simpl in H.
  discriminate.
Qed.

Lemma rssQ_length_ge_one:
  forall msgs midx msg,
    msg_type msg = MRs ->
    InMP midx msg msgs ->
    length (rssQ msgs midx) >= 1.
Proof.
  unfold rssQ, InMP; intros.
  induction (findQ midx msgs); simpl; intros.
  - elim H0.
  - inv H0.
    + rewrite H; simpl; omega.
    + find_if_inside; simpl; [omega|auto].
Qed.

Lemma rssQ_length_one:
  forall msgs midx msg,
    length (rssQ msgs midx) <= 1 ->
    msg_type msg = MRs ->
    FirstMP msgs midx msg ->
    length (rssQ msgs midx) = 1.
Proof.
  intros.
  apply FirstMP_InMP in H1.
  eapply rssQ_length_ge_one in H1; [|assumption].
  omega.
Qed.

Lemma rssQ_enqMP_rq:
  forall msgs rqMIdx rqm midx,
    msg_type rqm = MRq ->
    rssQ (enqMP rqMIdx rqm msgs) midx =
    rssQ msgs midx.
Proof.
  unfold rssQ, findQ, enqMP; intros.
  mred; simpl.
  rewrite filter_app; simpl.
  rewrite H; simpl.
  rewrite app_nil_r; reflexivity.
Qed.

Lemma rssQ_enqMsgs_rqs:
  forall rqs msgs midx,
    Forall (fun idm => msg_type (valOf idm) = MRq) rqs ->
    rssQ (enqMsgs rqs msgs) midx =
    rssQ msgs midx.
Proof.
  induction rqs; simpl; intros; [reflexivity|].
  inv H.
  destruct a as [rqMIdx rqm]; simpl in *.
  rewrite IHrqs by assumption.
  apply rssQ_enqMP_rq; auto.
Qed.

Lemma rqsQ_enqMP_rs:
  forall msgs rsMIdx rsm midx,
    msg_type rsm = MRs ->
    rqsQ (enqMP rsMIdx rsm msgs) midx =
    rqsQ msgs midx.
Proof.
  unfold rqsQ, findQ, enqMP; intros.
  mred; simpl.
  rewrite filter_app; simpl.
  rewrite H; simpl.
  rewrite app_nil_r; reflexivity.
Qed.

Lemma rqsQ_enqMsgs_rss:
  forall rss msgs midx,
    Forall (fun idm => msg_type (valOf idm) = MRs) rss ->
    rqsQ (enqMsgs rss msgs) midx =
    rqsQ msgs midx.
Proof.
  induction rss; simpl; intros; [reflexivity|].
  inv H.
  destruct a as [rsMIdx rsm]; simpl in *.
  rewrite IHrss by assumption.
  apply rqsQ_enqMP_rs; auto.
Qed.

Lemma rqsQ_deqMP_rs:
  forall rsMIdx rsm msgs midx,
    FirstMP msgs rsMIdx rsm ->
    msg_type rsm = MRs ->
    rqsQ (deqMP rsMIdx msgs) midx =
    rqsQ msgs midx.
Proof.
  unfold rqsQ, FirstMP, firstMP, deqMP; intros.
  remember (findQ rsMIdx msgs) as q.
  destruct q as [|msg q]; [discriminate|].
  inv H.
  unfold findQ in *; mred; simpl.
  rewrite <-Heqq.
  simpl; rewrite H0; reflexivity.
Qed.

Lemma rqsQ_deqMsgs_rss:
  forall rss msgs midx,
    NoDup (idsOf rss) ->
    Forall (FirstMPI msgs) rss ->
    Forall (fun idm => msg_type (valOf idm) = MRs) rss ->
    rqsQ (deqMsgs (idsOf rss) msgs) midx =
    rqsQ msgs midx.
Proof.
  induction rss; simpl; intros; [reflexivity|].
  inv H; inv H0; inv H1.
  destruct a as [rsMIdx rsm]; simpl in *.
  rewrite IHrss; auto.
  - eapply rqsQ_deqMP_rs; eauto.
  - apply Forall_forall; intros [nrsMIdx nrsm] ?.
    apply FirstMP_deqMP; simpl.
    + intro Hx; subst; elim H4.
      apply in_map with (f:= idOf) in H; auto.
    + rewrite Forall_forall in H6.
      specialize (H6 _ H); assumption.
Qed.

Ltac solve_midx_neq_unit :=
  match goal with
  | [Hw: WfDTree ?dtr, H: parentIdxOf ?dtr ?cidx = Some ?pidx |- _] =>
    isNew (cidx <> pidx);
    pose proof (parentIdxOf_not_eq Hw H)
  | [Hp1: parentIdxOf _ ?oidx1 = Some ?pidx1,
     Hp2: parentIdxOf _ ?oidx2 = Some ?pidx2,
     Hneq: Some ?pidx1 <> Some ?pidx2 |- _] =>
    isNew (oidx1 <> oidx2);
    assert (oidx1 <> oidx2)
      by (intro; subst;
          rewrite <-Hp1, <-Hp2 in Hneq;
          elim Hneq; reflexivity)
                               
  | [H: Some _ = rqEdgeUpFrom _ _ |- _] => apply eq_sym in H
  | [H: Some _ = rsEdgeUpFrom _ _ |- _] => apply eq_sym in H
  | [H: Some _ = edgeDownTo _ _ |- _] => apply eq_sym in H
  | [H: None = rqEdgeUpFrom _ _ |- _] => apply eq_sym in H
  | [H: None = rsEdgeUpFrom _ _ |- _] => apply eq_sym in H
  | [H: None = edgeDownTo _ _ |- _] => apply eq_sym in H

  | [Hidx: ?idx1 <> ?idx2,
     Hru1: rqEdgeUpFrom _ ?idx1 = Some ?rqUp1,
     Hru2: rqEdgeUpFrom _ ?idx2 = Some ?rqUp2 |- ?rqUp1 <> ?rqUp2] =>
    eapply rqrsDTree_rqUp_rqUp_not_eq
      with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hidx: ?idx2 <> ?idx1,
     Hru1: rqEdgeUpFrom _ ?idx1 = Some ?rqUp1,
     Hru2: rqEdgeUpFrom _ ?idx2 = Some ?rqUp2 |- ?rqUp1 <> ?rqUp2] =>
    eapply rqrsDTree_rqUp_rqUp_not_eq
      with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hidx: ?idx1 <> ?idx2,
     Hru1: rsEdgeUpFrom _ ?idx1 = Some ?rsUp1,
     Hru2: rsEdgeUpFrom _ ?idx2 = Some ?rsUp2 |- ?rsUp1 <> ?rsUp2] =>
    eapply rqrsDTree_rsUp_rsUp_not_eq
      with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hidx: ?idx2 <> ?idx1,
     Hru1: rsEdgeUpFrom _ ?idx1 = Some ?rsUp1,
     Hru2: rsEdgeUpFrom _ ?idx2 = Some ?rsUp2 |- ?rsUp1 <> ?rsUp2] =>
    eapply rqrsDTree_rsUp_rsUp_not_eq
      with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hidx: ?idx1 <> ?idx2,
     Hd1: edgeDownTo _ ?idx1 = Some ?down1,
     Hd2: edgeDownTo _ ?idx2 = Some ?down2 |- ?down1 <> ?down2] =>
    eapply rqrsDTree_down_down_not_eq
      with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hidx: ?idx2 <> ?idx1,
     Hd1: edgeDownTo _ ?idx1 = Some ?down1,
     Hd2: edgeDownTo _ ?idx2 = Some ?down2 |- ?down1 <> ?down2] =>
    eapply rqrsDTree_down_down_not_eq
      with (oidx1:= idx1) (oidx2:= idx2); eauto

  | [Hrq: rqEdgeUpFrom _ ?idx1 = Some ?rqUp,
     Hrs: rsEdgeUpFrom _ ?idx2 = Some ?rsUp |- ?rqUp <> ?rsUp] =>
    eapply rqrsDTree_rqUp_rsUp_not_eq with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hrq: rqEdgeUpFrom _ ?idx1 = Some ?rqUp,
     Hrs: rsEdgeUpFrom _ ?idx2 = Some ?rsUp |- ?rsUp <> ?rqUp] =>
    apply neq_sym;
    eapply rqrsDTree_rqUp_rsUp_not_eq with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hrq: rqEdgeUpFrom _ ?idx1 = Some ?rqUp,
     Hd: edgeDownTo _ ?idx2 = Some ?down |- ?rqUp <> ?down] =>
    eapply rqrsDTree_rqUp_down_not_eq with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hrq: rqEdgeUpFrom _ ?idx1 = Some ?rqUp,
     Hd: edgeDownTo _ ?idx2 = Some ?down |- ?down <> ?rqUp] =>
    apply neq_sym;
    eapply rqrsDTree_rqUp_down_not_eq with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hrs: rsEdgeUpFrom _ ?idx1 = Some ?rsUp,
     Hd: edgeDownTo _ ?idx2 = Some ?down |- ?rsUp <> ?down] =>
    eapply rqrsDTree_rsUp_down_not_eq with (oidx1:= idx1) (oidx2:= idx2); eauto
  | [Hrs: rsEdgeUpFrom _ ?idx1 = Some ?rsUp,
     Hd: edgeDownTo _ ?idx2 = Some ?down |- ?down <> ?rsUp] =>
    apply neq_sym;
    eapply rqrsDTree_rsUp_down_not_eq with (oidx1:= idx1) (oidx2:= idx2); eauto

  | [Hru1: rqEdgeUpFrom _ ?idx1 = Some ?rqUp1,
     Hdowns2: RqRsDownMatch _ ?idx2 ?downs2 _ _ |- ~ In ?rqUp1 ?downs2] =>
    eapply rqrsDTree_rqUp_downs_not_in; eauto
  | [Hru1: rsEdgeUpFrom _ ?idx1 = Some ?rsUp1,
     Hdowns2: RqRsDownMatch _ ?idx2 ?downs2 _ _ |- ~ In ?rsUp1 ?downs2] =>
    eapply rqrsDTree_rsUp_downs_not_in; eauto
  | [Hdown1: edgeDownTo _ ?idx = Some ?down1,
     Hdowns2: RqRsDownMatch _ ?idx ?downs2 _ _ |- ~ In ?down1 ?downs2] =>
    eapply rqrsDTree_down_downs_not_in; eauto

  | [Hru1: rqEdgeUpFrom _ ?idx1 = Some ?rqUp1,
     Hdowns2: RqRsDownMatch _ ?idx2 _ ?ups2 _ |- ~ In ?rqUp1 ?ups2] =>
    eapply rqrsDTree_rqUp_ups_not_in; eauto
  | [Hru1: rsEdgeUpFrom _ ?idx = Some ?rsUp1,
     Hdowns2: RqRsDownMatch _ ?idx _ ?ups2 _ |- ~ In ?rsUp1 ?ups2] =>
    eapply rqrsDTree_rsUp_ups_not_in; eauto
  | [Hdown1: edgeDownTo _ ?idx1 = Some ?down1,
     Hdowns2: RqRsDownMatch _ ?idx2 _ ?ups2 _ |- ~ In ?down1 ?ups2] =>
    eapply rqrsDTree_down_ups_not_in; eauto

  | [Hru1: rsEdgeUpFrom _ ?idx1 = Some ?rsUp1,
     Hdowns2: RqRsDownMatch _ ?idx2 _ ?ups2 _,
     Hp: parentIdxOf _ ?idx1 = Some ?pidx,
     Hnp: Some ?pidx <> Some ?idx2 |- ~ In ?rqUp1 ?ups2] =>
    rewrite <-Hp in Hnp;
    eapply rqrsDTree_rsUp_ups_not_in_parent; eauto
  | [Hdown1: edgeDownTo _ ?idx1 = Some ?down1,
     Hdowns2: RqRsDownMatch _ ?idx2 ?downs2 _ _,
     Hp: parentIdxOf _ ?idx1 = Some ?pidx,
     Hnp: Some ?pidx <> Some ?idx2 |- ~ In ?down1 ?downs2] =>
    rewrite <-Hp in Hnp;
    eapply rqrsDTree_down_downs_not_in_parent; eauto

  | [Hdown1: edgeDownTo _ ?idx1 = Some ?down1,
     Hdowns2: RqRsDownMatch _ ?idx2 ?downs2 _ (fun _ => _ <> ?idx1) |- ~ In ?down1 ?downs2] =>
    eapply rqrsDTree_down_downs_not_in_child_P; eauto

  | [Hp: parentIdxOf _ ?cidx = Some ?oidx,
     Hdown: edgeDownTo _ ?cidx = Some ?down,
     Hup: rsEdgeUpFrom _ ?cidx = Some ?rsUp,
     Hnin: ~ In ?rsUp ?ups,
     Hud: RqRsDownMatch _ ?oidx ?downs ?ups _ |- ~ In ?down ?downs] =>
    eapply rqrsDTree_down_downs_not_in_child; eauto
  end.

Ltac solve_midx_neq :=
  repeat solve_midx_neq_unit; fail.

Ltac solve_q_unit :=
  match goal with
  | [ |- context[let (_, _) := ?idm in _] ] =>
    let midx := fresh "midx" in
    let msg := fresh "msg" in
    destruct idm as [midx msg]; simpl in *
                                         
  | [ |- context[findQ _ (enqMsgs _ _)] ] =>
    rewrite findQ_not_In_enqMsgs; [|solve_midx_neq]
  | [ |- context[findQ _ (deqMsgs _ _)] ] =>
    rewrite findQ_not_In_deqMsgs; [|solve_midx_neq]
  | [ |- context[findQ _ (enqMP _ _ _)] ] =>
    rewrite findQ_not_In_enqMP; [|solve_midx_neq]
  | [ |- context[findQ _ (deqMP _ _)] ] =>
    rewrite findQ_not_In_deqMP; [|solve_midx_neq]

  | [ |- context[findQ _ (enqMP _ _ _)] ] =>
    rewrite findQ_In_enqMP
  end.

Ltac solve_q :=
  unfold rssQ, rqsQ;
  repeat solve_q_unit;
  try reflexivity.

Ltac solve_midx_disj :=
  repeat
    match goal with
    | [ |- _ <> _] => solve_midx_neq
    | [ |- ~ In _ _] => solve_midx_neq
    | [ |- DisjList (_ :: nil) (_ :: nil)] =>
      apply (DisjList_singletons eq_nat_dec)
    | [ |- DisjList (_ :: nil) _] =>
      apply (DisjList_singleton_1 eq_nat_dec)
    | [ |- DisjList _ (_ :: nil)] =>
      apply (DisjList_singleton_2 eq_nat_dec)
    end.

