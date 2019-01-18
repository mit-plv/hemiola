Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** Useful invariants on top of [RqRsSys] *)

Ltac inv_steps :=
  repeat
    match goal with
    | [H: steps _ _ _ _ _ |- _] => inv H
    end.

Ltac inv_step :=
  repeat
    match goal with
    | [H: step_m _ _ (RlblInt _ _ _ _) _ |- _] => inv H
    | [H: {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} =
          {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} |- _] => inv H
    end.

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
  | [H: GoodRqRsRule _ _ rule |- _] =>
    destruct H as [|[|[|[|]]]]
  end.

Ltac disc_rule_custom := idtac.

Ltac disc_rule_conds_unit_rule_preds :=
  match goal with
  | [H: ImmDownRule _ _ _ |- _] =>
    let cidx := fresh "cidx" in
    let rqFrom := fresh "rqFrom" in
    let rsTo := fresh "rsTo" in
    destruct H as [cidx [rqFrom [rsTo ?]]]; dest
  | [H: ImmUpRule _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rsTo := fresh "rsTo" in
    destruct H as [rqFrom [rsTo ?]]; dest
  | [H: RqFwdRule _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqTos := fresh "rqTos" in
    let Hft := fresh "H" in
    red in H;
    destruct H as [rqFrom [rqTos [? Hft]]];
    red in Hft; dest
  | [H: RqFwdFromTo _ _ _ |- _] => red in H; dest
  | [H: RqUpUp _ _ _ _ ?rule \/
        RqUpDown _ _ _ _ ?rule \/
        RqDownDown _ _ _ _ ?rule |- _] =>
    destruct H as [|[|]]
  | [H: RqUpUp _ _ _ _ _ |- _] =>
    let rqTo := fresh "rqTo" in
    let rsFrom := fresh "rsFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [? [rqTo [rsFrom [rsbTo ?]]]]; dest
  | [H: RqUpDown _ _ _ _ _ |- _] =>
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [? [rssFrom [rsbTo ?]]]; dest
  | [H: RqDownDown _ _ _ _ _ |- _] =>
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [? [rssFrom [rsbTo ?]]]; dest
  | [H: RsBackRule _ |- _] =>
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    let Hft := fresh "H" in
    destruct H as [rssFrom [rsbTo [? Hft]]];
    red in Hft; dest
  | [H: RsBackFromTo _ _ _ |- _] => red in H; dest
  | [H: RsDownRqDownRule _ _ _ |- _] =>
    let rsFrom := fresh "rsFrom" in
    let rqTos := fresh "rqTos" in
    destruct H as [rsFrom [rqTos ?]]; dest
  | [H: MsgsFrom _ _ _ _ |- _] => red in H
  | [H: MsgsTo _ _ |- _] => red in H
  | [H: RqAccepting _ _ _ |- _] => red in H
  | [H: RsAccepting _ _ _ |- _] => red in H
  | [H: RqReleasing _ |- _] => red in H
  | [H: RsReleasing _ |- _] => red in H
  | [H: DownLockFree _ _ _ |- _] => red in H
  | [H: DownLockFreeORq _ |- _] => red in H
  | [H: UpLockFree _ _ _ |- _] => red in H
  | [H: UpLockFreeORq _ |- _] => red in H
  | [H: StateSilent _ |- _] => red in H
  end.

Ltac disc_rule_conds_unit_footprint :=
  match goal with
  | [H: (FootprintReleasingUp _ _ _ /\ _) \/
        (FootprintReleasingDown _ _ _ /\ _) |- _] => destruct H; dest
  | [H: FootprintReleasingUp _ _ _ |- _] => red in H; dest
  | [H: FootprintReleasingDown _ _ _ |- _] => red in H; dest
  | [H: FootprintingUp _ _ _ |- _] => red in H
  | [H: FootprintingDown _ _ _ |- _] => red in H
  | [H: FootprintedUp _ _ _ |- _] =>
    let rqi := fresh "rqi" in
    destruct H as [rqi ?]; dest
  | [H: FootprintedDown _ _ _ |- _] =>
    let rqi := fresh "rqi" in
    destruct H as [rqi ?]; dest
  | [H: exists _:RqInfo Msg, _ |- _] =>
    let rqi := fresh "rqi" in
    destruct H as [rqi ?]; dest
  | [H: FootprintUpToDown _ _ _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rsbTo := fresh "rsbTo" in
    let nrssFrom := fresh "nrssFrom" in
    destruct H as [rqFrom [rsbTo [nrssFrom ?]]]; dest
  | [H: FootprintingUpToDown _ _ _ _ |- _] => destruct H
  | [H: FootprintSilent _ |- _] => red in H; dest
  | [H: FootprintUpSilent _ |- _] => red in H
  | [H: FootprintDownSilent _ |- _] => red in H
  | [H: DownLockFree _ _ _ |- _] => red in H
  | [H: DownLockFreeORq _ |- _] => red in H
  | [H: UpLockFree _ _ _ |- _] => red in H
  | [H: UpLockFreeORq _ |- _] => red in H
  end.

Ltac disc_rule_conds_unit_simpl :=
  match goal with
  | [H1: rule_precond ?rule ->oprec _, H2: rule_precond ?rule _ _ _ |- _] =>
    specialize (H1 _ _ _ H2)
  | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
  | [H1: rule_trs ?rule ?ost ?orq ?ins = _, H2: context[rule_trs ?rule _ _ _] |- _] =>
    specialize (H2 ost orq ins); rewrite H1 in H2; simpl in H2

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

  | [H: idsOf ?ivs = _ :: nil |- _] =>
    destruct ivs; [discriminate|simpl in H; inv H]
  | [H: idsOf ?ivs = nil |- _] => destruct ivs; [|discriminate]
  | [H: _ :: nil = _ :: nil |- _] => inv H
  | [H: _ :: nil = idsOf ?ivs |- _] => apply eq_sym in H
  | [H: nil = idsOf ?ivs |- _] => apply eq_sym in H
  | [H: nil = nil |- _] => clear H
  end.

Ltac disc_rule_conds_unit :=
  try disc_rule_conds_unit_rule_preds;
  try disc_rule_conds_unit_footprint;
  try disc_rule_conds_unit_simpl.

Ltac disc_rule_conds :=
  repeat
    (repeat disc_rule_conds_unit;
     try disc_rule_custom;
     simpl in *; subst; mred).

Ltac solve_rule_conds :=
  repeat red;
  repeat
    (repeat
       match goal with
       | [ |- exists _, _] => eexists
       | [ |- _ /\ _] => split
       end;
     try reflexivity; try eassumption).

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
    eapply RqRsDownMatch_rs_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    pose proof (rqrsDTree_rqUp_rsUp_not_eq _ _ H H2).
    elim H3; reflexivity.
  Qed.

  Lemma rqrsDTree_rsUp_ups_not_in:
    forall oidx rsUp1 downs2 ups2 P,
      rsEdgeUpFrom dtr oidx = Some rsUp1 ->
      RqRsDownMatch dtr oidx downs2 ups2 P ->
      ~ In rsUp1 ups2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rs_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    destruct Hsd.
    apply parentIdxOf_not_eq in H1; [|assumption].
    pose proof (rqrsDTree_rsUp_rsUp_not_eq H1 H2 H).
    elim H5; reflexivity.
  Qed.

  Lemma rqrsDTree_rsUp_ups_not_in_parent:
    forall oidx1 oidx2 rsUp1 downs2 ups2 P,
      rsEdgeUpFrom dtr oidx1 = Some rsUp1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      ~ In rsUp1 ups2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rs_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    destruct Hsd.
    destruct (eq_nat_dec oidx1 cidx); subst.
    - rewrite H2 in H1; elim H1; reflexivity.
    - pose proof (rqrsDTree_rsUp_rsUp_not_eq n H H3).
      elim H6; reflexivity.
  Qed.

  Lemma rqrsDTree_down_ups_not_in:
    forall oidx1 oidx2 down1 downs2 ups2 P,
      edgeDownTo dtr oidx1 = Some down1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      ~ In down1 ups2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rs_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    pose proof (rqrsDTree_rsUp_down_not_eq _ _ H2 H).
    elim H3; reflexivity.
  Qed.
  
  Lemma rqrsDTree_rqUp_downs_not_in:
    forall oidx1 oidx2 rqUp1 downs2 ups2 P,
      rqEdgeUpFrom dtr oidx1 = Some rqUp1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      ~ In rqUp1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    pose proof (rqrsDTree_rqUp_down_not_eq _ _ H H2).
    elim H3; reflexivity.
  Qed.

  Lemma rqrsDTree_rsUp_downs_not_in:
    forall oidx1 oidx2 rsUp1 downs2 ups2 P,
      rsEdgeUpFrom dtr oidx1 = Some rsUp1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      ~ In rsUp1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    pose proof (rqrsDTree_rsUp_down_not_eq _ _ H H2).
    elim H3; reflexivity.
  Qed.

  Lemma rqrsDTree_down_downs_not_in:
    forall oidx down1 downs2 ups2 P,
      edgeDownTo dtr oidx = Some down1 ->
      RqRsDownMatch dtr oidx downs2 ups2 P ->
      ~ In down1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    destruct Hsd.
    apply parentIdxOf_not_eq in H1; [|eassumption].
    pose proof (rqrsDTree_down_down_not_eq H1 H2 H).
    elim H5; reflexivity.
  Qed.

  Lemma rqrsDTree_down_downs_not_in_parent:
    forall oidx1 oidx2 down1 downs2 ups2 P,
      edgeDownTo dtr oidx1 = Some down1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 P ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      ~ In down1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    destruct Hsd.
    destruct (eq_nat_dec oidx1 cidx); subst.
    - rewrite H2 in H1; elim H1; reflexivity.
    - pose proof (rqrsDTree_down_down_not_eq n H H3).
      elim H6; reflexivity.
  Qed.

  Lemma rqrsDTree_down_downs_not_in_child:
    forall oidx1 oidx2 down1 downs2 ups2,
      edgeDownTo dtr oidx1 = Some down1 ->
      RqRsDownMatch dtr oidx2 downs2 ups2 (fun cidx => cidx <> oidx1) ->
      ~ In down1 downs2.
  Proof.
    intros; intro Hx.
    eapply RqRsDownMatch_rq_In in H0; [|eassumption].
    destruct H0 as [cidx ?]; dest.
    pose proof (rqrsDTree_down_down_not_eq H0 H2 H).
    elim H3; reflexivity.
  Qed.

End RqRsDTree.

Definition rqsQ (msgs: MessagePool Msg) (midx: IdxT) :=
  filter (fun msg => msg.(msg_type) ==n MRq) (findQ midx msgs).

Definition rssQ (msgs: MessagePool Msg) (midx: IdxT) :=
  filter (fun msg => msg.(msg_type) ==n MRs) (findQ midx msgs).

Lemma findQ_length_one:
  forall (msgs: MessagePool Msg) midx msg,
    length (findQ midx msgs) <= 1 ->
    FirstMPI msgs (midx, msg) ->
    length (findQ midx msgs) = 1.
Proof.
  unfold FirstMPI, FirstMP, firstMP; simpl; intros.
  destruct (findQ midx msgs); [discriminate|].
  inv H0; simpl in *.
  omega.
Qed.

Lemma rqsQ_length_one:
  forall msgs midx msg,
    length (rqsQ msgs midx) <= 1 ->
    msg_type msg = MRq ->
    FirstMPI msgs (midx, msg) ->
    length (rqsQ msgs midx) = 1.
Proof.
  unfold rqsQ; intros.
  unfold FirstMPI, FirstMP, firstMP in H1.
  simpl in H1.
  destruct (findQ midx msgs); [discriminate|].
  inv H1.
  simpl in *; rewrite H0 in *; simpl in *.
  omega.
Qed.

Lemma rssQ_length_one:
  forall msgs midx msg,
    length (rssQ msgs midx) <= 1 ->
    msg_type msg = MRs ->
    FirstMPI msgs (midx, msg) ->
    length (rssQ msgs midx) = 1.
Proof.
  unfold rssQ; intros.
  unfold FirstMPI, FirstMP, firstMP in H1.
  simpl in H1.
  destruct (findQ midx msgs); [discriminate|].
  inv H1.
  simpl in *; rewrite H0 in *; simpl in *.
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
     Hdowns2: RqRsDownMatch _ ?idx2 ?downs2 _ (fun _ => _ <> ?idx1) |- _] =>
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





