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
      pose proof (rules_same_id_in_object_same _ _ _ H0 H1 H2);
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
    red in H;
    destruct H as [rqFrom [rqTos ?]]; dest
  | [H: RqUpUp _ _ _ _ ?rule \/
        RqUpDown _ _ _ _ ?rule \/
        RqDownDown _ _ _ _ ?rule |- _] =>
    destruct H as [|[|]]
  | [H: RqUpUp _ _ _ _ _ |- _] => red in H; dest
  | [H: RqUpDown _ _ _ _ _ |- _] => red in H; dest
  | [H: RqDownDown _ _ _ _ _ |- _] => red in H; dest
  | [H: RsBackRule _ |- _] =>
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rssFrom [rsbTo ?]]; dest
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
  | [H: FootprintUpToDown _ _ _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rsbTo := fresh "rsbTo" in
    let nrssFrom := fresh "nrssFrom" in
    destruct H as [rqFrom [rsbTo [nrssFrom ?]]]; dest
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
     simpl in *; subst).

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
  
End RqRsDTree.

Ltac solve_midx_neq_unit :=
  match goal with
  | [Hw: WfDTree ?dtr, H: parentIdxOf ?dtr ?cidx = Some ?pidx |- _] =>
    isNew (cidx <> pidx); pose proof (parentIdxOf_not_eq Hw H)
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
  end.

Ltac solve_midx_neq :=
  repeat solve_midx_neq_unit; fail.

Section FootprintInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition FootprintUpOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqFrom rqTo rsFrom rsbTo,
      rqi.(rqi_minds_rss) = [rsFrom] /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      FootprintUpOk dtr oidx rqFrom rqTo rsFrom rsbTo.

  Definition FootprintDownOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqTos rssFrom rsbTo,
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      ((exists rqFrom,
           FootprintUpDownOk dtr oidx rqFrom rqTos rssFrom rsbTo) \/
       FootprintDownDownOk dtr oidx rqTos rssFrom).

  Definition FootprintsOkORqs (orqs: ORqs Msg) :=
    forall oidx,
      orqs@[oidx] >>=[True]
          (fun orq =>
             (orq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu)) /\
             (orq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx oidx rqid))).

  Lemma footprints_ok_orqs_add:
    forall orqs,
      FootprintsOkORqs orqs ->
      forall oidx norq,
        norq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu) ->
        norq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx oidx rqid) ->
        FootprintsOkORqs (orqs +[oidx <- norq]).
  Proof.
    unfold FootprintsOkORqs; intros.
    mred; simpl; intros; auto.
  Qed.
  
  Definition FootprintsOk (st: MState oifc) :=
    FootprintsOkORqs st.(bst_orqs).

  Ltac disc_rule_custom ::=
    repeat
      match goal with
      | [H1: FootprintsOkORqs ?orqs, H2: ?orqs @[?oidx] = _ |- _] =>
        let Hf := fresh "H" in
        pose proof (H1 oidx) as Hf;
        rewrite H2 in Hf; simpl in Hf; dest;
        clear H2
      end.

  Lemma footprints_ok_init:
    InvInit sys FootprintsOk.
  Proof.
    intros; do 3 red.
    intros; simpl; auto.
  Qed.
  
  Lemma footprints_ok_step:
    InvStep sys step_m FootprintsOk.
  Proof.
    red; intros.
    red in H0; red.
    inv H1; try assumption.

    simpl in *.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      mred.
      apply footprints_ok_orqs_add; auto; try (mred; fail).
    - disc_rule_conds.
      mred.
      apply footprints_ok_orqs_add; auto; try (mred; fail).
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        * do 4 eexists; repeat split; eassumption.
        * rewrite <-H20; assumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        * rewrite <-H19; assumption.
        * do 3 eexists; repeat split.
          left; eexists; eassumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        * rewrite <-H21; assumption.
        * do 3 eexists; repeat split.
          right; eassumption.
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        rewrite <-H15; assumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        rewrite <-H15; assumption.
    - disc_rule_conds.
      apply footprints_ok_orqs_add; disc_rule_conds; auto.
      do 3 eexists; repeat split.
      left; eexists; eassumption.
  Qed.

  Lemma footprints_ok:
    InvReachable sys step_m FootprintsOk.
  Proof.
    eapply inv_reachable.
    - apply footprints_ok_init.
    - apply footprints_ok_step.
  Qed.
  
End FootprintInv.

Ltac good_footprint_get oidx :=
  match goal with
  | [Hfpok: FootprintsOk _ _, Ho: _@[oidx] = Some _ |- _] =>
    let H := fresh "H" in
    pose proof Hfpok as H;
    specialize (H oidx); simpl in H
  end.

Ltac disc_footprints_ok :=
  repeat
    match goal with
    | [H: FootprintsOk _ _ |- _] => red in H
    | [H1: FootprintsOkORqs _ ?orqs, H2: ?orqs @[?oidx] = _ |- _] =>
      let Hf := fresh "H" in
      pose proof (H1 oidx) as Hf;
      rewrite H2 in Hf; simpl in Hf; dest;
      clear H2
    | [H: FootprintUpOkEx _ _ _ |- _] =>
      let rqFrom := fresh "rqFrom" in
      let rqTo := fresh "rqTo" in
      let rsFrom := fresh "rsFrom" in
      let rsbTo := fresh "rsbTo" in
      destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest
    | [H: FootprintDownOkEx _ _ _ |- _] =>
      let rqTos := fresh "rqTos" in
      let rssFrom := fresh "rssFrom" in
      let rsbTo := fresh "rsbTo" in
      destruct H as [rqTos [rssFrom [rsbTo ?]]]; dest
                                                   
    | [H: FootprintUpOk _ _ _ _ _ _ |- _] =>
      let cidx := fresh "cidx" in
      destruct H as [cidx ?]; dest
    | [H: (exists _, FootprintUpDownOk _ _ _ _ _ _) \/
          FootprintDownDownOk _ _ _ _ |- _] => destruct H
    | [H: exists _, FootprintUpDownOk _ _ _ _ _ _ |- _] =>
      let rsFrom := fresh "rqFrom" in
      destruct H as [rqFrom ?]; dest
    | [H: FootprintUpDownOk _ _ _ _ _ _ |- _] =>
      let upCIdx := fresh "upCIdx" in
      destruct H as [upCIdx ?]; dest
    | [H: FootprintDownDownOk _ _ _ _ |- _] => red in H; dest
    end.

Section MessageInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition RqUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists cidx rqUp,
      msgs = [rqUp] /\
      msg_type (valOf rqUp) = MRq /\
      parentIdxOf dtr cidx = Some oidx /\
      rqEdgeUpFrom dtr cidx = Some (idOf rqUp).

  Definition RqDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rqDown, msgs = [rqDown] /\
                   msg_type (valOf rqDown) = MRq /\
                   edgeDownTo dtr oidx = Some (idOf rqDown).

  Definition RsUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    Forall (fun msg => msg_type (valOf msg) = MRs) msgs /\
    Forall (fun rs => exists cidx, rsEdgeUpFrom dtr cidx = Some rs)
           (idsOf msgs).

  Definition RsDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rsDown, msgs = [rsDown] /\
                   msg_type (valOf rsDown) = MRs /\
                   edgeDownTo dtr oidx = Some (idOf rsDown).
  
  Ltac disc_rule_custom ::=
    disc_footprints_ok.
  
  Lemma messages_in_cases:
    forall st1 oidx ridx rins routs st2,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      RqUpMsgs oidx rins \/
      RqDownMsgs oidx rins \/
      RsUpMsgs oidx rins \/
      RsDownMsgs oidx rins.
  Proof.
    intros.

    (* Register some necessary invariants to prove this invariant. *)
    pose proof (footprints_ok Hitr H).

    inv H0.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - left.
      disc_rule_conds.
      solve_rule_conds.

    - right; left.
      disc_rule_conds.
      solve_rule_conds.

    - disc_rule_conds.
      + left; solve_rule_conds.
      + left; solve_rule_conds.
      + right; left; solve_rule_conds.

    - disc_rule_conds.
      + right; right; right.
        rewrite H4 in H2.
        disc_rule_conds.
        solve_rule_conds.
      + right; right; left.
        rewrite H2 in H23.
        split; auto.
        clear -H23; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_In in H23; [|eassumption].
        dest; eauto.
      + right; right; left.
        rewrite H2 in H19.
        split; auto.
        clear -H19; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_In in H19; [|eassumption].
        dest; eauto.

    - right; right; right.
      disc_rule_conds.
      solve_rule_conds.
  Qed.
    
End MessageInv.

(** NOTE: With [LockInv] below we may need some invariants 
 * for [Atomic] histories, such as: if [Atomic hst] and [st1 -(hst)-> st2]
 * then [hst.eouts ⊆ st2.msgs].
 *)

(* Want: between two continuous histories H1 and H2, after H1, related locks are
 * never released until H2; it can be proven by [LockInv] below and
 * [atomic_messages_spec_in] in SerialFacts.v.
 *)
Section LockInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hrr: GoodRqRsSys dtr sys)
             (Hsd: RqRsDTree dtr sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition OUpLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               orq@[upRq] = Some rqi /\
               rqi.(rqi_midx_rsb) = rsbTo).

    Definition ODownLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               orq@[downRq] = Some rqi /\
               rqi.(rqi_midx_rsb) = rsbTo).
    
    Definition OUpLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => UpLockFreeORq orq).

    Definition ONoUpLockTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[True]
          (fun orq =>
             match orq@[upRq] with
             | Some rqi => rqi.(rqi_midx_rsb) <> rsbTo
             | None => True
             end).

    Definition ODownLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => DownLockFreeORq orq).

    Definition rqsQ (midx: IdxT) :=
      filter (fun msg => msg.(msg_type) ==n MRq) (findQ midx msgs).

    Definition rssQ (midx: IdxT) :=
      filter (fun msg => msg.(msg_type) ==n MRs) (findQ midx msgs).

    Lemma rqsQ_length_one:
      forall midx msg,
        length (rqsQ midx) <= 1 ->
        msg_type msg = MRq ->
        FirstMPI msgs (midx, msg) ->
        length (rqsQ midx) = 1.
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
      forall midx msg,
        length (rssQ midx) <= 1 ->
        msg_type msg = MRs ->
        FirstMPI msgs (midx, msg) ->
        length (rssQ midx) = 1.
    Proof.
      unfold rssQ; intros.
      unfold FirstMPI, FirstMP, firstMP in H1.
      simpl in H1.
      destruct (findQ midx msgs); [discriminate|].
      inv H1.
      simpl in *; rewrite H0 in *; simpl in *.
      omega.
    Qed.
    
    Definition UpLockFreeInv (oidx: IdxT) :=
      parentIdxOf dtr oidx = None \/
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx /\
        findQ rqUp msgs = nil /\
        rssQ down = nil /\
        ONoUpLockTo pidx down.
    
    Definition UpLockedInv (oidx: IdxT) :=
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx /\
        length (findQ rqUp msgs) <= 1 /\
        length (rssQ down) <= 1 /\
        xor3 (length (findQ rqUp msgs) = 1)
             (length (rssQ down) = 1)
             (OUpLockedTo pidx down).

    Definition DownLockFreeInv (oidx: IdxT) :=
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        ((edgeDownTo dtr cidx) >>=[True] (fun down => rqsQ down = nil) /\
         (rsEdgeUpFrom dtr cidx) >>=[True] (fun rsUp => findQ rsUp msgs = nil)).
    
    Definition DownLockedInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      Forall (fun rsUp =>
                exists down cidx,
                  edgeDownTo dtr cidx = Some down /\
                  rsEdgeUpFrom dtr cidx = Some rsUp /\
                  parentIdxOf dtr cidx = Some oidx /\
                  length (rqsQ down) <= 1 /\
                  length (findQ rsUp msgs) <= 1 /\
                  xor3 (length (rqsQ down) = 1)
                       (length (findQ rsUp msgs) = 1)
                       (ODownLockedTo cidx rsUp))
             rqi.(rqi_minds_rss).

    Definition UpLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[upRq] with
      | Some _ => UpLockedInv oidx
      | None => UpLockFreeInv oidx
      end.

    Definition DownLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[downRq] with
      | Some downRqi => DownLockedInv oidx downRqi
      | None => DownLockFreeInv oidx
      end.

    Definition LockInvMO :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        let orq := orqs@[oidx] >>=[[]] (fun orq => orq) in
        UpLockInvORq oidx orq /\ DownLockInvORq oidx orq.

  End OnMState.
  
  Definition LockInv (st: MState oifc) :=
    LockInvMO st.(bst_orqs) st.(bst_msgs).

  Lemma lockInv_init:
    InvInit sys LockInv.
  Proof.
    intros; do 3 red; cbn.
    intros; cbn.
    split.
    - red.
      remember (parentIdxOf dtr oidx) as opidx.
      destruct opidx as [pidx|]; [right|left; reflexivity].
      pose proof (eq_sym Heqopidx).
      eapply parentIdxOf_Some in H0; [|eassumption].
      destruct H0 as [rqUp [rsUp [down ?]]]; dest.
      do 3 eexists; repeat split; try eassumption.
    - red; intros; split.
      + destruct (edgeDownTo dtr cidx); simpl; auto.
      + destruct (rsEdgeUpFrom dtr cidx); simpl; auto.
  Qed.

  Lemma ONoUpLockTo_not_OUpLockedTo:
    forall orqs oidx rsbTo,
      ONoUpLockTo orqs oidx rsbTo -> ~ OUpLockedTo orqs oidx rsbTo.
  Proof.
    unfold ONoUpLockTo, OUpLockedTo; intros.
    intro Hx.
    destruct (orqs@[oidx]); simpl in *; auto.
    destruct Hx as [rqi ?]; dest.
    rewrite H0 in H; elim H; assumption.
  Qed.

  Lemma not_ONoUpLockTo_OUpLockedTo:
    forall orqs oidx rsbTo,
      ~ OUpLockedTo orqs oidx rsbTo -> ONoUpLockTo orqs oidx rsbTo.
  Proof.
    unfold ONoUpLockTo, OUpLockedTo; intros.
    destruct (orqs@[oidx]); simpl in *; auto.
    destruct (o@[upRq]); auto.
    intro Hx; elim H.
    eexists; split; eauto.
  Qed.

  Lemma OUpLockedTo_orqs_preserved:
    forall orqs1 orqs2 oidx rsbTo,
      OUpLockedTo orqs1 oidx rsbTo ->
      orqs1@[oidx] = orqs2@[oidx] ->
      OUpLockedTo orqs2 oidx rsbTo.
  Proof.
    unfold OUpLockedTo; intros.
    rewrite <-H0; assumption.
  Qed.

  Lemma upLockedInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      UpLockedInv orqs msgs1 oidx ->
      (match rqEdgeUpFrom dtr oidx with
       | Some rqUp => findQ rqUp msgs1 = findQ rqUp msgs2
       | None => False
       end) ->
      (match edgeDownTo dtr oidx with
       | Some down => rssQ msgs1 down = rssQ msgs2 down
       | None => False
       end) ->
      UpLockedInv orqs msgs2 oidx.
  Proof.
    unfold UpLockedInv; simpl; intros.
    destruct H as [rqUp [down [pidx ?]]]; dest.
    rewrite H in H0.
    rewrite H2 in H1.
    exists rqUp, down, pidx.
    rewrite <-H0, <-H1.
    repeat split; try assumption.
  Qed.
  
  Corollary upLockedInv_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      UpLockedInv orqs msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      UpLockedInv orqs (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply upLockedInv_msgs_preserved; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Corollary upLockedInv_deqMsgs_preserved:
    forall orqs msgs eminds oidx,
      UpLockedInv orqs msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      UpLockedInv orqs (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply upLockedInv_msgs_preserved; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Lemma upLockFreeInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      UpLockFreeInv orqs msgs1 oidx ->
      (match rqEdgeUpFrom dtr oidx with
       | Some rqUp => findQ rqUp msgs1 = findQ rqUp msgs2
       | None => True
       end) ->
      (match edgeDownTo dtr oidx with
       | Some down => rssQ msgs1 down = rssQ msgs2 down
       | None => True
       end) ->
      UpLockFreeInv orqs msgs2 oidx.
  Proof.
    unfold UpLockFreeInv; simpl; intros.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx ?]]]; dest.
    rewrite H in H0.
    rewrite H2 in H1.
    exists rqUp, down, pidx; repeat split;
      try assumption; try congruence.
  Qed.
  
  Corollary upLockFreeInv_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      UpLockFreeInv orqs msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      UpLockFreeInv orqs (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply upLockFreeInv_msgs_preserved; eauto.
    - red in H; dest.
      remember (rqEdgeUpFrom dtr oidx) as rqUp.
      destruct rqUp as [rqUp|]; simpl in *; dest; auto.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Corollary upLockFreeInv_deqMsgs_preserved:
    forall orqs msgs eminds oidx,
      UpLockFreeInv orqs msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      UpLockFreeInv orqs (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply upLockFreeInv_msgs_preserved; eauto.
    - red in H; dest.
      remember (rqEdgeUpFrom dtr oidx) as rqUp.
      destruct rqUp as [rqUp|]; simpl in *; dest; auto.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Lemma downLockedInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx rqi,
      DownLockedInv orqs msgs1 oidx rqi ->
      (forall rsUp down cidx,
          In rsUp (rqi_minds_rss rqi) ->
          edgeDownTo dtr cidx = Some down ->
          rsEdgeUpFrom dtr cidx = Some rsUp ->
          parentIdxOf dtr cidx = Some oidx ->
          rqsQ msgs1 down = rqsQ msgs2 down /\
          findQ rsUp msgs1 = findQ rsUp msgs2) ->
      DownLockedInv orqs msgs2 oidx rqi.
  Proof.
    unfold DownLockedInv; simpl; intros.
    rewrite Forall_forall in H.
    apply Forall_forall; intros rsUp ?.
    specialize (H _ H1).
    destruct H as [down [cidx ?]]; dest.
    specialize (H0 _ _ _ H1 H H2 H3); dest.
    exists down, cidx.
    rewrite <-H0, <-H7.
    repeat split; try assumption.
  Qed.
  
  Corollary downLockedInv_enqMsgs_preserved:
    forall orqs msgs emsgs oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      DownLockedInv orqs (enqMsgs emsgs msgs) oidx rqi.
  Proof.
    intros.
    eapply downLockedInv_msgs_preserved; eauto.
    intros; split.
    - unfold rqsQ.
      rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Corollary downLockedInv_deqMsgs_preserved:
    forall orqs msgs eminds oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      DisjList eminds (sys_minds sys) ->
      DownLockedInv orqs (deqMsgs eminds msgs) oidx rqi.
  Proof.
    intros.
    eapply downLockedInv_msgs_preserved; eauto.
    intros; split.
    - unfold rqsQ.
      rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Lemma downLockFreeInv_msgs_preserved:
    forall msgs1 msgs2 oidx,
      DownLockFreeInv msgs1 oidx ->
      (forall cidx,
          parentIdxOf dtr cidx = Some oidx ->
          (forall down,
              edgeDownTo dtr cidx = Some down ->
              rqsQ msgs1 down = rqsQ msgs2 down) /\
          (forall rsUp,
              rsEdgeUpFrom dtr cidx = Some rsUp ->
              findQ rsUp msgs1 = findQ rsUp msgs2)) ->
      DownLockFreeInv msgs2 oidx.
  Proof.
    unfold DownLockFreeInv; simpl; intros.
    specialize (H _ H1); dest.
    specialize (H0 _ H1); dest.
    split.
    - remember (edgeDownTo dtr cidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      rewrite <-H0; auto.
    - remember (rsEdgeUpFrom dtr cidx) as rsUp.
      destruct rsUp as [rsUp|]; simpl in *; dest; auto.
      rewrite <-H3; auto.
  Qed.
  
  Corollary downLockFreeInv_enqMsgs_preserved:
    forall msgs emsgs oidx,
      DownLockFreeInv msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      DownLockFreeInv (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply downLockFreeInv_msgs_preserved; eauto.
    intros; split; intros.
    - unfold rqsQ.
      rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Lemma downLockFreeInv_deqMsgs_preserved:
    forall msgs eminds oidx,
      DownLockFreeInv msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      DownLockFreeInv (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply downLockFreeInv_msgs_preserved; eauto.
    intros; split; intros.
    - unfold rqsQ.
      rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Lemma upLockedInv_orqs_preserved:
    forall orqs1 orqs2 msgs oidx pidx,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] = orqs2@[pidx] ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H3 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.
    destruct H6.
    - xfst; try assumption.
      intro Hx; elim H7.
      red; rewrite H1; assumption.
    - xsnd; try assumption.
      intro Hx; elim H7.
      red; rewrite H1; assumption.
    - xthd; try assumption.
      red; rewrite <-H1; assumption.
  Qed.

  Corollary upLockedInv_orqs_preserved_add:
    forall orqs msgs oidx orq,
      UpLockedInv orqs msgs oidx ->
      UpLockedInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    intros.
    destruct Hsd.
    pose proof H.
    destruct H2 as [rqUp [down [pidx ?]]]; dest.
    eapply upLockedInv_orqs_preserved; eauto.
    apply parentIdxOf_not_eq in H4; [|assumption].
    mred.
  Qed.

  Lemma upLockFreeInv_orqs_preserved:
    forall orqs1 orqs2 msgs oidx pidx,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] = orqs2@[pidx] ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H3 in H0; inv H0.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red; rewrite <-H1; assumption.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_add:
    forall orqs msgs oidx orq,
      UpLockFreeInv orqs msgs oidx ->
      UpLockFreeInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx ?]]]; dest.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red in H4; red.
    apply parentIdxOf_not_eq in H1; [|destruct Hsd; assumption].
    mred.
  Qed.
  
  Lemma lockInv_step_ext_in:
    forall oss orqs msgs eins,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := enqMsgs eins msgs |}.
  Proof.
    unfold LockInv; simpl; intros.
    red; intros.
    specialize (H oidx H2).

    destruct H1.
    assert (DisjList (idsOf eins) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merqs_DisjList.
    }
    
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.

    - split.
      + clear H5; red in H; red.
        remember (orq@[upRq]) as orqi.
        destruct orqi as [rqi|].
        * apply upLockedInv_enqMsgs_preserved; assumption.
        * apply upLockFreeInv_enqMsgs_preserved; assumption.
      + clear H; red in H5; red.
        remember (orq@[downRq]) as orqi.
        destruct orqi as [rqi|].
        * apply downLockedInv_enqMsgs_preserved; assumption.
        * apply downLockFreeInv_enqMsgs_preserved; assumption.

    - red in H; simpl in H.
      red in H5; simpl in H5.
      split.
      + red; simpl.
        apply upLockFreeInv_enqMsgs_preserved; assumption.
      + red; simpl.
        apply downLockFreeInv_enqMsgs_preserved; assumption.
  Qed.

  Lemma lockInv_step_ext_out:
    forall oss orqs msgs eouts,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    unfold LockInv; simpl; intros.
    red; intros.
    specialize (H oidx H3).

    destruct H2.
    assert (DisjList (idsOf eouts) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merss_DisjList.
    }
    
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.

    - split.
      + clear H6; red in H; red.
        remember (orq@[upRq]) as orqi.
        destruct orqi as [rqi|].
        * apply upLockedInv_deqMsgs_preserved; assumption.
        * apply upLockFreeInv_deqMsgs_preserved; assumption.
      + clear H; red in H6; red.
        remember (orq@[downRq]) as orqi.
        destruct orqi as [rqi|].
        * apply downLockedInv_deqMsgs_preserved; assumption.
        * apply downLockFreeInv_deqMsgs_preserved; assumption.

    - red in H; simpl in H.
      red in H6; simpl in H6.
      split.
      + red; simpl.
        apply upLockFreeInv_deqMsgs_preserved; assumption.
      + red; simpl.
        apply downLockFreeInv_deqMsgs_preserved; assumption.
  Qed.

  Section InternalStep.
    Variables (oss: OStates oifc) (orqs: ORqs Msg) (msgs: MessagePool Msg)
              (obj: Object oifc) (rule: Rule oifc)
              (post: OState oifc) (porq: ORq Msg) (mins: list (Id Msg))
              (nost: OState oifc) (norq: ORq Msg) (mouts: list (Id Msg)).

    Hypotheses
      (Hfpok: FootprintsOk
                dtr {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |})
      (HobjIn: In obj (sys_objs sys))
      (HruleIn: In rule (obj_rules obj))
      (Hporq: orqs@[obj_idx obj] = Some porq)
      (Hpost: oss@[obj_idx obj] = Some post)
      (HminsF: Forall (FirstMPI msgs) mins)
      (HminsV: ValidMsgsIn sys mins)
      (Hprec: rule_precond rule post porq mins)
      (Htrs: rule_trs rule post porq mins = (nost, norq, mouts))
      (HmoutsV: ValidMsgsOut sys mouts)
      (Hmdisj: DisjList (idsOf mins) (idsOf mouts)).

    Lemma deqMP_rq_filter_rs_eq:
      forall midx msg,
        msg_type msg = MRq ->
        FirstMPI msgs (midx, msg) ->
        filter (fun msg => msg_type msg ==n MRs)
               (findQ midx msgs) =
        filter (fun msg => msg_type msg ==n MRs)
               (findQ midx (deqMP midx msgs)).
    Proof.
      intros.
      unfold FirstMPI, FirstMP, firstMP in H0.
      unfold deqMP, idOf in *; simpl in *.
      destruct (findQ midx msgs); [discriminate|].
      simpl in H0; inv H0.
      unfold findQ; mred; simpl.
      rewrite H; simpl.
      reflexivity.
    Qed.

    Lemma deqMP_rs_filter_rq_eq:
      forall midx msg,
        msg_type msg = MRs ->
        FirstMPI msgs (midx, msg) ->
        filter (fun msg => msg_type msg ==n MRq)
               (findQ midx msgs) =
        filter (fun msg => msg_type msg ==n MRq)
               (findQ midx (deqMP midx msgs)).
    Proof.
      intros.
      unfold FirstMPI, FirstMP, firstMP in H0.
      unfold deqMP, idOf in *; simpl in *.
      destruct (findQ midx msgs); [discriminate|].
      simpl in H0; inv H0.
      unfold findQ; mred; simpl.
      rewrite H; simpl.
      reflexivity.
    Qed.

    Ltac disc_rule_custom ::=
      match goal with
      | [H: FootprintUpOkEx _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        let rqTo := fresh "rqTo" in
        let rsFrom := fresh "rsFrom" in
        let rsbTo := fresh "rsbTo" in
        destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest
      | [H: FootprintUpOk _ _ _ _ _ _ |- _] =>
        let cidx := fresh "cidx" in
        destruct H as [cidx ?]; dest
      end.

    Lemma upLockInvORq_step_int_me:
      UpLockInvORq orqs msgs (obj_idx obj) porq ->
      In (obj_idx obj) (map (@obj_idx _) (sys_objs sys)) ->
      GoodRqRsRule dtr (obj_idx obj) rule ->
      UpLockInvORq (orqs+[obj_idx obj <- norq])
                   (enqMsgs mouts (deqMsgs (idsOf mins) msgs))
                   (obj_idx obj) norq.
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        replace (orqs +[obj_idx obj <- porq]) with orqs by meq.
        destruct i as [rsMIdx rsd]; simpl in *.
        eapply upLockFreeInv_msgs_preserved; eauto.
        + remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
          destruct orqUp as [rqUp|]; auto.
          rewrite findQ_not_In_enqMP; [|solve_midx_neq].
          rewrite findQ_not_In_deqMP; [|solve_midx_neq].
          reflexivity.
        + remember (edgeDownTo dtr (obj_idx obj)) as odown.
          destruct odown as [down|]; auto.
          unfold rssQ.
          rewrite findQ_not_In_enqMP; [|solve_midx_neq].
          rewrite findQ_not_In_deqMP; [|solve_midx_neq].
          reflexivity.

      - (** case [ImmUpRule] *)
        disc_rule_conds.
        replace (orqs +[obj_idx obj <- porq]) with orqs by meq.
        destruct i as [rsMIdx rsd]; simpl in *.
        destruct (porq@[upRq]).
        + eapply upLockedInv_msgs_preserved; eauto.
          * red in H.
            destruct H as [rqUp [down [pidx ?]]]; dest.
            rewrite H.
            rewrite findQ_not_In_enqMP; [|solve_midx_neq].
            rewrite findQ_not_In_deqMP; [|solve_midx_neq].
            reflexivity.
          * rewrite H1.
            unfold rssQ.
            rewrite findQ_not_In_enqMP; [|solve_midx_neq].
            destruct i0 as [down rqDown]; simpl in *.
            eapply deqMP_rq_filter_rs_eq; eauto.
        + eapply upLockFreeInv_msgs_preserved; eauto.
          * remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
            destruct orqUp as [rqUp|]; auto.
            rewrite findQ_not_In_enqMP; [|solve_midx_neq].
            rewrite findQ_not_In_deqMP; [|solve_midx_neq].
            reflexivity.
          * rewrite H1.
            unfold rssQ.
            rewrite findQ_not_In_enqMP; [|solve_midx_neq].
            eapply deqMP_rq_filter_rs_eq; eauto.

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + (** case [RqUpUp]; setting an uplock. *)
          red in H.
          pose proof (rqEdgeUpFrom_Some Hsd _ H6).
          destruct H14 as [rsUp [down [pidx ?]]]; dest.
          disc_rule_conds.
          destruct H; [discriminate|].
          destruct H as [rqUp [down' [pidx' ?]]]; dest.
          disc_rule_conds.
          destruct i0 as [rqUp rqm]; simpl in *.
          do 3 eexists; repeat split; try eassumption.
          * rewrite findQ_In_enqMP.
            rewrite findQ_not_In_deqMP; [|solve_midx_neq].
            rewrite H19; simpl; omega.
          * unfold rssQ.
            rewrite findQ_not_In_enqMP; [|solve_midx_neq].
            rewrite findQ_not_In_deqMP; [|solve_midx_neq].
            unfold rssQ in H20; rewrite H20.
            simpl; omega.
          * xfst.
            { rewrite findQ_In_enqMP.
              rewrite findQ_not_In_deqMP; [|solve_midx_neq].
              rewrite H19; reflexivity.
            }
            { unfold rssQ.
              rewrite findQ_not_In_enqMP; [|solve_midx_neq].
              rewrite findQ_not_In_deqMP; [|solve_midx_neq].
              unfold rssQ in H20; rewrite H20; auto.
            }
            { apply ONoUpLockTo_not_OUpLockedTo.
              red; pose proof (parentIdxOf_not_eq H2 H16); mred.
            }

        + (** case [RqUpDown]; setting a downlock. *)
          rewrite <-H11.
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_msgs_preserved with (msgs1:= msgs).
            { apply upLockedInv_orqs_preserved_add; auto. }
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              rewrite H.
              red in H9; destruct H9 as [upCIdx ?]; dest.
              rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
              rewrite findQ_not_In_deqMP; [|solve_midx_neq].
              reflexivity.
            }
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              rewrite H4.
              red in H9; destruct H9 as [upCIdx ?]; dest.
              unfold rssQ.
              rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
              rewrite findQ_not_In_deqMP; [|solve_midx_neq].
              reflexivity.
            }

          * apply upLockFreeInv_msgs_preserved with (msgs1:= msgs).
            { apply upLockFreeInv_orqs_preserved_add; auto. }
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                rewrite H.
                red in H9; destruct H9 as [upCIdx ?]; dest.
                rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
                rewrite findQ_not_In_deqMP; [|solve_midx_neq].
                reflexivity.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                rewrite H4.
                red in H9; destruct H9 as [upCIdx ?]; dest.
                unfold rssQ.
                rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
                rewrite findQ_not_In_deqMP; [|solve_midx_neq].
                reflexivity.
              }
            }

        + (** case [RqDownDown]; setting a downlock *)
          rewrite <-H13.
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_msgs_preserved with (msgs1:= msgs).
            { apply upLockedInv_orqs_preserved_add; auto. }
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              rewrite H.
              red in H11.
              rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
              rewrite findQ_not_In_deqMP; [|solve_midx_neq].
              reflexivity.
            }
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              rewrite H4; red in H11.
              unfold rssQ.
              rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
              destruct i as [rqDown rqm]; simpl in *.
              disc_rule_conds.
              eapply deqMP_rq_filter_rs_eq; eauto.
            }

          * apply upLockFreeInv_msgs_preserved with (msgs1:= msgs).
            { apply upLockFreeInv_orqs_preserved_add; auto. }
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                rewrite H.
                red in H11.
                rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
                rewrite findQ_not_In_deqMP; [|solve_midx_neq].
                reflexivity.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                rewrite H4; red in H11.
                unfold rssQ.
                rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
                destruct i as [rqDown rqm]; simpl in *.
                disc_rule_conds.
                eapply deqMP_rq_filter_rs_eq; eauto.
              }
            }

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + (** case [FootprintReleasingUp]; releasing the uplock. *)
          destruct H as [rqUp [down [pidx ?]]]; dest.
          destruct i as [rsDown rsbm]; simpl in *.
          rewrite H4 in H6.
          disc_rule_conds.
          eapply xor3_inv_2 with (B:= length (rssQ msgs (fst i)) = 1) in H21;
            [dest|eapply rssQ_length_one; eauto].
          remember (rqi_midx_rsb rqi) as rsbTo; clear HeqrsbTo.
          destruct i as [rsFrom rsm]; simpl in *.
          right.
          exists rqTo, rsFrom, pidx.
          repeat split; try assumption.
          * rewrite findQ_not_In_enqMP; [|solve_midx_neq].
            rewrite findQ_not_In_deqMP; [|solve_midx_neq].
            apply length_zero_iff_nil; omega.
          * unfold rssQ.
            rewrite findQ_not_In_enqMP; [|solve_midx_neq].
            apply findQ_In_deqMP_FirstMP in H11; simpl in H11.
            unfold rssQ in H20; rewrite <-H11 in H20.
            simpl in H20; rewrite H13 in H20; simpl in H20.
            apply length_zero_iff_nil; omega.
          * apply not_ONoUpLockTo_OUpLockedTo; auto.
            intro Hx; elim H10.
            apply parentIdxOf_not_eq in H18; [|assumption].
            eapply OUpLockedTo_orqs_preserved; [eassumption|].
            mred.
          
        + (** case [FootprintReleasingDown]; releasing the downlock *)
          admit.

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        apply upLockFreeInv_orqs_preserved_add.
        red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
        destruct i as [rsDown rsm]; simpl in *.
        disc_rule_conds.
        eapply xor3_inv_2 with (B:= length (rssQ msgs rsDown) = 1) in H18;
          [dest|eapply rssQ_length_one; eauto].
        red in H9; destruct H9 as [upCIdx ?]; dest.
        red; right.
        exists rqUp, rsDown, pidx; repeat split; try assumption.
        + rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
          rewrite findQ_not_In_deqMP; [|solve_midx_neq].
          apply length_zero_iff_nil; omega.
        + unfold rssQ.
          rewrite findQ_not_In_enqMsgs; [|solve_midx_neq].
          apply findQ_In_deqMP_FirstMP in H14; simpl in H14.
          unfold rssQ in H17; rewrite <-H14 in H17.
          simpl in H17; rewrite H15 in H17; simpl in H17.
          apply length_zero_iff_nil; omega.
        + apply not_ONoUpLockTo_OUpLockedTo; auto.
    Admitted.

    Lemma upLockInvORq_step_int_other:
      forall oidx,
        UpLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr (obj_idx obj) rule ->
        obj_idx obj <> oidx ->
        UpLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
      (* The only nontrivial case will be when [oidx = parentIdxOf dtr (obj_idx obj)].
       * Otherwise state transitions are orthogonal.
       *)
    Admitted.

    Lemma downLockInvORq_step_int_me:
      DownLockInvORq orqs msgs (obj_idx obj) porq ->
      In (obj_idx obj) (map (@obj_idx _) (sys_objs sys)) ->
      GoodRqRsRule dtr (obj_idx obj) rule ->
      DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs))
                     (obj_idx obj) norq.
    Proof.
    Admitted.

    Lemma downLockInvORq_step_int_other:
      forall oidx,
        DownLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr (obj_idx obj) rule ->
        obj_idx obj <> oidx ->
        DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
    Admitted.

    Lemma lockInv_step_int:
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      LockInv {| bst_oss := (oss) +[ obj_idx obj <- nost];
                 bst_orqs := (orqs) +[ obj_idx obj <- norq];
                 bst_msgs := enqMsgs mouts (deqMsgs (idsOf mins) msgs) |}.
    Proof.
      intros.
      do 2 red; simpl; intros.
      good_rqrs_rule_get rule.
      specialize (H _ H0); simpl in H; dest; split.

      - (** Proving invariants about uplocks *)
        M.cmp (obj_idx obj) oidx; mred; simpl in *.
        + (** case [oidx = obj_idx obj] *)
          apply upLockInvORq_step_int_me; assumption.
        + (** case [oidx <> obj_idx obj] *)
          apply upLockInvORq_step_int_other; assumption.

      - (** Proving invariants about downlocks *)
        M.cmp (obj_idx obj) oidx; mred; simpl in *.
        + (** case [oidx = obj_idx obj] *)
          apply downLockInvORq_step_int_me; assumption.
        + (** case [oidx <> obj_idx obj] *)
          apply downLockInvORq_step_int_other; assumption.
    Qed.

  End InternalStep.

  Lemma lockInv_step:
    InvStep sys step_m LockInv.
  Proof.
    red; intros.
    inv H1.
    - auto.
    - apply lockInv_step_ext_in; auto.
    - apply lockInv_step_ext_out; auto.
    - eapply lockInv_step_int; eauto.
      eapply footprints_ok; eassumption.
  Qed.

  Lemma lockInv_ok:
    InvReachable sys step_m LockInv.
  Proof.
    apply inv_reachable.
    - apply lockInv_init.
    - apply lockInv_step.
  Qed.
  
End LockInv.

Section RqUpInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: GoodRqRsSys dtr sys)
             (Hrud: RqUpRsUpOkSys dtr sys).
  
  (* Lemma rqUp_reducible: *)
  (*   forall oidx1 ridx1 rins1 routs1 rule1 obj1 *)
  (*          (Hobj1: In obj1 sys.(sys_objs)) (Hoidx1: obj1.(obj_idx) = oidx1) *)
  (*          (Hrule1: In rule1 obj1.(obj_rules)) *)
  (*          (Hridx1: rule1.(rule_idx) = ridx1) *)
  (*          oidx2 ridx2 rins2 routs2 rule2 obj2 *)
  (*          (Hobj2: In obj2 sys.(sys_objs)) (Hoidx2: obj2.(obj_idx) = oidx2) *)
  (*          (Hrule2: In rule2 obj2.(obj_rules)) *)
  (*          (Hridx2: rule2.(rule_idx) = ridx2), *)
  (*     RqToUpRule dtr oidx1 rule1 -> *)
  (*     DisjList routs1 rins2 -> *)
  (*     Reducible sys [RlblInt oidx2 ridx2 rins2 routs2; *)
  (*                      RlblInt oidx1 ridx1 rins1 routs1] *)
  (*               [RlblInt oidx1 ridx1 rins1 routs1; *)
  (*                  RlblInt oidx2 ridx2 rins2 routs2]. *)
  (* Proof. *)
  (* Admitted. *)

End RqUpInv.

Inductive TrsType := RqUp | RqDown | RsUp | RsDown.
(* Object index -> TrsTypes (ordered, head is the oldest one) *)
Definition TrsState := M.t (list TrsType).

Definition addTrsState (oidx: IdxT) (tr: TrsType) (ts: TrsState): TrsState :=
  match ts@[oidx] with
  | Some tts => ts +[oidx <- tr :: tts]
  | None => ts +[oidx <- [tr]]
  end.

Definition rssOfL (lbl: MLabel) :=
  match lbl with
  | RlblInt oidx _ _ mouts =>
    match mouts with
    | nil => Some oidx (* Requests are never ignored. *)
    | (midx, mout) :: _ =>
      if eq_nat_dec (msg_type mout) MRs
      then Some oidx else None
    end
  | _ => None
  end.

Fixpoint rssOf (hst: MHistory): list IdxT :=
  match hst with
  | nil => nil
  | lbl :: hst' => (rssOfL lbl) ::> (rssOf hst')
  end.

(* Definition rqsOfL (lbl: MLabel) := *)
(*   match lbl with *)
(*   | RlblInt oidx _ _ mouts => *)
(*     match mouts with *)
(*     | nil => None (* Requests are never ignored. *) *)
(*     | (midx, mout) :: _ => *)
(*       if eq_nat_dec (msg_type mout) MRq *)
(*       then Some oidx else None *)
(*     end *)
(*   | _ => None *)
(*   end. *)

Section AtomicInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition rsUpCover (idm: Id Msg): list IdxT :=
    nil. (** TODO: define it. *)

  Fixpoint rsUpCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rsUpCover idm ++ rsUpCovers eouts'
    end.

  Definition rsDownCover (idm: Id Msg): list IdxT :=
    nil. (** TODO: define it. *)

  Fixpoint rsDownCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rsDownCover idm ++ rsDownCovers eouts'
    end.

  Definition AtomicInv (inits eouts: list (Id Msg)) (hst: MHistory) :=
    NoDup (rssOf hst) /\
    SubList (rssOf hst) (rsUpCovers eouts) /\
    DisjList (rssOf hst) (rsDownCovers eouts).

  Lemma atomic_inv:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        steps step_m sys s1 hst s2 ->
        AtomicInv inits eouts hst.
  Proof.
  Admitted.
  
End AtomicInv.

Close Scope list.
Close Scope fmap.

