Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo.

Set Implicit Arguments.

Import MonadNotations.
Import CaseNotations.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Ltac disc_AtomicInv :=
  repeat
    match goal with
    | [H: AtomicInv _ _ _ _ _ _ |- _] => red in H; dest
    end.

Ltac atomic_cont_exfalso_bound msgOutPred :=
  exfalso;
  disc_rule_conds_ex;
  repeat 
    match goal with
    | [H1: AtomicMsgOutsInv _ ?eouts _, H2: In _ ?eouts |- _] =>
      red in H1; rewrite Forall_forall in H1;
      specialize (H1 _ H2); simpl in H1
    | [H: msgOutPred _ _ _ |- _] => red in H
    | [H1: caseDec _ ?sig _ _ |- _] =>
      match sig with
      | sigOf (?midx, ?msg) =>
        match goal with
        | [H2: msg_id ?msg = ?mid, H3: msg_type ?msg = ?mty |- _] =>
          progress replace sig with (midx, (mty, mid)) in H1
            by (unfold sigOf; simpl; rewrite H2, H3; reflexivity);
          simpl in H1
        end
      end
    end;
  assumption.

Ltac atomic_init_exfalso_rq :=
  exfalso;
  disc_rule_conds_ex;
  repeat
    match goal with
    | [H: _ = _ \/ _ |- _] =>
      destruct H; [subst; try discriminate|auto]
    end.

Ltac atomic_init_exfalso_rs_from_parent :=
  exfalso;
  repeat
    (repeat match goal with
            | [H: UpLockInvORq _ _ _ _ _ |- _] => red in H
            | [H1: ?orq@[0] = Some _, H2: context[?orq@[0]] |- _] =>
              rewrite H1 in H2; simpl in H2
            | [H: UpLockRsFromParent _ _ _ |- _] =>
              let rsFrom := fresh "rsFrom" in
              destruct H as [rsFrom [? ?]]
            end;
     disc_rule_conds_ex);
  repeat
    match goal with
    | [H1: _ = ?rsFrom \/ _, H2: edgeDownTo _ _ = Some ?rsFrom |- _] =>
      destruct H1; [subst; try discriminate|auto]
    end.

Ltac atomic_init_solve_AtomicMsgOutsInv :=
  simpl; repeat constructor.

(* Ltac atomic_init_solve_AtomicLocksInv := *)
(*   red; intros; dest_in; *)
(*   repeat (simpl; mred); *)
(*   unfold sigOf; simpl; *)
(*   repeat *)
(*     match goal with *)
(*     | [H: msg_id ?msg = _ |- context [msg_id ?msg] ] => rewrite H *)
(*     | [H1: msg_id ?msg = _, H2: context [msg_id ?msg] |- _] => *)
(*       rewrite H1 in H2 *)
(*     | [H: ?orq@[?i] = Some _ |- context [?orq@[?i]] ] => rewrite H *)
(*     | [H1: ?orq@[?i] = Some _, H2: context [?orq@[?i]] |- _] => *)
(*       rewrite H1 in H2 *)
(*     | [H: ?orq@[?i] = None |- context [?orq@[?i]] ] => rewrite H *)
(*     | [H1: ?orq@[?i] = None, H2: context [?orq@[?i]] |- _] => *)
(*       rewrite H1 in H2 *)
(*     end; *)
(*   repeat (red; simpl; mred; auto). *)

Ltac atomic_init_solve_AtomicInv :=
  atomic_init_solve_AtomicMsgOutsInv.

Ltac disc_sig_caseDec :=
  match goal with
  | [H1: caseDec _ ?sig _ _ |- _] =>
    match sig with
    | sigOf (?midx, ?msg) =>
      match goal with
      | [H2: msg_id ?msg = ?mid, H3: msg_type ?msg = ?mty |- _] =>
        progress replace sig with (midx, (mty, mid)) in H1
          by (unfold sigOf; simpl; rewrite H2, H3; reflexivity);
        simpl in H1
      end
    end
  end.

Ltac disc_msg_preds_with Hl Hin :=
  match type of Hl with
  | AtomicMsgOutsInv _ ?eouts _ =>
    red in Hl; rewrite Forall_forall in Hl;
    specialize (Hl _ Hin); simpl in Hl;
    red in Hl; disc_sig_caseDec
  end.

Ltac disc_msg_preds Hin :=
  match goal with
  | [H: AtomicMsgOutsInv _ _ _ |- _] =>
    let Hl := fresh "H" in
    pose proof H as Hl;
    disc_msg_preds_with Hl Hin
  end.

Section Inv.

  (** Basic predicates per an object *)
  
  Definition ImplOStateM (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiM /\ ost#[implValueIdx] = cv.

  Definition ImplOStateS (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiS /\ ost#[implValueIdx] = cv.

  Definition ImplOStateI (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI.

  Definition ImplOStateMSI (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] >= msiS -> ost#[implValueIdx] = cv.

  Definition ImplDirM (ost: OState ImplOStateIfc): Prop :=
    (ost#[implDirIdx].(fst) = msiM /\ ost#[implDirIdx].(snd) = msiI) \/
    (ost#[implDirIdx].(fst) = msiI /\ ost#[implDirIdx].(snd) = msiM).

  Definition ImplDirS (ost: OState ImplOStateIfc): Prop :=
    ost#[implDirIdx].(fst) <= msiS /\
    ost#[implDirIdx].(snd) <= msiS.

  Definition ImplDirI (ost: OState ImplOStateIfc): Prop :=
    ost#[implDirIdx].(fst) = msiI /\
    ost#[implDirIdx].(snd) = msiI.

  Section GInv.
    Variables (post cost1 cost2: OState ImplOStateIfc)
              (porq corq1 corq2: ORq Msg).

    (** The first invariant: the directory status is coherent to statuses of
     * children. Note that an object is *not* required to keep the coherency
     * when it is (properly) locked (the meaning of "properly" depends on the
     * protocol).
     *)
    Definition ImplDirCoh: Prop :=
      (!corq1@[upRq]; cost1#[implStatusIdx] <= post#[implDirIdx].(fst)) /\
      (!corq2@[upRq]; cost2#[implStatusIdx] <= post#[implDirIdx].(snd)).
    
    (** The second invariant is only for parent, saying that the parent status
     * and its directory status are coherent.
     *)
    Definition ImplParentCoh (cv: nat): Prop :=
      (ImplOStateM cv post /\ ImplDirI post) \/
      (ImplOStateS cv post /\ ImplDirS post) \/
      (ImplOStateI post /\ ImplDirM post).

    (** The last invariant is for children, in order for ensuring
     * the local coherency. 
     *)
    Definition ImplChildCoh1 (cv: nat): Prop :=
      !corq1@[upRq]; ImplOStateMSI cv cost1.
    Definition ImplChildCoh2 (cv: nat): Prop :=
      !corq2@[upRq]; ImplOStateMSI cv cost2.

    Definition ImplChildrenCoh: Prop :=
      !corq1@[upRq]; !corq2@[upRq];
        (cost1#[implStatusIdx] = msiM -> cost2#[implStatusIdx] = msiI) /\
        (cost2#[implStatusIdx] = msiM -> cost1#[implStatusIdx] = msiI).
  
    Definition ImplStateCoh (cv: nat): Prop :=
      ImplParentCoh cv /\ 
      ImplChildCoh1 cv /\ ImplChildCoh2 cv /\
      ImplChildrenCoh.

    Definition ImplParentLockInv: Prop :=
      rqid <+- porq@[downRq];
        ((rqid.(rqi_minds_rss) = [c2pRs] /\ rqid.(rqi_midx_rsb) = pc1) \/
         (rqid.(rqi_minds_rss) = [c1pRs] /\ rqid.(rqi_midx_rsb) = pc2)).
    
  End GInv.

  Definition ImplStateInv (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      (exists cv, ImplStateCoh post cost1 cost2 corq1 corq2 cv) /\
      ImplDirCoh post cost1 cost2 corq1 corq2.

  Definition ImplLockInv (st: MState ImplOStateIfc): Prop :=
    porq <-- (bst_orqs st)@[parentIdx];
      ImplParentLockInv porq.

  Definition ImplInv (st: MState ImplOStateIfc): Prop :=
    ImplStateInv st /\ ImplLockInv st.

  Hint Unfold ImplOStateM ImplOStateS ImplOStateI ImplOStateMSI
       ImplDirM ImplDirS ImplDirI
       ImplDirCoh ImplParentCoh ImplChildCoh1 ImplChildCoh2 ImplChildrenCoh
       ImplStateCoh: RuleConds.

  Ltac disc_msi :=
    try
      match goal with
      | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl)
      | [H: ?p -> _, Hp: ?p |- _] => specialize (H Hp)
      | [H: VNat ?v = VNat _ |- _] => is_var v; inv H
      | [H: VNat _ = VNat ?v |- _] => is_var v; inv H
      | [H: ?oss@[parentIdx] = Some ?ost |- _] =>
        match type of ost with
        | OState _ =>
          let val := fresh "val" in
          let stt := fresh "stt" in
          let dir := fresh "dir" in
          destruct ost as [val [stt [dir ?]]]
        end
      | [H: ?oss@[child1Idx] = Some ?ost |- _] =>
        match type of ost with
        | OState _ =>
          let val := fresh "val" in
          let stt := fresh "stt" in
          destruct ost as [val [stt ?]]
        end
      | [H: ?oss@[child2Idx] = Some ?ost |- _] =>
        match type of ost with
        | OState _ =>
          let val := fresh "val" in
          let stt := fresh "stt" in
          destruct ost as [val [stt ?]]
        end
      | [H: msiM = _ |- _] => apply eq_sym in H
      | [H: msiS = _ |- _] => apply eq_sym in H
      | [H: msiI = _ |- _] => apply eq_sym in H
      | [H1: ?t = msiM, H2: ?t = msiS |- _] => rewrite H1 in H2; discriminate
      | [H1: ?t = msiM, H2: ?t = msiI |- _] => rewrite H1 in H2; discriminate
      | [H1: ?t = msiS, H2: ?t = msiI |- _] => rewrite H1 in H2; discriminate
      | [H1: ?t = msiM, H2: ?t <= msiS |- _] =>
        rewrite H1 in H2; unfold msiM, msiS in H2; lia
      | [H1: ?t = msiI, H2: ?t >= msiS |- _] =>
        rewrite H1 in H2; unfold msiS, msiI in H2; lia
      end.

  Ltac solve_msi :=
    unfold msiM, msiS, msiI in *; lia.
  
  Ltac disc_rule_custom ::=
    try disc_msi.
  
  Section Facts.

    Lemma msiSv_impl_ORqsInit: GoodORqsInit (initsOf impl).
    Proof.
      red; intros.
      cbn; unfold implORqsInit.
      mred.
    Qed.

    Lemma implInv_orqs_weakened:
      forall st oidx orq norq rqt rqi nmsgs,
        ImplInv st ->
        (oidx = child1Idx \/ oidx = child2Idx) ->
        (bst_orqs st)@[oidx] = Some orq ->
        norq = orq +[rqt <- rqi] ->
        ImplInv {| bst_oss := bst_oss st;
                   bst_orqs := (bst_orqs st) +[oidx <- norq];
                   bst_msgs := nmsgs |}.
    Proof.
      unfold ImplInv, ImplStateInv, ImplLockInv; simpl; intros; dest.
      split.
      - disc_rule_conds_const.
        destruct H as [[cv ?] ?].
        destruct H0; subst.
        + solve_rule_conds_ex.
        + solve_rule_conds_ex.
      - disc_rule_conds_const.
        destruct H0; subst; mred.
    Qed.

    Lemma implInv_M_value_changed:
      forall st,
        ImplInv st ->
        forall oidx ost orq,
          (oidx = child1Idx \/ oidx = child2Idx) ->
          (bst_oss st)@[oidx] = Some ost ->
          ost#[implStatusIdx] = msiM ->
          (bst_orqs st)@[oidx] = Some orq ->
          orq@[upRq] = None ->
          forall n (uv: DirT * unit) nmsgs,
            ImplInv
              (Build_MState
                 (oifc:= ImplOStateIfc)
                 ((bst_oss st) +[oidx <- (n, (msiM, uv))])
                 (bst_orqs st) nmsgs).
    Proof.
      unfold ImplInv, ImplStateInv, ImplLockInv; simpl; intros; dest.
      split.
      - disc_rule_conds_const.
        destruct H as [[cv ?] ?].
        disc_rule_conds_ex.
        + destruct H0; discriminate.
        + split.
          * exists n; repeat split.
            { disc_rule_conds_ex.
              destruct H as [|[|]];
                try (exfalso; solve_rule_conds_ex; solve_msi; fail).
              right; right.
              solve_rule_conds_ex.
            }
            { solve_rule_conds_ex; solve_msi. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.
        + split.
          * exists n; repeat split.
            { disc_rule_conds_ex.
              destruct H as [|[|]];
                try (exfalso; solve_rule_conds_ex; solve_msi; fail).
              right; right.
              solve_rule_conds_ex.
            }
            { solve_rule_conds_ex; solve_msi. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.
        + eauto 7.
      - assumption.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_in:
      forall st1 eins st2,
        ImplInv st1 ->
        step_m impl st1 (RlblIns eins) st2 ->
        ImplInv st2.
    Proof.
      intros; inv_step; assumption.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_out:
      forall st1 eouts st2,
        ImplInv st1 ->
        step_m impl st1 (RlblOuts eouts) st2 ->
        ImplInv st2.
    Proof.
      intros; inv_step; assumption.
    Qed.

    Definition MsiSvMsgOutPred: MsgOutPred ImplOStateIfc :=
      fun eout oss orqs =>
        match case (sigOf eout) on sig_dec default True with
        | (ec1, (MRq, Spec.getRq)): False
        | (ec1, (MRq, Spec.setRq)): False
        | (ec1, (MRq, Spec.evictRq)): False
        | (ec2, (MRq, Spec.getRq)): False
        | (ec2, (MRq, Spec.setRq)): False
        | (ec2, (MRq, Spec.evictRq)): False

        | (pc1, (MRs, msiRsS)): 
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiS /\
            post#[implDirIdx].(fst) = msiS /\
            porq@[downRq] = None /\
            msg_value (valOf eout) = VNat post#[implValueIdx]
        | (pc2, (MRs, msiRsS)):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiS /\
            post#[implDirIdx].(snd) = msiS /\
            porq@[downRq] = None /\
            msg_value (valOf eout) = VNat post#[implValueIdx]

        | (pc1, (MRs, msiRsM)):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiI /\
            post#[implDirIdx].(fst) = msiM /\
            porq@[downRq] = None
        | (pc2, (MRs, msiRsM)):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiI /\
            post#[implDirIdx].(snd) = msiM /\
            porq@[downRq] = None

        | (pc1, (MRs, msiRsI)):
            post <-- oss@[parentIdx];
            post#[implDirIdx].(fst) = msiI
        | (pc2, (MRs, msiRsI)):
            post <-- oss@[parentIdx];
            post#[implDirIdx].(snd) = msiI

        | (c1pRs, (MRs, msiDownRsS)):
            cost1 <-- oss@[child1Idx];
            cost1#[implStatusIdx] = msiS /\             
            msg_value (valOf eout) = VNat cost1#[implValueIdx]
        | (c2pRs, (MRs, msiDownRsS)):
            cost2 <-- oss@[child2Idx];
            cost2#[implStatusIdx] = msiS /\
            msg_value (valOf eout) = VNat cost2#[implValueIdx]

        | (c1pRs, (MRs, msiDownRsM)):
            cost1 <-- oss@[child1Idx];
            cost1#[implStatusIdx] = msiI
        | (c2pRs, (MRs, msiDownRsM)):
            cost2 <-- oss@[child2Idx];
            cost2#[implStatusIdx] = msiI
        end.

    Lemma msiSvMsgOutPred_good:
      GoodMsgOutPred topo impl MsiSvMsgOutPred.
    Proof.
      red; intros; repeat split.

      - do 2 (red; intros).
        red in H0; unfold caseDec in H0.
        repeat find_if_inside;
          try (exfalso; auto; fail);
          disc_GoodMsgOutPred.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child1Idx (subtreeIndsOf topo child1Idx)).
          { simpl; tauto. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child2Idx (subtreeIndsOf topo child2Idx)).
          { simpl; tauto. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child1Idx (subtreeIndsOf topo child1Idx)).
          { simpl; tauto. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child2Idx (subtreeIndsOf topo child2Idx)).
          { simpl; tauto. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold caseDec.
          repeat find_if_inside; congruence.

      - do 2 (red; intros).
        red in H0; unfold caseDec in H0.
        repeat find_if_inside;
          try (exfalso; auto; fail);
          disc_GoodMsgOutPred.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child1Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1, <-H6.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child2Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1, <-H6.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child1Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1, <-H6.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child2Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1, <-H6.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child1Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child2Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold caseDec.
          repeat find_if_inside; congruence.
          
      - red; intros.
        destruct (in_dec eq_nat_dec (idOf eout) (sys_merqs impl)); auto.
        right; intros.
        red; unfold caseDec.
        repeat find_if_inside; disc_GoodMsgOutPred.
        auto.

      - red; intros.
        red; unfold caseDec.
        repeat find_if_inside; disc_GoodMsgOutPred.
        auto.
    Qed.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_AtomicInv.

    Lemma msiSv_impl_InvTrs_init:
      forall st1,
        Reachable (steps step_m) impl st1 ->
        ImplInv st1 ->
        forall oidx ridx ins outs st2,
          SubList (idsOf ins) (sys_merqs impl) ->
          step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
          AtomicInv
            MsiSvMsgOutPred
            ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
          ImplInv st2.
    Proof.
      intros.
      inv_step.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree H) as Hulinv.
      pose proof (downLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys H) as Hdlinv.
      good_locking_get obj.
      dest_in.

      (** List of [Rule]s:
       * [childGetRqImm; childGetRqS; childGetRsS; childDownRqS; 
       *  childSetRqImm; childSetRqM; childSetRsM; childDownRqM;
       *  childEvictRqI; childEvictRsI] for [child1Idx] +
       * [childGetRqImm; childGetRqS; childGetRsS; childDownRqS; 
       *  childSetRqImm; childSetRqM; childSetRsM; childDownRqM;
       *  childEvictRqI; childEvictRsI] for [child2Idx] +
       * [parentGetRqImm; parentGetDownRqS; parentSetRqImm; parentSetDownRqM;
       *  parentGetDownRsS; parentSetDownRsM;
       *  parentEvictRqImmI; parentEvictRqImmS; parentEvictRqImmLastS; parentEvictRqImmM]
       *  * {child1Idx, child2Idx}
       *)

      3, 7, 10, 13, 17, 20: atomic_init_exfalso_rs_from_parent.
      all: try (atomic_init_exfalso_rq; fail).

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        assumption.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implInv_orqs_weakened in H0; eauto.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        eapply implInv_M_value_changed in H0; eauto.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implInv_orqs_weakened in H0; eauto.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implInv_orqs_weakened in H0; eauto.

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        replace (orqs +[child2Idx <- norq]) with orqs by meq.
        assumption.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implInv_orqs_weakened in H0; eauto.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (orqs +[child2Idx <- norq]) with orqs by meq.
        eapply implInv_M_value_changed in H0; eauto.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implInv_orqs_weakened in H0; eauto.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implInv_orqs_weakened in H0; eauto.
    Qed.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_msg_case;
      try disc_AtomicInv;
      try disc_msi;
      try disc_minds_const.

    Lemma msiSv_impl_InvTrs: InvTrs impl ImplInv.
    Proof.
      eapply inv_atomic_InvTrs;
        [red; intros; eapply msiSv_impl_InvTrs_ext_in; eauto
        |red; intros; eapply msiSv_impl_InvTrs_ext_out; eauto
        |].
      instantiate (1:= AtomicInv MsiSvMsgOutPred).
      red; intros.
      destruct H1.
      generalize dependent ist2.
      induction H3; simpl; intros; subst;
        [inv_steps; apply msiSv_impl_InvTrs_init; auto|].

      inv_steps.
      pose proof (footprints_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    (reachable_steps H H9))
        as Hftinv.
      specialize (IHAtomic H1 _ H9); dest.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree (reachable_steps H H9)) as Hulinv.
      pose proof (downLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys (reachable_steps H H9)) as Hdlinv.
      inv_step; dest_in.

      (** child1 *)

      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - atomic_cont_exfalso_bound MsiSvMsgOutPred.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        good_footprint_get child1Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H7).
        dest_in; try discriminate; simpl in *.
        cbn in H26; inv H26.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists val0.
              red; repeat ssplit.
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex; solve_msi. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H22; red; simpl in *; mred.
            
      - (** [childDownRqS] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
            red; simpl.
            mred; simpl; auto.
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H7; red; simpl in *; mred.

      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        good_footprint_get child1Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H7).
        dest_in; try discriminate; simpl in *.
        cbn in H26; inv H26.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists n.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                destruct H6 as [|[|]]; try (exfalso; dest; discriminate).
                right; right; solve_rule_conds_ex.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex; solve_msi. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H22; red; simpl in *; mred.

      - (** [childDownRqM] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
            red; simpl.
            mred; simpl; auto.
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H7; red; simpl in *; mred.

      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        good_footprint_get child1Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H7).
        dest_in; try discriminate; simpl in *.
        cbn in H21; inv H21.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            rename porq into orq.
            destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H20; red; simpl in *; mred.

      (** child2 *)
      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - atomic_cont_exfalso_bound MsiSvMsgOutPred.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        good_footprint_get child2Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H7).
        dest_in; try discriminate; simpl in *.
        cbn in H26; inv H26.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists val0.
              red; repeat ssplit.
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H22; red; simpl in *; mred.

      - (** [childDownRqS] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
            red; simpl.
            mred; simpl; auto.
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct H6 as [[cv ?] [? ?]].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H7; red; simpl in *; mred.
        
      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        good_footprint_get child2Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H7).
        dest_in; try discriminate; simpl in *.
        cbn in H26; inv H26.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists n.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                destruct H6 as [|[|]]; try (exfalso; dest; discriminate).
                right; right; solve_rule_conds_ex.
              }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H22; red; simpl in *; mred.
          
      - (** [childDownRqM] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
            red; simpl.
            mred; simpl; auto.
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct H6 as [[cv ?] [? ?]].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H7; red; simpl in *; mred.

      - atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        good_footprint_get child2Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H7).
        dest_in; try discriminate; simpl in *.
        cbn in H21; inv H21.

        (* construction *)
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsDown_preserves_msg_out_preds; eauto;
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys
              |red; auto
              |exact msiSvMsgOutPred_good].
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            rename porq into orq.
            destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex; solve_msi. }
          * red in H20; red; simpl in *; mred.

      (** parent(child1) *)

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; left.
                destruct H6 as [|[|]].
                { solve_rule_conds_ex; solve_msi. }
                { solve_rule_conds_ex. }
                { solve_msi. }
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
              clear H24.
              eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred.
          * solve_rule_conds_ex.

      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in H13; simpl in H13.

            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; right; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
              clear H24.
              eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentSetDownRqM] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred.
          * solve_rule_conds_ex.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.

        (* discharge the lock invariant *)
        destruct H6.
        red in H8; simpl in H8.
        disc_rule_conds_const.
        red in H8.
        disc_rule_conds_const.
        destruct H8; dest; [|discriminate].
        rewrite H10 in *.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsUps_preserves_msg_out_preds
              with (rsUps:= [(c2pRs, rmsg)]); eauto.
            { exact msiSv_impl_ORqsInit. }
            { exact msiSv_impl_RqRsSys. }
            { repeat constructor; intro; dest_in. }
            { apply SubList_cons; [|apply SubList_nil].
              assumption.
            }
            { instantiate (1:= fun _ => True).
              instantiate (1:= [pc2]).
              repeat split.
              { discriminate. }
              { repeat constructor.
                simpl; exists child2Idx.
                repeat split.
              }
            }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; simpl.
            solve_rule_conds_ex.
        + split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.

            assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
            clear H21.
            eapply upLockInvORq_parent_locked_locked in H22; try reflexivity;
              [|red; repeat (simpl; mred); eauto]; dest.
          
            split.
            { exists val0.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; left; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentSetDownRsM] *)
        disc_rule_conds_ex.

        (* discharge the lock invariant *)
        destruct H6.
        red in H8; simpl in H8.
        disc_rule_conds_const.
        red in H8.
        disc_rule_conds_const.
        destruct H8; dest; [|discriminate].
        rewrite H10 in *.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsUps_preserves_msg_out_preds
              with (rsUps:= [(c2pRs, rmsg)]); eauto.
            { exact msiSv_impl_ORqsInit. }
            { exact msiSv_impl_RqRsSys. }
            { repeat constructor; intro; dest_in. }
            { apply SubList_cons; [|apply SubList_nil].
              assumption.
            }
            { instantiate (1:= fun _ => True).
              instantiate (1:= [pc2]).
              repeat split.
              { discriminate. }
              { repeat constructor.
                simpl; exists child2Idx.
                repeat split.
              }
            }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; simpl.
            solve_rule_conds_ex.
        + split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.

            assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
            clear H21.
            eapply upLockInvORq_parent_locked_locked in H22; try reflexivity;
              [|red; repeat (simpl; mred); eauto]; dest.

            split.
            { exists val0.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; right; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentEvictRqImmI] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred.
          * red in H7; red; simpl in *; mred.
        
      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in *; simpl in *.
            disc_rule_conds_ex.
            destruct H6 as [|[|]];
              [exfalso; solve_rule_conds_ex
              | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
            split.
            { exists cv.
              repeat ssplit.
              { solve_rule_conds_ex.
                right; left; solve_msi.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
              clear H6.
              eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentEvictRqImmLastS] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in *; simpl in *.
            disc_rule_conds_ex.
            destruct H6 as [|[|]];
              [exfalso; solve_rule_conds_ex
              | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
            split.
            { exists cv.
              repeat ssplit.
              { solve_rule_conds_ex.
                left; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
              clear H6.
              eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child1Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in *; simpl in *.
            disc_rule_conds_ex.
            destruct H6 as [|[|]]; try (exfalso; solve_rule_conds_ex; fail).

            assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
            clear H26.
            eapply upLockInvORq_rqUp_length_one_locked in H27; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            disc_rule_conds_ex.
          
            split.
            { exists n.
              repeat ssplit.
              { solve_rule_conds_ex.
                left; solve_msi.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex. }
          * red in H7; red; simpl in *; mred.

      (** parent(child2) *)

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; left.
                destruct H6 as [|[|]].
                { solve_rule_conds_ex; solve_msi. }
                { solve_rule_conds_ex. }
                { solve_msi. }
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
              clear H24.
              eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred.
          * solve_rule_conds_ex.

      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in H14; simpl in H14.
            split.
            { exists cv.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; right; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
              clear H24.
              eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentSetDownRqM] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred.
          * solve_rule_conds_ex.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.

        (* discharge the lock invariant *)
        destruct H6.
        red in H8; simpl in H8.
        disc_rule_conds_const.
        red in H8.
        disc_rule_conds_const.
        destruct H8; dest; [discriminate|].
        rewrite H10 in *.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsUps_preserves_msg_out_preds
              with (rsUps:= [(c1pRs, rmsg)]); eauto.
            { exact msiSv_impl_ORqsInit. }
            { exact msiSv_impl_RqRsSys. }
            { repeat constructor; intro; dest_in. }
            { apply SubList_cons; [|apply SubList_nil].
              assumption.
            }
            { instantiate (1:= fun _ => True).
              instantiate (1:= [pc1]).
              repeat split.
              { discriminate. }
              { repeat constructor.
                simpl; exists child1Idx.
                repeat split.
              }
            }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; simpl.
            solve_rule_conds_ex.
        + split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.

            assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
            clear H21.
            eapply upLockInvORq_parent_locked_locked in H22; try reflexivity;
              [|red; repeat (simpl; mred); eauto]; dest.
          
            split.
            { exists val0.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; left; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentSetDownRsM] *)
        disc_rule_conds_ex.

        (* discharge the lock invariant *)
        destruct H6.
        red in H8; simpl in H8.
        disc_rule_conds_const.
        red in H8.
        disc_rule_conds_const.
        destruct H8; dest; [discriminate|].
        rewrite H10 in *.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsUps_preserves_msg_out_preds
              with (rsUps:= [(c1pRs, rmsg)]); eauto.
            { exact msiSv_impl_ORqsInit. }
            { exact msiSv_impl_RqRsSys. }
            { repeat constructor; intro; dest_in. }
            { apply SubList_cons; [|apply SubList_nil].
              assumption.
            }
            { instantiate (1:= fun _ => True).
              instantiate (1:= [pc1]).
              repeat split.
              { discriminate. }
              { repeat constructor.
                simpl; exists child1Idx.
                repeat split.
              }
            }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; simpl.
            solve_rule_conds_ex.
        + split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.

            assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
            clear H21.
            eapply upLockInvORq_parent_locked_locked in H22; try reflexivity;
              [|red; repeat (simpl; mred); eauto]; dest.

            split.
            { exists val0.
              red; repeat ssplit.
              { solve_rule_conds_ex.
                right; right; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentEvictRqImmI] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred.
          * red in H7; red; simpl in *; mred.
        
      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in *; simpl in *.
            disc_rule_conds_ex.
            destruct H6 as [|[|]];
              [exfalso; solve_rule_conds_ex
              | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
            split.
            { exists cv.
              repeat ssplit.
              { solve_rule_conds_ex.
                right; left; solve_msi.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
              clear H6.
              eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentEvictRqImmLastS] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in *; simpl in *.
            disc_rule_conds_ex.
            destruct H6 as [|[|]];
              [exfalso; solve_rule_conds_ex
              | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
            split.
            { exists cv.
              repeat ssplit.
              { solve_rule_conds_ex.
                left; auto.
              }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { disc_rule_conds_ex.
              assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
                by (simpl; tauto).
              good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
              clear H6.
              eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
                [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
              solve_rule_conds_ex.
            }
          * red in H7; red; simpl in *; mred.

      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqUp_preserves_msg_out_preds with (oidx:= child2Idx);
              [exact msiSv_impl_ORqsInit
              |exact msiSv_impl_RqRsSys|..]; eauto.
            { intro; dest_in; discriminate. }
            { red; auto. }
            { exact msiSvMsgOutPred_good. }
          * repeat (constructor; simpl).
            red; repeat (simpl; mred).
        + destruct H6; split.
          * red in H6; red; simpl in *; mred; simpl.
            destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
            destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
            destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
            destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
            destruct H6 as [[cv ?] ?].
            red in H6; dest.
            unfold getDir in *; simpl in *.
            disc_rule_conds_ex.
            destruct H6 as [|[|]]; try (exfalso; solve_rule_conds_ex; fail).

            assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
            clear H26.
            eapply upLockInvORq_rqUp_length_one_locked in H27; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            disc_rule_conds_ex.
          
            split.
            { exists n.
              repeat ssplit.
              { solve_rule_conds_ex.
                left; solve_msi.
              }
              { solve_rule_conds_ex; solve_msi. }
              { solve_rule_conds_ex. }
              { solve_rule_conds_ex. }
            }
            { solve_rule_conds_ex. }
          * red in H7; red; simpl in *; mred.

    Qed.

    Lemma implInv_init:
      ImplInv (initsOf impl).
    Proof.
      red; simpl.
      unfold implOStatesInit, implORqsInit; mred.
      simpl.
      repeat split.
      exists 0.
      repeat split; intros.
      - vm_compute; intros.
        right; left; auto.
      - discriminate.
      - discriminate.
      - vm_compute; intros; auto.
      - vm_compute; intros; auto.
    Qed.

    Lemma implInv_invStep:
      InvStep impl step_m ImplInv.
    Proof.
      apply invSeq_serializable_invStep.
      - apply implInv_init.
      - apply inv_trs_seqSteps.
        apply msiSv_impl_InvTrs.
      - eapply rqrs_Serializable.
        + apply msiSv_impl_ORqsInit.
        + apply msiSv_impl_RqRsSys.
    Qed.

  End Facts.
  
End Inv.

Hint Unfold ImplOStateM ImplOStateS ImplOStateI ImplOStateMSI
     ImplDirM ImplDirS ImplDirI
     ImplDirCoh ImplParentCoh ImplChildCoh1 ImplChildCoh2 ImplChildrenCoh
     ImplStateCoh: RuleConds.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

