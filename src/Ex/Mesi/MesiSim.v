Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** TODO: refactor; will be used by MOSI as well. *)
Lemma tree2Topo_internal_chns_not_exts:
  forall tr bidx oidx,
    let cifc := snd (tree2Topo tr bidx) in
    In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
    DisjList [rqUpFrom oidx; rsUpFrom oidx; downTo oidx]
             ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
Proof.
  intros.
  eapply DisjList_SubList.
  - apply tree2Topo_obj_chns_minds_SubList; eassumption.
  - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
    apply DisjList_comm, DisjList_app_4.
    + apply DisjList_comm, tree2Topo_minds_merqs_disj.
    + apply DisjList_comm, tree2Topo_minds_merss_disj.
Qed.

Ltac solve_not_in_ext_chns :=
  eapply DisjList_In_2;
  [eapply tree2Topo_internal_chns_not_exts;
   apply in_or_app; eauto|simpl; tauto].

(** TODO: refactor; will be used by MOSI as well. *)
Section SimExtMP.
  Variable (l1s: list IdxT).

  Let erqs := map (fun cidx => rqUpFrom (l1ExtOf cidx)) l1s.
  Let erss := map (fun cidx => downTo (l1ExtOf cidx)) l1s.

  Definition SimExtMP (imsgs: MessagePool Msg) (iorqs: ORqs Msg)
             (smsgs: MessagePool Msg) :=
    Forall
      (fun cidx =>
         let eidx := l1ExtOf cidx in
         (corq <-- iorqs@[cidx];
            (corq@[upRq] >>= (fun rqiu => rqiu.(rqi_msg)))
              ::> (findQ (rqUpFrom eidx) imsgs) = findQ (rqUpFrom eidx) smsgs) /\
         findQ (downTo eidx) imsgs = findQ (downTo eidx) smsgs)
      l1s.

  Ltac disc_SimExtMP :=
    unfold SimExtMP; intros;
    repeat
      match goal with
      | [ |- Forall _ l1s] =>
        let cidx := fresh "cidx" in
        let He := fresh "He" in
        apply Forall_forall; intros cidx He
      | [H1: Forall _ l1s, H2: In _ l1s |- _] =>
        rewrite Forall_forall in H1; specialize (H1 _ H2)
      end.

  Lemma SimExtMP_enqMsgs:
    forall eins,
      NoDup (idsOf eins) ->
      forall imsgs orqs smsgs,
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (enqMsgs eins imsgs) orqs (enqMsgs eins smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    repeat split.
    - destruct (in_dec idx_dec (rqUpFrom (l1ExtOf cidx)) (idsOf eins)).
      + apply in_map_iff in i.
        destruct i as [[midx msg] ?]; dest; simpl in *; subst.
        do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
        rewrite ocons_app; congruence.
      + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
        assumption.
    - destruct (in_dec idx_dec (downTo (l1ExtOf cidx)) (idsOf eins)).
      + apply in_map_iff in i.
        destruct i as [[midx msg] ?]; dest; simpl in *; subst.
        do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
        congruence.
      + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
        assumption.
  Qed.

  Corollary SimExtMP_enqMP:
    forall midx msg imsgs orqs smsgs,
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (enqMP midx msg imsgs) orqs (enqMP midx msg smsgs).
  Proof.
    intros.
    eapply SimExtMP_enqMsgs with (eins:= [(midx, msg)]) in H; auto.
    repeat constructor; intro; dest_in.
  Qed.

  Lemma SimExtMP_orqs:
    forall imsgs orqs1 orqs2 smsgs,
      SimExtMP imsgs orqs1 smsgs ->
      Forall (fun cidx => orqs1@[cidx] = orqs2@[cidx]) l1s ->
      SimExtMP imsgs orqs2 smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
  Qed.

  Lemma SimExtMP_ext_outs_deqMsgs:
    forall eouts,
      SubList (idsOf eouts) erss ->
      NoDup (idsOf eouts) ->
      forall imsgs orqs smsgs,
        Forall (FirstMPI imsgs) eouts ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (deqMsgs (idsOf eouts) imsgs) orqs (deqMsgs (idsOf eouts) smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    repeat split.
    - destruct (in_dec idx_dec (rqUpFrom (l1ExtOf cidx)) (idsOf eouts)).
      + exfalso.
        apply H in i.
        apply in_map_iff in i; dest.
        discriminate.
      + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
        assumption.
    - destruct (in_dec idx_dec (downTo (l1ExtOf cidx)) (idsOf eouts)).
      + apply in_map_iff in i; destruct i as [[midx msg] ?]; dest.
        simpl in *; subst.
        apply findQ_deqMsgs_eq; assumption.
      + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
        assumption.
  Qed.

  Lemma SimExtMP_ext_outs_FirstMPI:
    forall eouts,
      SubList (idsOf eouts) erss ->
      NoDup (idsOf eouts) ->
      forall imsgs orqs smsgs,
        SimExtMP imsgs orqs smsgs ->
        Forall (FirstMPI imsgs) eouts ->
        Forall (FirstMPI smsgs) eouts.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    apply Forall_forall; intros [midx msg] ?.
    rewrite Forall_forall in H2; specialize (H2 _ H3).
    apply in_map with (f:= idOf) in H3.
    apply H in H3; unfold idOf, fst in H3.
    apply in_map_iff in H3; destruct H3 as [cidx ?]; dest; subst.
    rewrite Forall_forall in H1; specialize (H1 _ H4); dest.
    unfold FirstMPI, FirstMP, firstMP in *; simpl in *.
    congruence.
  Qed.

  Lemma SimExtMP_outs_deqMP_child:
    forall cidx msg imsgs (orqs: ORqs Msg) smsgs corq,
      In cidx l1s ->
      orqs@[cidx] = Some corq ->
      corq@[upRq] = None ->
      FirstMPI imsgs (rqUpFrom (l1ExtOf cidx), msg) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (deqMP (rqUpFrom (l1ExtOf cidx)) imsgs) orqs
               (deqMP (rqUpFrom (l1ExtOf cidx)) smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    destruct (idx_dec cidx cidx0); subst.
    - disc_rule_conds_ex.
      pose proof (findQ_eq_FirstMPI H2 _ H3).
      apply findQ_In_deqMP_FirstMP in H2.
      apply findQ_In_deqMP_FirstMP in H5; simpl in *.
      rewrite <-H2, <-H5 in H3; inv H3.
      split; auto.
      do 2 (rewrite findQ_not_In_deqMP by (intro; subst; discriminate)).
      assumption.
    - do 2 (rewrite findQ_not_In_deqMP
             by (intro Hx; injection Hx; intros; auto)).
      do 2 (rewrite findQ_not_In_deqMP by (intro; subst; discriminate)).
      split; assumption.
  Qed.
  
  Lemma SimExtMP_impl_enqMP_indep:
    forall midx msg imsgs (orqs: ORqs Msg) smsgs,
      ~ In midx (erqs ++ erss) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (enqMP midx msg imsgs) orqs smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split.
    - rewrite findQ_not_In_enqMP; [assumption|].
      intro; subst.
      elim H; apply in_or_app; left.
      apply in_map with (f:= fun cidx => rqUpFrom (l1ExtOf cidx)) in He.
      assumption.
    - rewrite findQ_not_In_enqMP; [assumption|].
      intro; subst.
      elim H. apply in_or_app; right.
      apply in_map with (f:= fun cidx => downTo (l1ExtOf cidx)) in He.
      assumption.
  Qed.

  Lemma SimExtMP_impl_deqMP_indep:
    forall midx imsgs (orqs: ORqs Msg) smsgs,
      ~ In midx (erqs ++ erss) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (deqMP midx imsgs) orqs smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split.
    - rewrite findQ_not_In_deqMP; [assumption|].
      intro; subst.
      elim H; apply in_or_app; left.
      apply in_map with (f:= fun cidx => rqUpFrom (l1ExtOf cidx)) in He.
      assumption.
    - rewrite findQ_not_In_deqMP; [assumption|].
      intro; subst.
      elim H. apply in_or_app; right.
      apply in_map with (f:= fun cidx => downTo (l1ExtOf cidx)) in He.
      assumption.
  Qed.

  Lemma SimExtMP_spec_deqMP_locked:
    forall cidx imsgs (orqs: ORqs Msg) smsgs porq norq rqiu msg,
      orqs@[cidx] = Some porq ->
      porq@[upRq] = None -> norq@[upRq] = Some rqiu ->
      FirstMPI imsgs (rqUpFrom (l1ExtOf cidx), msg) ->
      rqiu.(rqi_msg) = Some msg ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (deqMP (rqUpFrom (l1ExtOf cidx)) imsgs)
               (orqs +[cidx <- norq]) smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    - split.
      + rewrite findQ_In_deqMP_FirstMP; assumption.
      + rewrite findQ_not_In_deqMP by discriminate; assumption.
    - split.
      + rewrite findQ_not_In_deqMP
          by (intro Hx; subst; injection Hx; intros; auto).
        assumption.
      + rewrite findQ_not_In_deqMP by (intro; subst; discriminate).
        assumption.
  Qed.

  Lemma SimExtMP_spec_deqMP_unlocked:
    forall cidx imsgs (orqs: ORqs Msg) smsgs porq rqiu norq,
      orqs@[cidx] = Some porq ->
      porq@[upRq] = Some rqiu -> rqiu.(rqi_msg) <> None ->
      norq@[upRq] = None ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP imsgs (orqs +[cidx <- norq]) (deqMP (rqUpFrom (l1ExtOf cidx)) smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    - split.
      + destruct (rqi_msg rqiu); [|exfalso; auto].
        unfold deqMP, findQ in *; simpl in *.
        rewrite <-H3; mred.
      + rewrite findQ_not_In_deqMP by discriminate; assumption.
    - split.
      + rewrite findQ_not_In_deqMP
          by (intro Hx; subst; injection Hx; intros; auto).
        assumption.
      + rewrite findQ_not_In_deqMP by (intro; subst; discriminate).
        assumption.
  Qed.
  
End SimExtMP.

Section Sim.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).
  Let impl := Mesi.impl Htr.

  Axiom c_l1_indices_NoPrefix: NoPrefix (c_l1_indices cifc).
  Local Definition spec := @SpecInds.spec (c_l1_indices cifc) c_l1_indices_NoPrefix.

  Existing Instance Mesi.ImplOStateIfc.

  (** NOTE: simulation only states about coherent values. 
   * Exclusiveness is stated and proven as an invariant. *)

  (** TODO: move to [MesiInv.v] *)
  Definition ImplOStateMESI (cv: nat) (ost: OState): Prop :=
    mesiS <= ost#[implStatusIdx] -> ost#[implValueIdx] = cv.
  Hint Unfold ImplOStateMESI: RuleConds.

  Section ObjCoh.
    Variables (cv: nat)
              (cidx: IdxT)
              (cost: OState)
              (msgs: MessagePool Msg).

    Definition DirMsgCoh (idm: Id Msg) :=
      match case (sigOf idm) on sig_dec default True with
      | (downTo cidx, (MRs, mesiRsS)): (valOf idm).(msg_value) = cv
      | (downTo cidx, (MRs, mesiRsE)): (valOf idm).(msg_value) = cv
      | (rsUpFrom cidx, (MRs, mesiDownRsS)): (valOf idm).(msg_value) = cv
      | (rqUpFrom cidx, (MRq, mesiRqI)):
          (cost#[implStatusIdx] = mesiM -> (valOf idm).(msg_value) = cv)
      end.

    Definition DirMsgsCoh :=
      forall idm, InMPI msgs idm -> DirMsgCoh idm.

    Definition DirCoh :=
      ImplOStateMESI cv cost /\ DirMsgsCoh.

  End ObjCoh.

  Section DirMsgsCohFacts.

    Lemma DirMsgsCoh_other_midx_enqMP:
      forall cv cidx cost msgs,
        DirMsgsCoh cv cidx cost msgs ->
        forall midx msg,
          ~ In midx [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          DirMsgsCoh cv cidx cost (enqMP midx msg msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_enqMP_or in H1; destruct H1; auto.
      destruct idm as [midx' msg']; simpl in *; dest; subst.
      destruct msg as [mid mty mval].
      red; cbv [sigOf idOf valOf fst snd msg_id msg_type].
      unfold caseDec.
      repeat (find_if_inside; [inv e; exfalso; intuition idtac|]).
      auto.
    Qed.

    Lemma DirMsgsCoh_other_midx_enqMsgs:
      forall cv cidx cost msgs,
        DirMsgsCoh cv cidx cost msgs ->
        forall eins,
          DisjList (idsOf eins) [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          DirMsgsCoh cv cidx cost (enqMsgs eins msgs).
    Proof.
      intros.
      generalize dependent msgs.
      induction eins as [|ein eins]; simpl; intros; [assumption|].
      destruct ein as [midx msg]; simpl in *.
      apply DisjList_cons in H0; dest.
      eapply IHeins; eauto.
      apply DirMsgsCoh_other_midx_enqMP; auto.
    Qed.

    Lemma DirMsgsCoh_other_msg_id_enqMP:
      forall cv cidx cost msgs,
        DirMsgsCoh cv cidx cost msgs ->
        forall midx msg,
          ~ In (msg_id msg) [mesiRsS; mesiRsE; mesiDownRsS; mesiRqI] ->
          DirMsgsCoh cv cidx cost (enqMP midx msg msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_enqMP_or in H1; destruct H1; auto.
      destruct idm as [midx' msg']; simpl in *; dest; subst.
      destruct msg as [mid mty mval]; simpl in H0.
      red; cbv [sigOf idOf valOf fst snd msg_id msg_type].
      unfold caseDec.
      repeat (find_if_inside; [inv e; exfalso; intuition idtac|]).
      auto.
    Qed.

    Lemma DirMsgsCoh_other_msg_id_enqMsgs:
      forall cv cidx cost msgs,
        DirMsgsCoh cv cidx cost msgs ->
        forall eins,
          DisjList (map (fun idm => msg_id (valOf idm)) eins)
                   [mesiRsS; mesiRsE; mesiDownRsS; mesiRqI] ->
          DirMsgsCoh cv cidx cost (enqMsgs eins msgs).
    Proof.
      intros.
      generalize dependent msgs.
      induction eins as [|ein eins]; simpl; intros; [assumption|].
      destruct ein as [midx msg]; simpl in *.
      apply DisjList_cons in H0; dest.
      eapply IHeins; eauto.
      apply DirMsgsCoh_other_msg_id_enqMP; auto.
    Qed.

    Lemma DirMsgsCoh_deqMP:
      forall cv cidx cost msgs,
        DirMsgsCoh cv cidx cost msgs ->
        forall midx,
          DirMsgsCoh cv cidx cost (deqMP midx msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_deqMP in H0; auto.
    Qed.

    Lemma DirMsgsCoh_deqMsgs:
      forall cv cidx cost msgs,
        DirMsgsCoh cv cidx cost msgs ->
        forall minds,
          DirMsgsCoh cv cidx cost (deqMsgs minds msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_deqMsgs in H0; auto.
    Qed.

  End DirMsgsCohFacts.

  Definition ImplStateCoh (cv: nat) (st: MState): Prop :=
    (most <-- (bst_oss st)@[rootOf topo]; ImplOStateMESI cv most) /\
    Forall (fun oidx => ost <-- (bst_oss st)@[oidx]; DirCoh cv oidx ost (bst_msgs st))
           (tl (c_li_indices cifc) ++ c_l1_indices cifc).

  Definition SpecStateCoh (cv: nat) (st: @MState SpecOStateIfc): Prop :=
    sost <-- (bst_oss st)@[specIdx];
      sorq <-- (bst_orqs st)@[specIdx];
      sost#[specValueIdx] = cv.

  Inductive SimState: MState -> @MState SpecOStateIfc -> Prop :=
  | SimStateIntro:
      forall cv ist sst,
        SpecStateCoh cv sst ->
        ImplStateCoh cv ist ->
        SimState ist sst.

  Definition SimMESI (ist: MState) (sst: @MState SpecOStateIfc): Prop :=
    SimState ist sst /\
    SimExtMP (c_l1_indices cifc) ist.(bst_msgs) ist.(bst_orqs) sst.(bst_msgs).

  Hint Unfold DirCoh ImplStateCoh: RuleConds.

  Section Facts.

    Lemma simMesi_init:
      SimMESI (initsOf impl) (initsOf spec).
    Proof.
      split.
      - apply SimStateIntro with (cv:= 0).
        + reflexivity.
        + repeat split.
          * simpl; rewrite implOStatesInit_value.
            { compute; auto. }
            { apply in_or_app; left.
              rewrite c_li_indices_head_rootOf by assumption.
              left; reflexivity.
            }
          * apply Forall_forall; intros oidx ?.
            simpl; rewrite implOStatesInit_value.
            { simpl; split; [compute; auto|].
              red; intros.
              do 2 red in H0; dest_in.
            }
            { apply in_or_app.
              apply in_app_or in H; destruct H; auto.
              apply tl_In in H; auto.
            }
      - red; apply Forall_forall; intros oidx ?.
        repeat split.
        simpl; unfold implORqsInit.
        rewrite initORqs_value; [|apply in_or_app; auto].
        simpl; mred.
    Qed.

    Lemma simMesi_sim_silent:
      forall ist sst1,
        SimMESI ist sst1 ->
        exists slbl sst2,
          getLabel (RlblEmpty Msg) = getLabel slbl /\
          step_m spec sst1 slbl sst2 /\ SimMESI ist sst2.
    Proof.
      simpl; intros.
      exists (RlblEmpty _); eexists.
      repeat ssplit; eauto.
      constructor.
    Qed.

    Lemma simMesi_sim_ext_in:
      forall oss orqs msgs sst1,
        SimMESI {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} sst1 ->
        forall eins,
          eins <> nil -> ValidMsgsExtIn impl eins ->
          exists slbl sst2,
            getLabel (RlblIns eins) = getLabel slbl /\
            step_m spec sst1 slbl sst2 /\
            SimMESI {| bst_oss := oss;
                       bst_orqs := orqs;
                       bst_msgs := enqMsgs eins msgs |} sst2.
    Proof.
      destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
      red in H; simpl in *; dest.
      exists (RlblIns eins); eexists.
      repeat ssplit.
      + reflexivity.
      + eapply SmIns; eauto.
        destruct H1; split; [|assumption].
        simpl in *; rewrite c_merqs_l1_rqUpFrom in H1.
        assumption.
      + split.
        * inv H.
          apply SimStateIntro with (cv:= cv); [assumption|].
          red in H4; simpl in H4; dest.
          split; simpl; [assumption|].
          apply Forall_forall; intros oidx ?.
          rewrite Forall_forall in H4; specialize (H4 _ H5).
          disc_rule_conds_ex.
          split; [assumption|].
          apply DirMsgsCoh_other_midx_enqMsgs; [assumption|].
          destruct H1; simpl in H1.
          eapply DisjList_SubList; [eassumption|].
          apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
          { apply tree2Topo_obj_chns_minds_SubList.
            apply in_or_app.
            apply in_app_or in H5; destruct H5; auto.
            apply tl_In in H5; auto.
          }
          { apply tree2Topo_minds_merqs_disj. }
        * apply SimExtMP_enqMsgs; auto.
          apply H1.
    Qed.

    Lemma simMesi_sim_ext_out:
      forall oss orqs msgs sst1,
        SimMESI {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} sst1 ->
        forall eouts: list (Id Msg),
          eouts <> nil ->
          Forall (FirstMPI msgs) eouts ->
          ValidMsgsExtOut impl eouts ->
          exists slbl sst2,
            getLabel (RlblOuts eouts) = getLabel slbl /\
            step_m spec sst1 slbl sst2 /\
            SimMESI {| bst_oss := oss;
                       bst_orqs := orqs;
                       bst_msgs := deqMsgs (idsOf eouts) msgs |} sst2.
    Proof.
      destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
      red in H; simpl in *; dest.
      destruct H2; unfold impl in H2; simpl in H2.
      rewrite c_merss_l1_downTo in H2.
      exists (RlblOuts eouts); eexists.
      repeat ssplit.
      - reflexivity.
      - eapply SmOuts with (msgs0:= smsgs1); eauto.
        + eapply SimExtMP_ext_outs_FirstMPI; eauto.
        + split; assumption.
      - split.
        + inv H.
          apply SimStateIntro with (cv:= cv); [assumption|].
          red in H6; simpl in H6; dest.
          split; simpl; [assumption|].
          apply Forall_forall; intros oidx ?.
          rewrite Forall_forall in H6; specialize (H6 _ H7).
          disc_rule_conds_ex.
          split; [assumption|].
          apply DirMsgsCoh_deqMsgs; assumption.
        + apply SimExtMP_ext_outs_deqMsgs; auto.
    Qed.

    Definition ImplInvEx (st: MState) :=
      True. (* ImplInv st /\ ImplInvB st. *)

    Hint Unfold ImplInvEx (* ImplInv ImplInvB *): RuleConds.

    Ltac spec_constr_step_get_FirstMPI :=
      repeat constructor;
      repeat
        match goal with
        | [H: SimExtMP _ _ _ _ |- _] => red in H
        | [Hf: Forall _ ?l, Hin: In _ ?l |- _] =>
          rewrite Forall_forall in Hf; specialize (Hf _ Hin);
          disc_rule_conds_const; dest
        end;
      eapply findQ_eq_FirstMPI; eauto.

    Ltac spec_constr_step_get_ValidMsgs :=
      match goal with
      | [H: In _ (c_l1_indices _) |- _] =>
        clear -H; split;
        [simpl; apply SubList_cons; [|apply SubList_nil];
         apply in_map with (f:= fun cidx => _ (l1ExtOf cidx));
         assumption|
         repeat constructor; intro; dest_in]
      end.

    Ltac spec_constr_step_get cidx :=
      eapply SmInt with (ins:= [(rqUpFrom (l1ExtOf cidx), _)]);
      try reflexivity;
      [left; reflexivity
      |simpl; apply specGetRq_in_specRules, in_map; assumption
      |reflexivity
      |eassumption
      |eassumption
      |spec_constr_step_get_FirstMPI
      |spec_constr_step_get_ValidMsgs
      |solve_rule_conds_ex;
       match goal with
       | [H: msg_id ?msg = _ |- context[msg_id ?msg] ] => rewrite H
       end; reflexivity
      |spec_constr_step_get_ValidMsgs
      |solve_DisjList idx_dec].

    Ltac spec_case_get cidx :=
      eexists (RlblInt specIdx (rule_idx (specGetRq (l1ExtOf cidx))) _ _);
      eexists;
      repeat ssplit;
      [reflexivity|spec_constr_step_get cidx|].

    Ltac spec_case_silent :=
      idtac; exists (RlblEmpty _); eexists;
      repeat ssplit;
      [reflexivity
      |econstructor
      |].

    Ltac solve_sim_ext_mp :=
      repeat
        (match goal with
         | [ |- SimExtMP _ (enqMP _ _ _) _ (enqMP _ _ _) ] =>
           apply SimExtMP_enqMP
         | [ |- SimExtMP _ (deqMP ?midx _) _ (deqMP ?midx _) ] =>
           eapply SimExtMP_outs_deqMP_child; eauto; mred; fail
         | [ |- SimExtMP _ (enqMP _ _ _) _ _ ] =>
           apply SimExtMP_impl_enqMP_indep; [solve_not_in_ext_chns; fail|]
         | [ |- SimExtMP _ (deqMP _ _) _ _ ] =>
           eapply SimExtMP_spec_deqMP_locked; eauto; [mred|reflexivity]; fail
         | [ |- SimExtMP _ (deqMP _ _) _ _ ] =>
           apply SimExtMP_impl_deqMP_indep; [solve_not_in_ext_chns; fail|]
         | [ |- SimExtMP _ _ _ (deqMP _ _) ] =>
           eapply SimExtMP_spec_deqMP_unlocked; eauto; [congruence|mred]; fail
         | [ |- SimExtMP _ _ (?m +[?k <- ?v]) _ ] =>
           apply SimExtMP_orqs with (orqs1:= m);
           [|apply Forall_forall; intros; mred]
         end; try assumption).

    Ltac disc_rule_custom ::=
      repeat
        match goal with
        | [H: Forall _ (tl (c_li_indices _) ++ c_l1_indices _) |- _] =>
          apply Forall_app_inv in H; dest
        | [Hf: Forall _ (c_l1_indices ?ifc), Hin: In _ (c_l1_indices ?ifc) |- _] =>
          rewrite Forall_forall in Hf; pose proof (Hf _ Hin);
          disc_rule_conds_const; dest
        | [H: fst ?ost = fst _ |- context[fst ?ost] ] =>
          (* rewriting a coherent value *) rewrite H in *
        end.

    Lemma simMesi_sim:
      InvSim step_m step_m ImplInvEx SimMESI impl spec.
    Proof.
      red; intros.

      pose proof (footprints_ok
                    (mesi_GoodORqsInit Htr)
                    (mesi_GoodRqRsSys Htr) H) as Hftinv.
      pose proof (upLockInv_ok
                    (mesi_GoodORqsInit Htr)
                    (mesi_GoodRqRsSys Htr)
                    (mesi_RqRsDTree Htr) H) as Hpulinv.
      pose proof (upLockInv_ok
                    (mesi_GoodORqsInit Htr)
                    (mesi_GoodRqRsSys Htr)
                    (mesi_RqRsDTree Htr)
                    (reachable_steps H (steps_singleton H2))) as Hnulinv.

      inv H2;
        [apply simMesi_sim_silent; assumption
        |apply simMesi_sim_ext_in; assumption
        |apply simMesi_sim_ext_out; assumption
        |].

      destruct sst1 as [soss1 sorqs1 smsgs1].
      destruct H0; simpl in H0, H2; simpl.
      inv H0.
      red in H15; simpl in H15; dest. (** maybe need to discharge more? *)
      red in H6; simpl in H6.
      destruct (soss1@[specIdx]) as [sost|] eqn:Hsost; simpl in *; [|exfalso; auto].
      destruct (sorqs1@[specIdx]) as [sorq|] eqn:Hsorq; simpl in *; [|exfalso; auto].
      dest; subst.

      simpl in H4; destruct H4; [subst|].
      1: {
        (*! Cases for the main memory *)
        admit.
      }

      apply in_app_or in H4; destruct H4.

      - (*! Cases for Li caches *)
        apply in_map_iff in H4; destruct H4 as [oidx [? ?]]; subst; simpl in *.
        admit.

      - (*! Cases for L1 caches *)
        apply in_map_iff in H4; destruct H4 as [oidx [? ?]]; subst.
        dest_in.

        + (* [l1GetSImm] *)
          disc_rule_conds_ex.
          spec_case_get oidx.

          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl; split.
              { solve_rule_conds_ex. }
              { apply Forall_forall; intros lidx ?.
                destruct (idx_dec lidx oidx); subst.
                { disc_rule_conds_ex.
                  split; auto.
                  apply DirMsgsCoh_other_midx_enqMP;
                    [|intro Hx; dest_in; try discriminate;
                      inv H12; eapply l1ExtOf_not_eq; eauto].
                  apply DirMsgsCoh_deqMP.
                  assumption.
                }
                { apply in_app_or in H9; destruct H9.
                  { rewrite Forall_forall in H4; specialize (H4 _ H9).
                    disc_rule_conds_ex.
                    split; auto.
                    apply DirMsgsCoh_other_msg_id_enqMP;
                      [|intro Hx; dest_in; try discriminate].
                    apply DirMsgsCoh_deqMP.
                    assumption.
                  }
                  { specialize (H5 _ H9).
                    disc_rule_conds_ex.
                    split; auto.
                    apply DirMsgsCoh_other_msg_id_enqMP;
                      [|intro Hx; dest_in; try discriminate].
                    apply DirMsgsCoh_deqMP.
                    assumption.
                  }
                }
              }
            }
          * solve_sim_ext_mp.

        + (* [l1GetSRqUpUp] *)
          disc_rule_conds_ex.
          spec_case_silent.

          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl; split.
              { solve_rule_conds_ex. }
              { apply Forall_forall; intros lidx ?.
                destruct (idx_dec lidx oidx); subst.
                { disc_rule_conds_ex.
                  split; auto.
                  apply DirMsgsCoh_other_msg_id_enqMP;
                    [|intro Hx; dest_in; try discriminate].
                  apply DirMsgsCoh_deqMP.
                  assumption.
                }
                { apply in_app_or in H9; destruct H9.
                  { rewrite Forall_forall in H4; specialize (H4 _ H9).
                    disc_rule_conds_ex.
                    split; auto.
                    apply DirMsgsCoh_other_msg_id_enqMP;
                      [|intro Hx; dest_in; try discriminate].
                    apply DirMsgsCoh_deqMP.
                    assumption.
                  }
                  { specialize (H5 _ H9).
                    disc_rule_conds_ex.
                    split; auto.
                    apply DirMsgsCoh_other_msg_id_enqMP;
                      [|intro Hx; dest_in; try discriminate].
                    apply DirMsgsCoh_deqMP.
                    assumption.
                  }
                }
              }
            }
          * solve_sim_ext_mp.

    Admitted.
    
    Theorem Mesi_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement with (ginv:= ImplInvEx) (sim:= SimMESI).
      - apply simMesi_sim.
      - red; unfold ImplInvEx; intros.
        dest; split.
      - apply simMesi_init.
      - split.
    Qed.

  End Facts.
  
End Sim.

