Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecSv Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** TODO: to [MessagePool.v] *)
Lemma findQ_deqMsgs_eq:
  forall {MsgT} minds midx (msgs1 msgs2: MessagePool MsgT),
    findQ midx msgs1 = findQ midx msgs2 ->
    findQ midx (deqMsgs minds msgs1) =
    findQ midx (deqMsgs minds msgs2).
Proof.
  induction minds; simpl; intros; auto.
  apply IHminds.
  destruct (idx_dec midx a); subst.
  - unfold deqMP; rewrite H.
    destruct (findQ a msgs2) eqn:Hf; [congruence|].
    unfold findQ; mred.
  - do 2 (rewrite findQ_not_In_deqMP by assumption).
    assumption.
Qed.

(** TODO: will be used by MOSI as well. *)
Section SimExtMP.
  Variable (l1s: list IdxT).

  Local Notation erqs :=
    (map (fun cidx => rqUpFrom (l1ExtOf cidx)) l1s).
  Local Notation erss :=
    (map (fun cidx => downTo (l1ExtOf cidx)) l1s).

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

  Local Definition topo := fst (tree2Topo tr 0).
  Local Definition cifc := snd (tree2Topo tr 0).
  Local Definition impl := Mesi.impl Htr.
  Local Definition spec := SpecSv.spec (List.length (c_l1_indices cifc)).

  Existing Instance Mesi.ImplOStateIfc.

  (** NOTE: simulation only states about coherent values. 
   * Exclusiveness is stated and proven as an invariant. *)

  Definition ImplOStateMESI (cv: nat) (ost: OState): Prop :=
    mesiS <= ost#[implStatusIdx] -> ost#[implValueIdx] = cv.

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
    Admitted.

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
        admit.
      + split.
        * admit.
        * apply SimExtMP_enqMsgs; auto.
          apply H1.
    Admitted.

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
      destruct H2.
      unfold impl in H2; simpl in H2.
      unfold Mesi.cifc in H2.
      rewrite c_merss_l1_downTo in H2.
      exists (RlblOuts eouts); eexists.
      repeat ssplit.
      + reflexivity.
      + eapply SmOuts with (msgs0:= smsgs1); eauto.
        eapply SimExtMP_ext_outs_FirstMPI; eauto.
        admit.
      + split.
        * admit.
        * apply SimExtMP_ext_outs_deqMsgs; auto.
    Admitted.

    Definition ImplInvEx (st: MState) :=
      True. (* ImplInv st /\ ImplInvB st. *)

    Hint Unfold ImplInvEx (* ImplInv ImplInvB *): RuleConds.

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
      (* inv H0. *) (** discharge [SimState] *)

      move H4 at bottom.
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

        all: admit.
      
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

