Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo Ex.Mesi.MesiInv.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Ltac solve_mesi :=
  unfold mesiM, mesiE, mesiS, mesiI in *; lia.

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

Section TreeTopoChns.
  Context `{OStateIfc}.
  Variables (sys: System)
            (msgs: MessagePool Msg).

  Definition NoTwoMsgsInQ :=
    forall idm1 idm2,
      InMPI msgs idm1 -> InMPI msgs idm2 ->
      idOf idm1 = idOf idm2 ->
      (valOf idm1).(msg_id) <> (valOf idm2).(msg_id) -> False.

  Definition NoRqUpRsDown (oidx: IdxT) :=
    forall rqu rsd,
      InMPI msgs rqu -> InMPI msgs rsd ->
      fst (sigOf rqu) = rqUpFrom oidx ->
      fst (sigOf rsd) = downTo oidx -> fst (snd (sigOf rsd)) = MRs ->
      False.

  (* Definition TreeTopoChnsLocked := *)
  (*   forall oidx, NoRqUpRsDown oidx. *)

  (* Definition  *)
      
  (*     List.length (findQ (downTo *)
      
    

End TreeTopoChns.

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

  Lemma SimExtMP_impl_silent_locked:
    forall imsgs (orqs: ORqs Msg) smsgs,
      SimExtMP imsgs orqs smsgs ->
      forall oidx porq norq,
        orqs@[oidx] = Some porq -> porq@[upRq] = None ->
        (norq@[upRq] >>= (fun rqiu => rqiu.(rqi_msg)) = None) ->
        SimExtMP imsgs (orqs +[oidx <- norq]) smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split; assumption.
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

  Section ObjCoh.
    Variables (cv: nat)
              (cidx: IdxT)
              (cost: OState)
              (msgs: MessagePool Msg).

    Definition cohMsgs: list (MSig * (Id Msg -> Prop)) :=
      (| (downTo cidx, (MRs, mesiRsS)): fun idm => (valOf idm).(msg_value) = cv
       | (downTo cidx, (MRs, mesiRsE)): fun idm => (valOf idm).(msg_value) = cv
       | (rsUpFrom cidx, (MRs, mesiDownRsS)): fun idm => (valOf idm).(msg_value) = cv
       | (rqUpFrom cidx, (MRq, mesiRqI)):
           fun idm => (cost#[implStatusIdx] = mesiM -> (valOf idm).(msg_value) = cv))%cases.

    Definition MsgCoh := MsgP cohMsgs.
    Definition MsgsCoh := MsgsP cohMsgs msgs.

    Definition ObjCoh :=
      ImplOStateMESI cidx cost msgs cv /\ MsgsCoh.

  End ObjCoh.

  Section ObjCohFacts.

    Lemma ObjInvalid_ObjCoh:
      forall oidx ost msgs,
        ObjInvalid oidx ost msgs ->
        forall cv, ObjCoh cv oidx ost msgs.
    Proof.
      unfold ObjInvalid, ObjCoh; intros.
      destruct H.
      - red in H; dest; split.
        + red; intros; rewrite H in H1; solve_mesi.
        + do 2 red; intros.
          specialize (H0 _ H1); red in H0.
          red; unfold cohMsgs, map, caseDec, fst in *.
          repeat (find_if_inside; [exfalso; auto; fail|]).
          find_if_inside; [|auto].
          simpl in *; intros; rewrite H2 in H; discriminate.
      - split.
        + red; intros.
          exfalso; eapply NoRsI_MsgExistsSig_false; eauto.
        + destruct H as [idm [? ?]].
          red; intros.

          red; intros.
          red; unfold cohMsgs, map, caseDec, fst.
          find_if_inside.
          
          (** TODO: build a good automation that can deduce
           * {rsD/rsD, rqU/rsD, rsU/rsD} cases are not possible. *)
          admit. 
    Admitted.

    Lemma ObjExcl_ObjCoh:
      forall oidx ost msgs,
        InvObjExcl0 oidx ost msgs ->
        ObjExcl oidx ost msgs ->
        ObjCoh ost#[implValueIdx] oidx ost msgs.
    Proof.
      unfold InvObjExcl0, ObjExcl, ObjCoh; intros.
      destruct H0 as [|[|]]; [|clear H|clear H].
      - specialize (H H0); dest.
        split; [red; intros; reflexivity|].
        do 2 red; intros.
        specialize (H _ H2); red in H.
        red; unfold cohMsgs, map, caseDec, fst in *.
        repeat (find_if_inside; [exfalso; auto; fail|]).
        find_if_inside; [|auto].
        simpl in *; intros; specialize (H1 H3 _ H2 e); assumption.
      - split; [red; intros; reflexivity|].
        destruct H0 as [idm [? ?]].
        red; intros.
        (** TODO: build a good automation that can deduce
         * {rsD/rsD, rqU/rsD, rsU/rsD} cases are not possible. *)
        admit.
      - split; [red; intros; reflexivity|].
        destruct H0 as [idm [? ?]].
        red; intros.
        (** TODO: build a good automation that can deduce
         * {rsD/rsD, rqU/rsD, rsU/rsD} cases are not possible. *)
        admit.
    Admitted.

    Lemma MsgsCoh_enqMP:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall midx msg,
          MsgCoh cv cidx cost (midx, msg) ->
          MsgsCoh cv cidx cost (enqMP midx msg msgs).
    Proof.
      intros; apply MsgsP_enqMP; auto.
    Qed.

    Lemma MsgsCoh_put_invalid_enqMP:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall midx msg,
          msg_id msg = mesiRqI ->
          cost#[implStatusIdx] < mesiM ->
          MsgsCoh cv cidx cost (enqMP midx msg msgs).
    Proof.
      intros; apply MsgsP_enqMP; auto.
      red; cbv [sigOf idOf valOf fst snd].
      rewrite H0.
      unfold caseDec, map, cohMsgs.
      repeat (find_if_inside; [inv e; exfalso; intuition idtac; fail|]).
      find_if_inside; [|auto].
      intros; simpl in *; rewrite H2 in H1; lia.
    Qed.

    Lemma MsgsCoh_other_midx_enqMP:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall midx msg,
          ~ In midx [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          MsgsCoh cv cidx cost (enqMP midx msg msgs).
    Proof.
      intros.
      apply MsgsP_other_midx_enqMP; auto.
      intro Hx; elim H0; dest_in; simpl; tauto.
    Qed.

    Lemma MsgsCoh_other_midx_enqMsgs:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall eins,
          DisjList (idsOf eins) [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          MsgsCoh cv cidx cost (enqMsgs eins msgs).
    Proof.
      intros.
      apply MsgsP_other_midx_enqMsgs; auto.
      simpl.
      eapply DisjList_comm, DisjList_SubList;
        [|apply DisjList_comm; eassumption].
      solve_SubList.
    Qed.

    Lemma MsgsCoh_other_msg_id_enqMP:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall midx msg,
          ~ In (msg_id msg) [mesiRsS; mesiRsE; mesiDownRsS; mesiRqI] ->
          MsgsCoh cv cidx cost (enqMP midx msg msgs).
    Proof.
      intros; apply MsgsP_other_msg_id_enqMP; auto.
    Qed.

    Lemma MsgsCoh_other_msg_id_enqMsgs:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall eins,
          DisjList (map (fun idm => msg_id (valOf idm)) eins)
                   [mesiRsS; mesiRsE; mesiDownRsS; mesiRqI] ->
          MsgsCoh cv cidx cost (enqMsgs eins msgs).
    Proof.
      intros; apply MsgsP_other_msg_id_enqMsgs; auto.
    Qed.

    Lemma MsgsCoh_deqMP:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall midx,
          MsgsCoh cv cidx cost (deqMP midx msgs).
    Proof.
      intros; apply MsgsP_deqMP; auto.
    Qed.

    Lemma MsgsCoh_deqMsgs:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall minds,
          MsgsCoh cv cidx cost (deqMsgs minds msgs).
    Proof.
      intros; apply MsgsP_deqMsgs; auto.
    Qed.

    Lemma MsgsCoh_state_update_indep:
      forall cv cidx cost msgs,
        MsgsCoh cv cidx cost msgs ->
        forall nost: OState,
          nost#[implStatusIdx] <> mesiM ->
          MsgsCoh cv cidx nost msgs.
    Proof.
      unfold MsgsCoh, MsgsP; intros.
      specialize (H _ H1).
      red in H; red; unfold map, cohMsgs, caseDec, fst in *.
      repeat (find_if_inside; [assumption|]).
      find_if_inside; [|auto].
      simpl in *; intros; exfalso; auto.
    Qed.

  End ObjCohFacts.

  Definition ImplStateCoh (cv: nat) (st: MState): Prop :=
    (most <-- (bst_oss st)@[rootOf topo];
       ImplOStateMESI (rootOf topo) most (bst_msgs st) cv) /\
    Forall (fun oidx => ost <-- (bst_oss st)@[oidx]; ObjCoh cv oidx ost (bst_msgs st))
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

  Hint Unfold ObjCoh ImplStateCoh: RuleConds.

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
            do 3 red; intros.
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
        split; simpl.
        { disc_rule_conds_ex.
          apply H; eapply MsgsP_enqMsgs_inv; eauto.
        }
        { apply Forall_forall; intros oidx ?.
          rewrite Forall_forall in H4; specialize (H4 _ H5).
          disc_rule_conds_ex.
          split.
          { intros; apply H4; auto.
            eapply MsgsP_enqMsgs_inv; eauto.
          }              
          { apply MsgsCoh_other_midx_enqMsgs; [assumption|].
            destruct H1; simpl in H1.
            eapply DisjList_SubList; [eassumption|].
            apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
            { apply tree2Topo_obj_chns_minds_SubList.
              apply in_or_app.
              apply in_app_or in H5; destruct H5; auto.
              apply tl_In in H5; auto.
            }
            { apply tree2Topo_minds_merqs_disj. }
          }
        }
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
    exists (RlblOuts eouts); eexists.
    repeat ssplit.
    - reflexivity.
    - rewrite c_merss_l1_downTo in H2.
      eapply SmOuts with (msgs0:= smsgs1); eauto.
      + eapply SimExtMP_ext_outs_FirstMPI; eauto.
      + split; assumption.
    - split.
      + inv H.
        apply SimStateIntro with (cv:= cv); [assumption|].
        red in H6; simpl in H6; dest.
        split; simpl.
        * disc_rule_conds_ex.
          apply H.
          eapply MsgsP_other_midx_deqMsgs_inv; [eassumption|].
          simpl.
          apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
          { eapply SubList_trans.
            2: {
              apply tree2Topo_obj_chns_minds_SubList.
              rewrite c_li_indices_head_rootOf by assumption.
              left; reflexivity.
            }
            solve_SubList.
          }
          { eapply DisjList_comm, DisjList_SubList; [eassumption|].
            apply DisjList_comm, tree2Topo_minds_merss_disj.
          }
        * apply Forall_forall; intros oidx ?.
          rewrite Forall_forall in H6; specialize (H6 _ H7).
          disc_rule_conds_ex.
          split.
          { intros; apply H6; auto.
            eapply MsgsP_other_midx_deqMsgs_inv; [eassumption|].
            simpl.
            apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
            { eapply SubList_trans.
              2: {
                apply tree2Topo_obj_chns_minds_SubList.
                rewrite c_li_indices_head_rootOf by assumption.
                right; eassumption.
              }
              solve_SubList.
            }
            { eapply DisjList_comm, DisjList_SubList; [eassumption|].
              apply DisjList_comm, tree2Topo_minds_merss_disj.
            }
          }
          { apply MsgsCoh_deqMsgs; assumption. }
      + rewrite c_merss_l1_downTo in H2.
        apply SimExtMP_ext_outs_deqMsgs; auto.
  Qed.

  Definition ImplInvEx (st: MState) :=
    InvExcl st.

  Hint Unfold ImplInvEx: RuleConds.

  Ltac disc_MsgsCoh_by_FirstMP Hd Hf :=
    specialize (Hd _ (FirstMP_InMP Hf));
    red in Hd;
    cbv [map cohMsgs] in Hd;
    cbv [sigOf idOf valOf fst snd] in Hd;
    match type of Hf with
    | FirstMPI _ (_, ?msg) =>
      match goal with
      | [H1: msg_id ?msg = _, H2: msg_type ?msg = _ |- _] =>
        rewrite H1, H2 in Hd
      end
    end;
    disc_caseDec Hd.

  Ltac spec_constr_step_FirstMPI :=
    repeat constructor;
    repeat
      match goal with
      | [H: SimExtMP _ _ _ _ |- _] => red in H
      | [Hf: Forall _ ?l, Hin: In _ ?l |- _] =>
        rewrite Forall_forall in Hf; specialize (Hf _ Hin);
        disc_rule_conds_const; dest

      | [H: _ :: findQ ?eidx _ = findQ ?eidx ?msgs |-
         FirstMPI ?msgs (?eidx, _) ] =>
        unfold FirstMPI, FirstMP, firstMP;
        simpl; rewrite <-H; reflexivity
      | [H: findQ ?eidx _ = findQ ?eidx ?msgs |-
         FirstMPI ?msgs (?eidx, _) ] =>
        eapply findQ_eq_FirstMPI; eauto; fail
      end.

  Ltac spec_constr_step_ValidMsgs :=
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
    |spec_constr_step_FirstMPI
    |spec_constr_step_ValidMsgs
    |solve_rule_conds_ex;
     match goal with
     | [H: msg_id ?msg = _ |- context[msg_id ?msg] ] => rewrite H
     end; reflexivity
    |spec_constr_step_ValidMsgs
    |solve_DisjList idx_dec].

  Ltac spec_constr_step_set cidx :=
    eapply SmInt with (ins:= [(rqUpFrom (l1ExtOf cidx), _)]);
    try reflexivity;
    [left; reflexivity
    |simpl; apply specSetRq_in_specRules, in_map; assumption
    |reflexivity
    |eassumption
    |eassumption
    |spec_constr_step_FirstMPI
    |spec_constr_step_ValidMsgs
    |solve_rule_conds_ex;
     match goal with
     | [H: msg_id ?msg = _ |- context[msg_id ?msg] ] => rewrite H
     end; reflexivity
    |spec_constr_step_ValidMsgs
    |solve_DisjList idx_dec].

  Ltac spec_case_get cidx :=
    eexists (RlblInt specIdx (rule_idx (specGetRq (l1ExtOf cidx))) _ _);
    eexists;
    repeat ssplit;
    [reflexivity|spec_constr_step_get cidx|].

  Ltac spec_case_set cidx :=
    eexists (RlblInt specIdx (rule_idx (specSetRq (l1ExtOf cidx))) _ _);
    eexists;
    repeat ssplit;
    [reflexivity|spec_constr_step_set cidx|].
  
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
         [|apply Forall_forall; intros; mred; fail]
       | [ |- SimExtMP _ _ (_ +[_ <- addRqS _ _ _]) _] =>
         eapply SimExtMP_impl_silent_locked;
         [|eassumption|eassumption|unfold addRqS; mred]
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

  (*! To solve [SimMESI] *)

  Ltac single_goal_left :=
    let n := numgoals in guard n = 1.

  Ltac solve_ImplStateCoh_mem :=
    idtac.

  Ltac solve_ImplStateCoh_li :=
    idtac.

  Ltac case_ImplStateCoh_mem_li :=
    red; simpl; split.
  
  Ltac solve_ImplStateCoh :=
    case_ImplStateCoh_mem_li;
    [solve_ImplStateCoh_mem|solve_ImplStateCoh_li].
  
  Ltac solve_SpecStateCoh :=
    eapply SimStateIntro; [solve_rule_conds_ex|].
  
  Ltac solve_sim_mesi_ext_mp :=
    red; simpl; split; [|solve_sim_ext_mp].

  Ltac solve_sim_mesi :=
    solve_sim_mesi_ext_mp;
    single_goal_left;
    solve_SpecStateCoh;
    single_goal_left;
    solve_ImplStateCoh.

  Ltac solve_ImplStateCoh_idx_not_in :=
    intro; dest_in; try discriminate;
    repeat
      match goal with
      | [H: rqUpFrom _ = rqUpFrom _ |- _] => inv H
      | [H: rsUpFrom _ = rsUpFrom _ |- _] => inv H
      | [H: downTo _ = downTo _ |- _] => inv H
      | [H: ?oidx = l1ExtOf ?oidx |- _] =>
        exfalso; eapply l1ExtOf_not_eq; eauto
      end.

  Ltac disc_MsgsP H :=
    repeat
      (first [apply MsgsP_enqMP_inv in H
             |apply MsgsP_other_midx_deqMP_inv in H; [|solve_not_in]
             |eapply MsgsP_other_msg_id_deqMP_inv in H;
              [|eassumption
               |unfold valOf, snd;
                match goal with
                | [Hi: msg_id ?rmsg = _, Hf: FirstMPI _ (_, ?rmsg) |- _] =>
                  rewrite Hi; solve_not_in
                end]
      ]).

  Ltac solve_ImplOStateMESI :=
    intros; auto; (* can be solved automatically? *)
    match goal with
    | [H: _ -> ?P |- ?P] => apply H; auto
    | [H: _ -> _ -> ?P |- ?P] => apply H; auto
    end;
    match goal with
    | [H: MsgsP ?P _ |- MsgsP ?P _] => disc_MsgsP H
    end;
    try assumption.

  Ltac solve_MsgsCoh :=
    repeat
      (try match goal with
           | |- MsgsCoh _ _ _ (enqMP _ _ _) =>
             apply MsgsCoh_other_midx_enqMP;
             [|solve_ImplStateCoh_idx_not_in; auto; fail]
           | |- MsgsCoh _ _ _ (enqMP _ _ _) =>
             apply MsgsCoh_other_msg_id_enqMP;
             [|intro; dest_in; discriminate]
           | |- MsgsCoh _ _ _ (enqMP _ _ _) =>
             apply MsgsCoh_enqMP;
             [|do 2 red; cbv [map cohMsgs]; solve_caseDec; reflexivity]
           | |- MsgsCoh _ _ _ (enqMP _ {| msg_id := mesiRqI |} _) =>
             apply MsgsCoh_put_invalid_enqMP; [|reflexivity|assumption]
           | |- MsgsCoh _ _ _ (deqMP _ _) =>
             apply MsgsCoh_deqMP
           | |- MsgsCoh _ _ (_, (?stt, _)) _ =>
             eapply MsgsCoh_state_update_indep; [|discriminate]
           end; try eassumption).
  
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
      Ltac solve_ImplStateCoh_mem ::=
        disc_rule_conds_ex; solve_ImplOStateMESI.

      Ltac solve_ImplStateCoh_li_me :=
        disc_rule_conds_ex;
        split; [solve_ImplOStateMESI|];
        solve_MsgsCoh.

      Ltac solve_ImplStateCoh_li_others :=
        try match goal with
            | [H: MsgsCoh _ ?oidx _ _, Hin: In ?odx _ |- Forall _ _] => clear Hin
            end;
        repeat
          match goal with
          | [H: In _ (_ ++ _) |- _] => apply in_app_or in H; destruct H
          | [Hf: Forall _ ?l, He: In _ ?l |- _] =>
            rewrite Forall_forall in Hf;
            specialize (Hf _ He); disc_rule_conds_ex
          | [Hf: forall _, In _ ?l -> _, He: In _ ?l |- _] =>
            specialize (Hf _ He); disc_rule_conds_ex
          end;
        match goal with
        | |- _ /\ _ => split; [solve_ImplOStateMESI|]; solve_MsgsCoh
        end.

      Ltac case_ImplStateCoh_li_me_others :=
        match goal with
        | [H: MsgsCoh _ ?oidx _ _ |- Forall _ _] =>
          let lidx := fresh "lidx" in
          apply Forall_forall;
          intros lidx ?; destruct (idx_dec lidx oidx); subst
        end.
          
      Ltac solve_ImplStateCoh_li ::=
        case_ImplStateCoh_li_me_others;
        [solve_ImplStateCoh_li_me|solve_ImplStateCoh_li_others].
      
      apply in_map_iff in H4; destruct H4 as [oidx [? ?]]; subst.
      dest_in.

      + (* [l1GetSImm] *)
        disc_rule_conds_ex.
        spec_case_get oidx.

        (** TODO: automate; "UpRq None" -> .. *)
        assert (NoRsI oidx msgs) by admit.
        disc_rule_conds_ex.

        solve_sim_mesi.

      + (* [l1GetSRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (** TODO: automate; "UpRq None" -> .. *)
        assert (NoRsI oidx msgs) by admit.
        disc_rule_conds_ex.
        
        solve_sim_mesi.

      + (* [l1GetSRsDownDownS] *)
        disc_rule_conds_ex.
        spec_case_get oidx.

        (** TODO: automate below various dischargers *)
        progress (good_footprint_get oidx).
        repeat (repeat disc_rule_conds_unit_simpl; try disc_footprints_ok).
        pose proof (edgeDownTo_Some (mesi_RqRsDTree Htr) _ H26).
        destruct H29 as [rqUp [rsUp [pidx ?]]]; dest.
        pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
        pose proof (Htn _ _ H11); dest.
        pose proof (Htn _ _ H31); dest.
        apply tree2Topo_l1_child_ext in H11; [|assumption]; subst.
        disc_rule_conds_const.
        assert (msg_value rmsg = fst sost)
          by (disc_MsgsCoh_by_FirstMP H22 H23; assumption).
        rewrite H11 in *.

        (** TODO: automate this as well *)
        assert (oidx <> rootOf topo) as Honr.
        { intro Hx; subst.
          pose proof (tree2Topo_WfCIfc tr 0) as [? _].
          apply (DisjList_NoDup idx_dec) in H29.
          eapply DisjList_In_1 in H29; [|eassumption].
          elim H29; rewrite c_li_indices_head_rootOf by assumption.
          left; reflexivity.
        }

        solve_sim_mesi.

      + (* [l1GetSRsDownDownE] *)
        disc_rule_conds_ex.
        spec_case_get oidx.

        (** TODO: automate below various dischargers *)
        progress (good_footprint_get oidx).
        repeat (repeat disc_rule_conds_unit_simpl; try disc_footprints_ok).
        pose proof (edgeDownTo_Some (mesi_RqRsDTree Htr) _ H26).
        destruct H29 as [rqUp [rsUp [pidx ?]]]; dest.
        pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
        pose proof (Htn _ _ H11); dest.
        pose proof (Htn _ _ H31); dest.
        apply tree2Topo_l1_child_ext in H11; [|assumption]; subst.
        disc_rule_conds_const.
        assert (msg_value rmsg = fst sost)
          by (disc_MsgsCoh_by_FirstMP H22 H23; assumption).
        rewrite H11 in *.

        (** TODO: automate this as well *)
        assert (oidx <> rootOf topo) as Honr.
        { intro Hx; subst.
          pose proof (tree2Topo_WfCIfc tr 0) as [? _].
          apply (DisjList_NoDup idx_dec) in H29.
          eapply DisjList_In_1 in H29; [|eassumption].
          elim H29; rewrite c_li_indices_head_rootOf by assumption.
          left; reflexivity.
        }

        solve_sim_mesi.

      + (* [downSImm] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (** TODO: automate; rsD/rqD not possible *)
        assert (NoRsI oidx msgs) by admit.
        disc_rule_conds_ex.

        solve_sim_mesi.

      + (* [l1GetMImmE] *)
        disc_rule_conds_ex.
        spec_case_set oidx.

        (** TODO: automate; "UpRq None" -> .. *)
        assert (NoRsI oidx msgs) by admit.
        disc_rule_conds_ex.

        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_mem_li.
        * (* mem *)
          disc_rule_conds_ex.
          exfalso.
          disc_MsgsP H16.
          eapply InvExcl_excl_invalid_status
            with (eidx:= oidx) (oidx:= rootOf topo) in H1;
            simpl in *; eauto; solve_mesi.

        * (* li *)
          case_ImplStateCoh_li_me_others.
          { mred; simpl.
            apply ObjExcl_ObjCoh.
            { specialize (H3 oidx); repeat (simpl in H3; mred); dest.
              assumption.
            }
            { left; split.
              { simpl; solve_mesi. }
              { do 2 red; simpl.
                apply MsgsP_other_midx_enqMP;
                  [|intro; dest_in;
                    inv H17; eapply l1ExtOf_not_eq; eauto].
                apply MsgsP_deqMP.
                assumption.
              }
            }
          }
          { clear H6. (* In oidx .. *)
            mred; simpl.
            assert (exists lost, oss@[lidx] = Some lost).
            { apply in_app_or in H12; destruct H12.
              { rewrite Forall_forall in H4; specialize (H4 _ H6).
                solve_rule_conds_ex.
              }
              { specialize (H5 _ H6); solve_rule_conds_ex. }
            }
            destruct H6 as [lost ?]; rewrite H6; simpl.
            apply ObjInvalid_ObjCoh.
            eapply InvExcl_excl_invalid; [eapply H3|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.

            do 2 red.
            apply MsgsP_other_midx_enqMP;
              [|intro; dest_in;
                inv H17; eapply l1ExtOf_not_eq; eauto].
            apply MsgsP_deqMP.
            assumption.
          }
          
      + (* [l1GetMImmM] *)
        disc_rule_conds_ex.
        spec_case_set oidx.

        (** TODO: automate; "UpRq None" -> .. *)
        assert (NoRsI oidx msgs) by admit.
        disc_rule_conds_ex.
        
        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_mem_li.
        * (* mem *)
          disc_rule_conds_ex.
          exfalso.
          disc_MsgsP H16.
          eapply InvExcl_excl_invalid_status
            with (eidx:= oidx) (oidx:= rootOf topo) in H1;
            simpl in *; eauto; solve_mesi.

        * (* li *)
          case_ImplStateCoh_li_me_others.
          { mred; simpl.
            apply ObjExcl_ObjCoh.
            { specialize (H3 oidx); repeat (simpl in H3; mred); dest.
              assumption.
            }
            { left; split.
              { simpl; solve_mesi. }
              { do 2 red; simpl.
                apply MsgsP_other_midx_enqMP;
                  [|intro; dest_in;
                    inv H17; eapply l1ExtOf_not_eq; eauto].
                apply MsgsP_deqMP.
                assumption.
              }
            }
          }
          { clear H6. (* In oidx .. *)
            mred; simpl.
            assert (exists lost, oss@[lidx] = Some lost).
            { apply in_app_or in H12; destruct H12.
              { rewrite Forall_forall in H4; specialize (H4 _ H6).
                solve_rule_conds_ex.
              }
              { specialize (H5 _ H6); solve_rule_conds_ex. }
            }
            destruct H6 as [lost ?]; rewrite H6; simpl.
            apply ObjInvalid_ObjCoh.
            eapply InvExcl_excl_invalid; [eapply H3|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.

            do 2 red.
            apply MsgsP_other_midx_enqMP;
              [|intro; dest_in;
                inv H17; eapply l1ExtOf_not_eq; eauto].
            apply MsgsP_deqMP.
            assumption.
          }

      + (* [l1GetMRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        solve_sim_mesi.

      + (* [l1GetMRsDownDown] *)
        disc_rule_conds_ex.
        spec_case_set oidx.

        (** TODO: automate below various dischargers *)
        progress (good_footprint_get oidx).
        repeat (repeat disc_rule_conds_unit_simpl; try disc_footprints_ok).
        pose proof (edgeDownTo_Some (mesi_RqRsDTree Htr) _ H26).
        destruct H29 as [rqUp [rsUp [pidx ?]]]; dest.
        pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
        pose proof (Htn _ _ H11); dest.
        pose proof (Htn _ _ H31); dest.
        apply tree2Topo_l1_child_ext in H11; [|assumption]; subst.
        disc_rule_conds_const.

        (** TODO: automate this as well *)
        assert (oidx <> rootOf topo) as Honr.
        { intro Hx; subst.
          pose proof (tree2Topo_WfCIfc tr 0) as [? _].
          apply (DisjList_NoDup idx_dec) in H11.
          eapply DisjList_In_1 in H11; [|eassumption].
          elim H11; rewrite c_li_indices_head_rootOf by assumption.
          left; reflexivity.
        }

        (** TODO: automate; rsD/rsD not possible *)
        assert (NoRsI oidx msgs) by admit.
        disc_rule_conds_ex.

        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_mem_li.
        * (* mem *)
          disc_rule_conds_ex.
          exfalso.
          eapply InvExcl_excl_invalid_status
            with (eidx:= oidx) (oidx:= rootOf topo) in H3;
            simpl in *; eauto; try mred; try solve_mesi.
          { do 2 red.
            apply MsgsP_other_midx_enqMP;
              [|intro; dest_in;
                inv H35; eapply l1ExtOf_not_eq; eauto].
            apply MsgsP_deqMP.
            assumption.
          }
          { simpl; solve_mesi. }
          
        * (* li *)
          case_ImplStateCoh_li_me_others.
          { mred; simpl.
            apply ObjExcl_ObjCoh.
            { specialize (H3 oidx); repeat (simpl in H3; mred); dest.
              assumption.
            }
            { left; split.
              { simpl; solve_mesi. }
              { do 2 red; simpl.
                apply MsgsP_other_midx_enqMP;
                  [|intro; dest_in;
                    inv H34; eapply l1ExtOf_not_eq; eauto].
                apply MsgsP_deqMP.
                assumption.
              }
            }
          }
          { clear H6. (* In oidx .. *)
            mred; simpl.
            assert (exists lost, oss@[lidx] = Some lost).
            { apply in_app_or in H29; destruct H29.
              { rewrite Forall_forall in H4; specialize (H4 _ H6).
                solve_rule_conds_ex.
              }
              { specialize (H5 _ H6); solve_rule_conds_ex. }
            }
            destruct H6 as [lost ?]; rewrite H6; simpl.
            apply ObjInvalid_ObjCoh.
            eapply InvExcl_excl_invalid; [eapply H3|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.

            do 2 red.
            apply MsgsP_other_midx_enqMP;
              [|intro; dest_in;
                inv H34; eapply l1ExtOf_not_eq; eauto].
            apply MsgsP_deqMP.
            assumption.
          }
          
      + (* [l1DownIImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        solve_sim_mesi.
        
      + (* [putRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        solve_sim_mesi.
        
      + (* [putRqUpUpM] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (** TODO: automate; "UpRq None" -> .. *)
        assert (MsgsP [(downTo oidx, (MRs, mesiRsI), fun _ => False)] msgs).
        { admit. }
        disc_rule_conds_ex.

        solve_sim_mesi.

        apply MsgsCoh_enqMP; [assumption|].
        do 2 red; cbv [map cohMsgs]; solve_caseDec.
        intros; apply H15; auto.
        solve_mesi.
        
  Admitted.
  
  Theorem Mesi_ok:
    (steps step_m) # (steps step_m) |-- impl ⊑ spec.
  Proof.
    apply invSim_implies_refinement with (ginv:= ImplInvEx) (sim:= SimMESI).
    - apply simMesi_sim.
    - admit.
    - apply simMesi_init.
    - admit.
  Admitted.

End Sim.

