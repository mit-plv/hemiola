Require Import Bool List String Peano_dec.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.
Require Import Ex.Mesi.MesiInvOk.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Lemma InvExcl_excl_invalid:
  forall st (He: InvExcl st) msgs eidx eost,
    bst_msgs st = msgs ->
    (bst_oss st)@[eidx] = Some eost ->
    NoRsI eidx msgs ->
    mesiE <= eost#[status] ->
    forall oidx ost,
      oidx <> eidx ->
      (bst_oss st)@[oidx] = Some ost ->
      ObjInvalid oidx ost msgs.
Proof.
  intros; subst.
  specialize (He eidx).
  disc_rule_conds_ex.
  red in He.
  unfold ObjExcl0 in He; simpl in He.
  specialize (He (conj H2 H1)); dest.
  specialize (H _ H3).
  rewrite H4 in H; auto.
Qed.

Section Sim.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).
  Let impl := Mesi.impl Htr.

  Local Definition spec :=
    @SpecInds.spec (c_l1_indices cifc) (tree2Topo_l1_NoPrefix tr 0).

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
       | (rsUpFrom cidx, (MRs, mesiDownRsS)): fun idm => (valOf idm).(msg_value) = cv)%cases.

    Definition MsgCoh := MsgP cohMsgs.
    Definition MsgsCoh := MsgsP cohMsgs msgs.

    Definition ObjCoh :=
      ImplOStateMESI cidx cost msgs cv /\ MsgsCoh.

  End ObjCoh.

  Section ObjCohFacts.

    Lemma ObjInvalid_ObjCoh:
      forall oidx orq ost msgs
             (Hrsi: RsDownConflicts oidx orq msgs)
             (Hwd: ObjWBDir oidx ost msgs),
        ObjInvalid oidx ost msgs ->
        forall cv, ObjCoh cv oidx ost msgs.
    Proof.
      unfold ObjInvalid, ObjCoh; intros.
      destruct H.
      - red in H; dest; repeat ssplit.
        + red; intros; rewrite H in H2; solve_mesi.
        + do 2 red; intros.
          specialize (H1 _ H2); red in H1.
          red; unfold cohMsgs, map, caseDec, fst in *.
          repeat (find_if_inside; [exfalso; auto; fail|]).
          auto.

      - repeat ssplit.
        + red; intros.
          exfalso; eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
        + destruct H as [idm [? ?]].
          red; intros.
          specialize (Hrsi idm ltac:(rewrite H0; reflexivity)
                                      ltac:(rewrite H0; reflexivity) H); dest.
          red; intros.
          red; unfold cohMsgs, map, caseDec, fst.
          repeat find_if_inside; [..|auto].
          * exfalso; eapply (H3 idm0); try rewrite H0; try rewrite e; auto.
            destruct idm as [midx msg], idm0 as [midx0 msg0].
            simpl in *; inv H0; inv e.
            intro; subst; rewrite H10 in H11; discriminate.
          * exfalso; eapply (H3 idm0); try rewrite H0; try rewrite e; auto.
            destruct idm as [midx msg], idm0 as [midx0 msg0].
            simpl in *; inv H0; inv e.
            intro; subst; rewrite H10 in H11; discriminate.
          * exfalso; eapply H5; try rewrite e; eauto.
    Qed.

    Lemma NoCohMsgs_MsgsCoh:
      forall oidx msgs,
        NoCohMsgs oidx msgs ->
        forall cv, MsgsCoh cv oidx msgs.
    Proof.
      intros.
      do 2 red; intros.
      specialize (H _ H0); red in H.
      red; unfold cohMsgs, map, caseDec, fst in *.
      repeat (find_if_inside; [exfalso; auto; fail|]).
      auto.
    Qed.

    Lemma ObjExcl0_ObjCoh:
      forall oidx ost oss msgs,
        InvObjExcl0 oidx ost oss msgs ->
        ObjExcl0 oidx ost msgs ->
        ObjCoh ost#[val] oidx ost msgs.
    Proof.
      intros.
      specialize (H H0); dest.
      repeat split.
      apply NoCohMsgs_MsgsCoh; assumption.
    Qed.

    Lemma MsgsCoh_enqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx msg,
          MsgCoh cv cidx (midx, msg) ->
          MsgsCoh cv cidx (enqMP midx msg msgs).
    Proof.
      intros; apply MsgsP_enqMP; auto.
    Qed.

    Lemma MsgsCoh_other_midx_enqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx msg,
          ~ In midx [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          MsgsCoh cv cidx (enqMP midx msg msgs).
    Proof.
      intros.
      apply MsgsP_other_midx_enqMP; auto.
      intro Hx; elim H0; dest_in; simpl; tauto.
    Qed.

    Lemma MsgsCoh_other_midx_enqMsgs:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall eins,
          DisjList (idsOf eins) [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          MsgsCoh cv cidx (enqMsgs eins msgs).
    Proof.
      intros.
      apply MsgsP_other_midx_enqMsgs; auto.
      simpl.
      eapply DisjList_comm, DisjList_SubList;
        [|apply DisjList_comm; eassumption].
      solve_SubList.
    Qed.

    Lemma MsgsCoh_other_msg_id_enqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx msg,
          ~ In (msg_id msg) [mesiRsS; mesiRsE; mesiDownRsS] ->
          MsgsCoh cv cidx (enqMP midx msg msgs).
    Proof.
      intros; apply MsgsP_other_msg_id_enqMP; auto.
    Qed.

    Lemma MsgsCoh_other_msg_id_enqMsgs:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall eins,
          DisjList (map (fun idm => msg_id (valOf idm)) eins)
                   [mesiRsS; mesiRsE; mesiDownRsS] ->
          MsgsCoh cv cidx (enqMsgs eins msgs).
    Proof.
      intros; apply MsgsP_other_msg_id_enqMsgs; auto.
    Qed.

    Lemma MsgsCoh_deqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx,
          MsgsCoh cv cidx (deqMP midx msgs).
    Proof.
      intros; apply MsgsP_deqMP; auto.
    Qed.

    Lemma MsgsCoh_deqMsgs:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall minds,
          MsgsCoh cv cidx (deqMsgs minds msgs).
    Proof.
      intros; apply MsgsP_deqMsgs; auto.
    Qed.

  End ObjCohFacts.

  Definition ImplStateCoh (cv: nat) (st: MState): Prop :=
    Forall (fun oidx =>
              ost <-- (bst_oss st)@[oidx];
                _ <-- (bst_orqs st)@[oidx];
                ObjCoh cv oidx ost (bst_msgs st))
           (c_li_indices cifc ++ c_l1_indices cifc).

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

  Lemma mesi_sim_init:
    SimMESI (initsOf impl) (initsOf spec).
  Proof.
    split.
    - apply SimStateIntro with (cv:= 0).
      + reflexivity.
      + apply Forall_forall; intros oidx ?.
        subst cifc; rewrite c_li_indices_head_rootOf in H by assumption.
        simpl in H; icase oidx.
        * simpl; rewrite implOStatesInit_value_root by assumption.
          unfold implORqsInit; simpl.
          rewrite initORqs_value
            by (rewrite c_li_indices_head_rootOf by assumption; left; reflexivity).
          simpl; repeat split.
          do 3 red; intros.
          do 2 red in H0; dest_in.
        * simpl; rewrite implOStatesInit_value_non_root by assumption.
          unfold implORqsInit; simpl.
          rewrite initORqs_value
            by (rewrite c_li_indices_head_rootOf by assumption; right; assumption).
          simpl; repeat split.
          do 3 red; intros.
          do 2 red in H0; dest_in.
    - red; apply Forall_forall; intros oidx ?.
      repeat split.
      simpl; unfold implORqsInit.
      rewrite initORqs_value; [|apply in_or_app; auto].
      simpl; mred.
  Qed.

  Lemma mesi_sim_silent:
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

  Lemma mesi_sim_ext_in:
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
        red in H4; simpl in H4.
        apply Forall_forall; intros oidx ?.
        rewrite Forall_forall in H4; specialize (H4 _ H).
        disc_rule_conds_ex.
        repeat split.
        { intros; apply H4; auto.
          eapply MsgsP_enqMsgs_inv; eauto.
        }
        { apply MsgsCoh_other_midx_enqMsgs; [assumption|].
          destruct H1; simpl in H1.
          eapply DisjList_SubList; [eassumption|].
          apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
          { apply tree2Topo_obj_chns_minds_SubList; auto. }
          { apply tree2Topo_minds_merqs_disj. }
        }
      * apply SimExtMP_enqMsgs; auto.
        apply H1.
  Qed.

  Lemma mesi_sim_ext_out:
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
        red in H6; simpl in H6.
        apply Forall_forall; intros oidx ?.
        rewrite Forall_forall in H6; specialize (H6 _ H).
        disc_rule_conds_ex.
        repeat split.
        { intros; apply H6; auto.
          eapply MsgsP_other_midx_deqMsgs_inv; [eassumption|].
          simpl.
          apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
          { eapply SubList_trans;
              [|apply tree2Topo_obj_chns_minds_SubList; eauto].
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

  Ltac disc_rule_custom ::=
    repeat
      match goal with
      (* get simulation propositions for the current impl. state *)
      | [Hf: Forall _ (c_li_indices ?cifc ++ c_l1_indices ?cifc),
             Hin: In ?oidx (c_li_indices ?cifc)
         |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _]] =>
        rewrite Forall_forall in Hf;
        pose proof (Hf _ (in_or_app _ _ _ (or_introl Hin)))
      | [Hf: Forall _ (c_li_indices ?cifc ++ c_l1_indices ?cifc),
             Hin: In ?oidx (tl (c_li_indices ?cifc))
         |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _]] =>
        rewrite Forall_forall in Hf;
        pose proof (Hf _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))))
      | [Hf: Forall _ (c_li_indices ?cifc ++ c_l1_indices ?cifc),
             Hin: In ?oidx (c_l1_indices ?cifc)
         |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _]] =>
        rewrite Forall_forall in Hf;
        pose proof (Hf _ (in_or_app _ _ _ (or_intror Hin)))
      (* rewrite a coherent value *)
      | [H: fst ?ost = fst _ |- context[fst ?ost] ] => rewrite H in *
      (* rewrite inputs/outputs message ids *)
      | [H: msg_id ?rmsg = _ |- context[msg_id ?rmsg] ] => rewrite H
      end.
  
  (*! Prove [SimMESI] for internal steps *)

  Ltac solve_ImplStateCoh :=
    idtac.
  
  Ltac solve_SpecStateCoh :=
    eapply SimStateIntro; [solve_rule_conds_ex|].
  
  Ltac solve_sim_mesi_ext_mp :=
    red; simpl; split; [|solve_sim_ext_mp].

  Ltac solve_sim_mesi :=
    solve_sim_mesi_ext_mp;
    solve_SpecStateCoh;
    solve_ImplStateCoh.

  Ltac solve_ImplOStateMESI :=
    intros;
    auto; try solve_mesi; (* check if the goal is solved automatically *)
    match goal with
    | [H: _ -> ?P |- ?P] => apply H; auto
    | [H: _ -> _ -> ?P |- ?P] => apply H; auto
    end;
    try match goal with
        | H:MsgsP ?P _ |- MsgsP ?P _ => disc_MsgsP H; assumption
        end;
    try solve_mesi.

  Ltac solve_MsgsCoh :=
    repeat
      (try match goal with
           | |- MsgsCoh _ _ (enqMP _ _ _) =>
             apply MsgsCoh_other_midx_enqMP;
             [|solve_chn_not_in; auto; fail]
           | |- MsgsCoh _ _ (enqMP _ _ _) =>
             apply MsgsCoh_other_msg_id_enqMP; [|solve_not_in]
           | |- MsgsCoh _ _ (enqMP _ _ _) =>
             apply MsgsCoh_enqMP;
             [|do 2 red; cbv [map cohMsgs]; solve_caseDec; reflexivity]
           | |- MsgsCoh _ _ (enqMsgs _ _) =>
             apply MsgsCoh_other_msg_id_enqMsgs; [|solve_DisjList_ex idx_dec]
           | |- MsgsCoh _ _ (deqMP _ _) => apply MsgsCoh_deqMP
           | |- MsgsCoh _ _ (deqMsgs _ _) => apply MsgsCoh_deqMsgs
           end; try eassumption).

  Ltac derive_input_msg_coherent :=
    match goal with
    | [Hcoh: MsgsCoh ?cv _ _, Hfmp: FirstMPI _ (_, ?cmsg) |- _] =>
      let Ha := fresh "H" in
      assert (msg_value cmsg = cv)
        as Ha by (disc_MsgsCoh_by_FirstMP Hcoh Hfmp; assumption);
      rewrite Ha in *
    end.

  Ltac derive_obj_coherent oidx :=
    match goal with
    | [Hcoh: _ -> _ -> fst ?ost = ?cv, Host: ?oss@[oidx] = Some ?ost |- _] =>
      let Ha := fresh "H" in
      assert (fst ost = cv) as Ha by (apply Hcoh; auto; solve_mesi);
      rewrite Ha in *
    end.

  Ltac derive_coherence_of oidx :=
    match goal with
    | [Hf: forall _, In _ ?l -> _, He: In oidx ?l |- _] =>
      pose proof (Hf _ He); disc_rule_conds_ex
    end.

  Theorem mesi_sim_ok:
    InvSim step_m step_m (MesiInvOk.InvForSim topo) SimMESI impl spec.
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
    pose proof (mesi_RootChnInv_ok H) as Hprc.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr)
                  (reachable_steps H (steps_singleton H2))) as Hnmcf.

    inv H2;
      [apply mesi_sim_silent; assumption
      |apply mesi_sim_ext_in; assumption
      |apply mesi_sim_ext_out; assumption
      |].

    destruct sst1 as [soss1 sorqs1 smsgs1].
    destruct H0; simpl in H0, H2; simpl.
    inv H0.
    red in H15; simpl in H15.
    red in H6; simpl in H6.
    destruct (soss1@[specIdx]) as [sost|] eqn:Hsost; simpl in *; [|exfalso; auto].
    destruct (sorqs1@[specIdx]) as [sorq|] eqn:Hsorq; simpl in *; [|exfalso; auto].
    subst.
    simpl in H4; destruct H4; [subst|apply in_app_or in H0; destruct H0].

    - (*! Cases for the main memory *)
      Ltac solve_ImplStateCoh_mem_me :=
        disc_rule_conds_ex;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac solve_ImplStateCoh_mem_others lidx :=
        match goal with
        | [Hf: forall _, In _ ?l -> _, He: In lidx ?l |- _] =>
          specialize (Hf _ He); disc_rule_conds_ex
        end;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac case_ImplStateCoh_mem_me_others lidx :=
        match goal with
        | |- ImplStateCoh _ {| bst_oss := _ +[?oidx <- _] |} =>
          red; simpl;
          apply Forall_forall;
          intros lidx ?; destruct (idx_dec lidx oidx); subst
        end.

      Ltac solve_ImplStateCoh ::=
        let lidx := fresh "lidx" in
        case_ImplStateCoh_mem_me_others lidx;
        [solve_ImplStateCoh_mem_me|solve_ImplStateCoh_mem_others lidx].

      (** Derive some properties of the root *)
      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      
      assert (In (rootOf (fst (tree2Topo tr 0))) (c_li_indices (snd (tree2Topo tr 0)))).
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      assert (~ In (rootOf (fst (tree2Topo tr 0))) (c_l1_indices (snd (tree2Topo tr 0)))).
      { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
        apply (DisjList_NoDup idx_dec) in H4.
        eapply DisjList_In_2; eassumption.
      }

      disc_rule_conds_ex.
      pose proof (RootChnInv_root_NoRsI Hprc) as Hnrsi.
      pose proof (RootChnInv_root_NoRqI Hprc) as Hnrqi.
      unfold topo in Hnrsi, Hnrqi; simpl in Hnrsi, Hnrqi.

      assert (rsEdgeUpFrom topo (rootOf (fst (tree2Topo tr 0))) = None).
      { destruct (rsEdgeUpFrom _ _) eqn:Hrs; [|reflexivity].
        exfalso.
        apply rsEdgeUpFrom_Some with (sys:= impl) in Hrs;
          [|subst topo impl; auto].
        destruct Hrs as [rqUp [down [pidx ?]]]; dest.
        apply parentIdxOf_child_not_root in H27; [|subst topo; auto].
        auto.
      }

      (** Abstract the root. *)
      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.
      disc_rule_conds_ex.

      (** Do case analysis per a rule. *)
      apply in_app_or in H5; destruct H5.

      1: { (** Rules per a child *)
        apply concat_In in H5; destruct H5 as [crls [? ?]].
        apply in_map_iff in H5; destruct H5 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }
        
        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmE] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_mem_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              disc_getDir.
              admit.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_mem_others lidx. }
        }

        { (* [liInvImmWBI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_mem_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirME oidx cidx.
              derive_ObjInvWRq cidx.
              match goal with | [H: _ = cidx |- _] => clear H end.
              assert (NoRsI cidx msgs)
                by (solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvWB cidx H21.
              disc_InvWBCoh_inv cidx H20.
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_mem_others lidx. }
        }

      }

      dest_in.

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|exfalso; subst topo; congruence].
        derive_child_chns upCIdx.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        derive_child_chns cidx.
        derive_child_idx_in cidx.
        derive_coherence_of cidx.
        derive_input_msg_coherent.
        solve_sim_mesi.
        destruct (idx_dec lidx (obj_idx upCObj)); subst; solve_MsgsCoh.
      }

      { (* [liDownIRsUpDown] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|exfalso; subst topo; congruence].
        derive_child_chns upCIdx.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

    - (*! Cases for Li caches *)
      Ltac solve_ImplStateCoh_li_me :=
        disc_rule_conds_ex;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac solve_ImplStateCoh_li_others lidx :=
        match goal with
        | [Hf: forall _, In _ ?l -> _, He: In lidx ?l |- _] =>
          specialize (Hf _ He); disc_rule_conds_ex
        end;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac case_ImplStateCoh_li_me_others lidx :=
        match goal with
        | |- ImplStateCoh _ {| bst_oss := _ +[?oidx <- _] |} =>
          red; simpl;
          apply Forall_forall;
          intros lidx ?; destruct (idx_dec lidx oidx); subst
        end.

      Ltac solve_ImplStateCoh ::=
        let lidx := fresh "lidx" in
        case_ImplStateCoh_li_me_others lidx;
        [solve_ImplStateCoh_li_me|solve_ImplStateCoh_li_others lidx].

      apply in_map_iff in H0; destruct H0 as [oidx [? ?]]; subst; simpl in *.

      (** Derive some necessary information: 1) each Li has a parent. *)
      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_li_indices_tail_has_parent Htr _ _ H4).
      destruct H0 as [pidx [? ?]].
      pose proof (Htn _ _ H6); dest.

      (** 2) The object index does not belong to [c_l1_indices]. *)
      assert (~ In oidx (c_l1_indices (snd (tree2Topo tr 0)))).
      { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
        apply (DisjList_NoDup idx_dec) in H19.
        eapply DisjList_In_2; [eassumption|].
        apply tl_In; assumption.
      }

      disc_rule_conds_ex.
      (** Do case analysis per a rule. *)
      apply in_app_or in H5; destruct H5.

      1: { (** Rules per a child *)
        apply concat_In in H5; destruct H5 as [crls [? ?]].
        apply in_map_iff in H5; destruct H5 as [cidx [? ?]]; subst.

        (** 3) The child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          assert (NoRsI oidx msgs)
            by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }
        
        { (* [liGetSImmME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          assert (NoRsI oidx msgs)
            by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }
        
        { (* [liGetSRqUpUp] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetMRqUpUp] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmE] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_li_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              disc_getDir.
              admit.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_li_others lidx. }
        }

        { (* [liInvImmWBI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns cidx.
          derive_child_idx_in cidx.
          assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_li_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirME oidx cidx.
              derive_ObjInvWRq cidx.
              match goal with | [H: _ = cidx |- _] => clear H end.
              assert (NoRsI cidx msgs)
                by (solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvWB cidx H26.
              disc_InvWBCoh_inv cidx H25.
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_li_others lidx. }
        }

      }

      dest_in.

      { (* [liGetSRsDownDownS] *)
        disc_rule_conds_ex; spec_case_silent.

        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        derive_child_idx_in cidx.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.
        destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
      }

      { (* [liGetSRsDownDownE] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        derive_child_idx_in cidx.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.
        destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
      }

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|disc_MesiDownLockInv oidx H27].
        derive_child_chns upCIdx.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        derive_child_chns cidx.
        derive_child_idx_in cidx.
        derive_coherence_of cidx.
        derive_input_msg_coherent.

        solve_sim_mesi.
        destruct (idx_dec lidx (obj_idx upCObj)); subst; solve_MsgsCoh.
      }

      { (* [liDownSImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liDownSRqDownDownME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
        solve_sim_mesi.
      }

      { (* [liDownSRsUpUp] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [disc_MesiDownLockInv oidx H27|].
        disc_responses_from.
        derive_child_chns cidx.
        derive_child_idx_in cidx.
        derive_coherence_of cidx.
        derive_input_msg_coherent.
        solve_sim_mesi.
      }

      { (* [liGetMRsDownDownDirI] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        derive_child_idx_in cidx.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).
        solve_sim_mesi.
      }

      { (* [liGetMRsDownRqDownDirS] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx.
        solve_sim_mesi.
      }

      { (* [liDownIRsUpDown] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|disc_MesiDownLockInv oidx H27].
        derive_child_chns upCIdx.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liDownIImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liDownIRqDownDownDirS] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

      { (* [liDownIRqDownDownDirME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
        solve_sim_mesi.
      }

      { (* [liDownIRsUpUp] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [disc_MesiDownLockInv oidx H27|].
        disc_responses_from.
        solve_sim_mesi.
      }

      { (* [liInvRqUpUp] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

      { (* [liInvRqUpUpWB] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

      { (* [liInvRsDownDown] *)
        disc_rule_conds_ex.
        spec_case_silent.
        derive_footprint_info_basis oidx.
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liPushImm] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_li_me_others lidx.
        { solve_ImplStateCoh_li_me. }
        { specialize (H15 _ H12); disc_rule_conds_ex. }
      }

    - (*! Cases for L1 caches *)
      apply in_map_iff in H0; destruct H0 as [oidx [? ?]]; subst.

      Ltac solve_ImplStateCoh_l1_me :=
        disc_rule_conds_ex;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac solve_ImplStateCoh_l1_others :=
        try match goal with
            | [H: MsgsCoh _ ?oidx _, Hin: In ?oidx _ |- _] => clear Hin
            end;
        match goal with
        | [Hf: forall _, In _ ?l -> _, He: In _ ?l |- _] =>
          specialize (Hf _ He); disc_rule_conds_ex
        end;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac case_ImplStateCoh_l1_me_others :=
        red; simpl;
        match goal with
        | [H: MsgsCoh _ ?oidx _ |- Forall _ _] =>
          let lidx := fresh "lidx" in
          apply Forall_forall;
          intros lidx ?; destruct (idx_dec lidx oidx); subst
        end.
      
      Ltac solve_ImplStateCoh ::=
        case_ImplStateCoh_l1_me_others;
        [solve_ImplStateCoh_l1_me|solve_ImplStateCoh_l1_others].

      (** Derive some necessary information: each L1 has a parent. *)
      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H4).
      destruct H0 as [pidx [? ?]].
      pose proof (Htn _ _ H6); dest.

      Opaque In.
      disc_rule_conds_ex.
      Transparent In.
      (** Do case analysis per a rule. *)
      dest_in.

      + (* [l1GetSImm] *)
        disc_rule_conds_ex.
        spec_case_get oidx.        
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1GetSRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1GetSRsDownDownS] *)
        disc_rule_conds_ex.
        spec_case_get oidx.

        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.

      + (* [l1GetSRsDownDownE] *)
        disc_rule_conds_ex.
        spec_case_get oidx.

        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.

      + (* [l1DownSImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1GetMImmE] *)
        disc_rule_conds_ex.
        spec_case_set oidx.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).
        disc_rule_conds_ex.

        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_l1_me_others.
        * mred; simpl.
          eapply ObjExcl0_ObjCoh.
          { specialize (H3 oidx); repeat (simpl in H3; mred); dest.
            eassumption.
          }
          { split; [simpl; solve_mesi|solve_MsgsP]. }

        * clear H4. (* In oidx .. *)
          mred; simpl.
          assert (exists lost lorq, oss@[lidx] = Some lost /\
                                    orqs@[lidx] = Some lorq).
          { specialize (H15 _ H11).
            solve_rule_conds_ex.
          }
          destruct H4 as [lost [lorq [? ?]]]; rewrite H4, H12; simpl.
          eapply ObjInvalid_ObjCoh.
          { apply Hnmcf; [|simpl; mred].
            assumption.
          }
          { specialize (H19 lidx); simpl in H19; mred. }
          { eapply InvExcl_excl_invalid; [eapply H3|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.
            solve_MsgsP.
          }
          
      + (* [l1GetMImmM] *)
        disc_rule_conds_ex.
        spec_case_set oidx.
        assert (NoRsI oidx msgs) 
          by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).
        disc_rule_conds_ex.
        
        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_l1_me_others.
        * mred; simpl.
          eapply ObjExcl0_ObjCoh.
          { specialize (H3 oidx); repeat (simpl in H3; mred); dest.
            eassumption.
          }
          { split; [simpl; solve_mesi|solve_MsgsP]. }

        * clear H4. (* In oidx .. *)
          mred; simpl.
          assert (exists lost lorq, oss@[lidx] = Some lost /\
                                    orqs@[lidx] = Some lorq).
          { specialize (H15 _ H11).
            solve_rule_conds_ex.
          }
          destruct H4 as [lost [lorq [? ?]]]; rewrite H4, H12; simpl.
          eapply ObjInvalid_ObjCoh.
          { apply Hnmcf; [|simpl; mred].
            assumption.
          }
          { specialize (H19 lidx); simpl in H19; mred. }
          { eapply InvExcl_excl_invalid; [eapply H3|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.
            solve_MsgsP.
          }

      + (* [l1GetMRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        solve_sim_mesi.

      + (* [l1GetMRsDownDown] *)
        disc_rule_conds_ex.
        spec_case_set oidx.

        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.

        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rsDown oidx).
        disc_rule_conds_ex.

        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_l1_me_others.
        * mred; simpl.
          eapply ObjExcl0_ObjCoh.
          { specialize (H3 oidx); repeat (simpl in H3; mred); dest.
            eassumption.
          }
          { split; [simpl; solve_mesi|solve_MsgsP]. }
          
        * clear H4. (* In oidx .. *)
          mred; simpl.
          assert (exists lost lorq, oss@[lidx] = Some lost /\
                                    orqs@[lidx] = Some lorq).
          { specialize (H15 _ H31).
            solve_rule_conds_ex.
          }
          destruct H4 as [lost [lorq [? ?]]]; rewrite H4, H40; simpl.
          eapply ObjInvalid_ObjCoh.
          { apply Hnmcf; [assumption|simpl; mred]. }
          { specialize (H19 lidx); simpl in H19; mred. }
          { eapply InvExcl_excl_invalid; [eapply H3|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.
            solve_MsgsP.
          }
          
      + (* [l1DownIImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1InvRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        solve_sim_mesi.
        
      + (* [l1InvRqUpUpM] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1InvRsDownDown] *)
        disc_rule_conds_ex.
        spec_case_silent.
        derive_footprint_info_basis oidx.
        disc_rule_conds_ex.
        solve_sim_mesi.

        Unshelve.
        all: eassumption.

  Qed.

  Theorem mesi_ok:
    (steps step_m) # (steps step_m) |-- impl ⊑ spec.
  Proof.
    apply invSim_implies_refinement
      with (ginv:= MesiInvOk.InvForSim topo) (sim:= SimMESI).
    - apply mesi_sim_ok.
    - apply mesi_InvForSim_ok.
    - apply mesi_sim_init.
    - apply mesi_InvForSim_init.
  Qed.

End Sim.

