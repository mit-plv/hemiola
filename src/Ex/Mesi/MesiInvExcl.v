Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Import Ex.Mesi.MesiInv.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Definition ObjsInvalid (eidx: IdxT) (oss: OStates) (msgs: MessagePool Msg) :=
  forall oidx,
    oidx <> eidx ->
    ost <+- oss@[oidx]; ObjInvalid oidx ost msgs.

Definition InvObjExcl0 (oidx: IdxT) (ost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  ObjExcl0 oidx ost msgs ->
  ObjsInvalid oidx oss msgs /\ NoCohMsgs oidx msgs.

Definition InvExcl (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      InvObjExcl0 eidx eost (bst_oss st) (bst_msgs st).

Section Facts.

  (** [ObjExcl0] *)

  Lemma ObjExcl0_enqMP_inv:
    forall oidx ost msgs midx msg,
      ObjExcl0 oidx ost (enqMP midx msg msgs) ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    disc_MsgsP H0; assumption.
  Qed.

  Lemma ObjExcl0_enqMsgs_inv:
    forall oidx ost msgs nmsgs,
      ObjExcl0 oidx ost (enqMsgs nmsgs msgs) ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    disc_MsgsP H0; assumption.
  Qed.

  Lemma ObjExcl0_other_midx_deqMP_inv:
    forall oidx ost msgs midx,
      ObjExcl0 oidx ost (deqMP midx msgs) ->
      midx <> downTo oidx ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    disc_MsgsP H1; assumption.
  Qed.

  Lemma ObjExcl0_other_midx_deqMsgs_inv:
    forall oidx ost msgs (rmsgs: list (Id Msg)),
      ObjExcl0 oidx ost (deqMsgs (idsOf rmsgs) msgs) ->
      NoDup (idsOf rmsgs) ->
      Forall (FirstMPI msgs) rmsgs ->
      Forall (fun midx => midx <> downTo oidx) (idsOf rmsgs) ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    apply MsgsP_other_midx_deqMsgs_inv in H3.
    - assumption.
    - simpl.
      simpl; apply (DisjList_spec_1 idx_dec); intros.
      rewrite Forall_forall in H2; specialize (H2 _ H4).
      intro Hx; dest_in; auto.
  Qed.

  Lemma ObjExcl0_other_msg_id_deqMP_inv:
    forall oidx ost msgs midx,
      ObjExcl0 oidx ost (deqMP midx msgs) ->
      forall msg,
        FirstMP msgs midx msg ->
        msg.(msg_id) <> mesiInvRs ->
        ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    eapply MsgsP_other_msg_id_deqMP_inv in H2;
      [|eassumption|simpl; intuition].
    assumption.
  Qed.

  Lemma ObjExcl0_other_msg_id_deqMsgs_inv:
    forall oidx ost msgs rmsgs,
      ObjExcl0 oidx ost (deqMsgs (idsOf rmsgs) msgs) ->
      NoDup (idsOf rmsgs) ->
      Forall (FirstMPI msgs) rmsgs ->
      Forall (fun idm => (valOf idm).(msg_id) <> mesiInvRs) rmsgs ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    eapply MsgsP_other_msg_id_deqMsgs_inv in H3; try assumption.
    simpl; apply (DisjList_spec_1 idx_dec); intros.
    apply in_map_iff in H4; dest; subst.
    rewrite Forall_forall in H2; specialize (H2 _ H5).
    intro Hx; dest_in; auto.
  Qed.

  Ltac disc_ObjExcl0_msgs H :=
    repeat
      (first [apply ObjExcl0_enqMP_inv in H
             |apply ObjExcl0_enqMsgs_inv in H
             |apply ObjExcl0_other_midx_deqMP_inv in H; [|solve_chn_neq]
             |apply ObjExcl0_other_midx_deqMsgs_inv in H;
              [|eassumption|eassumption|] (** FIXME: need to debug when not working *)
             |eapply ObjExcl0_other_msg_id_deqMP_inv in H;
              [|eassumption|congruence]
             |eapply ObjExcl0_other_msg_id_deqMsgs_inv in H;
              [|eassumption|eassumption|] (** FIXME: need to debug when not working *)
      ]).

End Facts.

Section InvExcl.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvExcl_init:
    Invariant.InvInit impl InvExcl.
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[eidx] as [eost|] eqn:Heost; simpl; auto.
    red; intros.
    red in H; dest.

    destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc)).
    - subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
      inv i.
      + split.
        * red; intros.
          destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
          red.
          destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                           ++ c_l1_indices (snd (tree2Topo tr 0)))).
          { rewrite c_li_indices_head_rootOf in i by assumption.
            inv i; [exfalso; auto|].
            rewrite implOStatesInit_value_non_root in Host by assumption.
            inv Host.
            left; repeat split; [simpl; solve_mesi..|].
            do 3 red; intros; do 2 red in H3; dest_in.
          }
          { rewrite implOStatesInit_None in Host by assumption.
            discriminate.
          }
        * do 3 red; intros; do 2 red in H1; dest_in.
      + exfalso.
        rewrite implOStatesInit_value_non_root in Heost by assumption.
        inv Heost.
        simpl in *; solve_mesi.
    - exfalso.
      rewrite implOStatesInit_None in Heost by assumption.
      discriminate.
  Qed.

  Lemma mesi_InvExcl_ext_in:
    forall oss orqs msgs,
      InvExcl {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvExcl {| bst_oss := oss; bst_orqs := orqs; bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    red; intros.

    destruct H2.
    apply MsgsP_enqMsgs_inv in H3.
    specialize (H (conj H2 H3)); dest.

    split.
    - red; intros.
      specialize (H _ H5).
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
      destruct H.
      + left.
        red in H; dest.
        repeat split; [assumption..|].
        apply MsgsP_other_midx_enqMsgs; [assumption|].
        destruct H1; simpl.
        eapply DisjList_SubList; [eassumption|].
        eapply DisjList_comm, DisjList_SubList.
        * eapply SubList_trans;
            [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
          { solve_SubList. }
          { specialize (H0 oidx); simpl in H0.
            rewrite Host in H0; simpl in H0.
            eassumption.
          }
        * apply tree2Topo_minds_merqs_disj.
      + right.
        destruct H as [idm ?]; dest.
        exists idm; split; [|assumption].
        apply InMP_or_enqMsgs; auto.

    - apply MsgsP_other_midx_enqMsgs; [assumption|].
      destruct H1; simpl.
      eapply DisjList_SubList; [eassumption|].
      eapply DisjList_comm, DisjList_SubList.
      + eapply SubList_trans;
          [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
        * solve_SubList.
        * specialize (H0 eidx); simpl in H0.
          rewrite Heost in H0; simpl in H0.
          eassumption.
      + apply tree2Topo_minds_merqs_disj.
  Qed.

  Corollary mesi_InvExcl_InvTrsIns: InvTrsIns impl InvExcl.
  Proof.
    red; intros.
    inv H1.
    eapply mesi_InvExcl_ext_in; eauto.
    apply (mesi_InObjInds H).
  Qed.

  Lemma mesi_InvExcl_ext_out:
    forall oss orqs msgs,
      InvExcl {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvExcl {| bst_oss := oss;
                   bst_orqs := orqs;
                   bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    red; intros.

    destruct H2.
    apply MsgsP_other_midx_deqMsgs_inv in H3.
    - specialize (H (conj H2 H3)); dest.
      split.
      + red; intros.
        specialize (H _ H5).
        destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
        destruct H.
        * left.
          red in H; dest.
          repeat split; [assumption..|].
          apply MsgsP_deqMsgs; assumption.
        * right.
          destruct H as [idm ?]; dest.
          exists idm; split; [|assumption].
          apply deqMsgs_InMP_midx; [assumption|].
          destruct H1.
          eapply DisjList_In_1.
          { eapply DisjList_SubList; [eassumption|].
            apply DisjList_comm, tree2Topo_minds_merss_disj.
          }
          { eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx).
            { specialize (H0 oidx); simpl in H0.
              rewrite Host in H0; simpl in H0.
              eassumption.
            }
            { inv H6; rewrite H9.
              solve_SubList.
            }
          }
      + apply MsgsP_deqMsgs; assumption.

    - destruct H1.
      simpl; eapply DisjList_SubList; [eassumption|].
      eapply DisjList_comm, DisjList_SubList.
      + eapply SubList_trans;
          [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
        * solve_SubList.
        * specialize (H0 eidx); simpl in H0.
          rewrite Heost in H0; simpl in H0.
          eassumption.
      + apply tree2Topo_minds_merss_disj.
  Qed.

  Corollary mesi_InvExcl_InvTrsOuts: InvTrsOuts impl InvExcl.
  Proof.
    red; intros.
    inv H1.
    eapply mesi_InvExcl_ext_out; eauto.
    apply (mesi_InObjInds H).
  Qed.

  Definition InvExclMsgOutPred: MsgOutPred :=
    fun eout oss orqs =>
      caseDec sig_dec (sigOf eout) True
              (List.concat
                 (map (fun oidx =>
                         [((rqUpFrom (l1ExtOf oidx), (MRq, Spec.getRq)), False);
                            ((rqUpFrom (l1ExtOf oidx), (MRq, Spec.setRq)), False)])
                      (c_l1_indices cifc))).

  Lemma InvExclMsgOutPred_good:
    GoodMsgOutPred topo InvExclMsgOutPred.
  Proof.
  Admitted.

  Lemma mesi_InvExcl_InvTrs_init:
    forall st1,
      Reachable (steps step_m) impl st1 ->
      InvExcl st1 ->
      forall oidx ridx ins outs st2,
        SubList (idsOf ins) (sys_merqs impl) ->
        step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
        AtomicInv
          InvExclMsgOutPred
          ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
        InvExcl st2.
  Proof.
  Admitted.

  Ltac disc_rule_custom ::=
    try disc_AtomicInv.

  Lemma mesi_InvExcl_InvTrs: InvTrs impl InvExcl.
  Proof.
    eapply inv_atomic_InvTrs;
      [red; intros; eapply mesi_InvExcl_InvTrsIns; eauto
      |red; intros; eapply mesi_InvExcl_InvTrsOuts; eauto
      |].
    instantiate (1:= AtomicInv InvExclMsgOutPred).

    red; intros.
    destruct H1.
    generalize dependent ist2.
    induction H3; simpl; intros; subst;
      [inv_steps; apply mesi_InvExcl_InvTrs_init; auto|].

    inv_steps.
    pose proof (reachable_steps H H9) as Hr1.
    pose proof (reachable_steps Hr1 (steps_singleton H11)) as Hr2.

    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    (* pose proof (footprints_ok *)
    (*               msiSv_impl_ORqsInit *)
    (*               msiSv_impl_GoodRqRsSys Hr1) as Hftinv. *)
    (* pose proof (upLockInv_ok *)
    (*               msiSv_impl_ORqsInit *)
    (*               msiSv_impl_GoodRqRsSys *)
    (*               msiSv_impl_RqRsDTree Hr1) as Hpulinv. *)

    specialize (IHAtomic H1 _ H9); dest.
    inv_step.

    simpl in H13; destruct H13; [subst|apply in_app_or in H7; destruct H7].
    
    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      assert (In (rootOf (fst (tree2Topo tr 0)))
                 (c_li_indices (snd (tree2Topo tr 0)))) as Hin.
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H14; destruct H14.

      1: { (** Rules per a child *)
        apply concat_In in H7; destruct H7 as [crls [? ?]].
        apply in_map_iff in H7; destruct H7 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.
        all: admit.
      }

      dest_in.
      all: admit.

    - (*! Cases for Li caches *)
      apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst; simpl in *.

      pose proof (c_li_indices_tail_has_parent Htr _ _ H8).
      destruct H7 as [pidx [? ?]].
      pose proof (Htn _ _ H10); dest.

      (** Do case analysis per a rule. *)
      apply in_app_or in H14; destruct H14.

      1: { (** Rules per a child *)
        apply concat_In in H14; destruct H14 as [crls [? ?]].
        apply in_map_iff in H14; destruct H14 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.
        all: admit.
      }

      dest_in.
      all: admit.

    - (*! Cases for L1 caches *)
      apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst.

      pose proof (c_l1_indices_has_parent Htr _ _ H8).
      destruct H7 as [pidx [? ?]].
      pose proof (Htn _ _ H10); dest.

      (** Discharge an invariant that holds only for L1 caches. *)
      (* red in Hl1d; simpl in Hl1d. *)
      (* rewrite Forall_forall in Hl1d; specialize (Hl1d _ H2). *)
      (* simpl in H5; rewrite H5 in Hl1d; simpl in Hl1d. *)

      (** Do case analysis per a rule. *)
      dest_in.
      all: admit.

  Qed.

  Lemma mesi_InvExcl_step:
    InvStep impl step_m InvExcl.
  Proof.
    apply invSeq_serializable_invStep.
    - apply mesi_InvExcl_init.
    - apply inv_trs_seqSteps.
      apply mesi_InvExcl_InvTrs.
    - eapply rqrs_Serializable.
      + apply mesi_GoodORqsInit.
      + apply mesi_RqRsSys.
  Qed.

  Lemma mesi_InvExcl_ok:
    Invariant.InvReachable impl step_m InvExcl.
  Proof.
    apply inv_reachable.
    - apply mesi_InvExcl_init.
    - apply mesi_InvExcl_step.
  Qed.

End InvExcl.

