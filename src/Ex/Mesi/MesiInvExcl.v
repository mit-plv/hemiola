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

Definition ObjsInvalid (inP: IdxT -> Prop) (oss: OStates) (msgs: MessagePool Msg) :=
  forall oidx,
    inP oidx ->
    ost <+- oss@[oidx]; ObjInvalid oidx ost msgs.

Definition InvObjExcl0 (eidx: IdxT) (ost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  ObjExcl0 eidx ost msgs ->
  ObjsInvalid (fun oidx => eidx <> oidx) oss msgs /\
  NoCohMsgs eidx msgs.

Definition InvObjOwned (topo: DTree) (eidx: IdxT) (eost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  eost#[owned] = true ->
  ObjsInvalid (fun oidx => ~ In oidx (subtreeIndsOf topo eidx)) oss msgs.

Definition InvExcl (topo: DTree) (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_oss st) (bst_msgs st) /\
       InvObjOwned topo eidx eost (bst_oss st) (bst_msgs st)).

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

  Lemma ObjsInvalid_obj_status_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx,
        inP oidx ->
        NoRsI oidx msgs ->
        forall ost,
          oss@[oidx] = Some ost ->
          mesiS <= ost#[status] ->
          False.
  Proof.
    intros.
    specialize (H _ H0).
    rewrite H2 in H; simpl in H.
    destruct H.
    - red in H; solve_mesi.
    - eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
  Qed.

End Facts.

Ltac disc_ObjExcl0_msgs H :=
  repeat
    (first [apply ObjExcl0_enqMP_inv in H
           |apply ObjExcl0_enqMsgs_inv in H
           |apply ObjExcl0_other_midx_deqMP_inv in H;
            [|solve_chn_neq; fail]
           |apply ObjExcl0_other_midx_deqMsgs_inv in H;
            [|eassumption|eassumption|] (** FIXME: need to debug when not working *)
           |eapply ObjExcl0_other_msg_id_deqMP_inv in H;
            [|eassumption
             |simpl; try match goal with
                         | [H: ?lh = _ |- ?lh <> _] => rewrite H
                         end; discriminate]
           |eapply ObjExcl0_other_msg_id_deqMsgs_inv in H;
            [|eassumption|eassumption|] (** FIXME: need to debug when not working *)
    ]).

Section InvExcl.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvExcl_init:
    Invariant.InvInit impl (InvExcl topo).
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[eidx] as [eost|] eqn:Heost; simpl; auto.
    split.

    - red; intros.
      red in H; dest.
      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc)).
      + subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
        inv i.
        * split.
          { red; intros.
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
          }
          { do 3 red; intros; do 2 red in H1; dest_in. }
        * exfalso.
          rewrite implOStatesInit_value_non_root in Heost by assumption.
          inv Heost.
          simpl in *; solve_mesi.
      + exfalso.
        rewrite implOStatesInit_None in Heost by assumption.
        discriminate.

    - red; intros.
      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc)).
      + subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
        inv i.
        * red; intros.
          destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
          red.
          destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                           ++ c_l1_indices (snd (tree2Topo tr 0)))).
          { rewrite c_li_indices_head_rootOf in i by assumption.
            inv i.
            { elim H0.
              apply subtreeIndsOf_root_in.
              { apply tree2Topo_WfDTree. }
              { apply Subtree_refl. }
            }
            { rewrite implOStatesInit_value_non_root in Host by assumption.
              inv Host.
              left; repeat split; [simpl; solve_mesi..|].
              do 3 red; intros; do 2 red in H2; dest_in.
            }
          }
          { rewrite implOStatesInit_None in Host by assumption; discriminate. }
        * rewrite implOStatesInit_value_non_root in Heost by assumption.
          inv Heost; discriminate.
      + rewrite implOStatesInit_None in Heost by assumption; discriminate.
  Qed.

  Lemma mesi_InvExcl_ext_in:
    forall oss orqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := orqs;
                        bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    dest; split.

    - clear H2.
      red; intros.
      destruct H2.
      apply MsgsP_enqMsgs_inv in H3.
      specialize (H (conj H2 H3)); dest.

      split.
      + red; intros.
        specialize (H _ H5).
        destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
        destruct H.
        * left.
          red in H; dest.
          repeat split; [assumption..|].
          apply MsgsP_other_midx_enqMsgs; [assumption|].
          destruct H1; simpl.
          eapply DisjList_SubList; [eassumption|].
          eapply DisjList_comm, DisjList_SubList.
          { eapply SubList_trans;
              [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
            { solve_SubList. }
            { specialize (H0 oidx); simpl in H0.
              rewrite Host in H0; simpl in H0.
              eassumption.
            }
          }
          { apply tree2Topo_minds_merqs_disj. }
        * right.
          destruct H as [idm ?]; dest.
          exists idm; split; [|assumption].
          apply InMP_or_enqMsgs; auto.

      + apply MsgsP_other_midx_enqMsgs; [assumption|].
        destruct H1; simpl.
        eapply DisjList_SubList; [eassumption|].
        eapply DisjList_comm, DisjList_SubList.
        * eapply SubList_trans;
            [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
          { solve_SubList. }
          { specialize (H0 eidx); simpl in H0.
            rewrite Heost in H0; simpl in H0.
            eassumption.
          }
        * apply tree2Topo_minds_merqs_disj.

    - clear H.
      red; intros.
      specialize (H2 H).

      red; intros.
      specialize (H2 _ H3).
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
      destruct H2.
      + left.
        red in H2; dest.
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
        destruct H2 as [idm ?]; dest.
        exists idm; split; [|assumption].
        apply InMP_or_enqMsgs; auto.
  Qed.

  Corollary mesi_InvExcl_InvTrsIns: InvTrsIns impl (InvExcl topo).
  Proof.
    red; intros.
    inv H1.
    eapply mesi_InvExcl_ext_in; eauto.
    apply (mesi_InObjInds H).
  Qed.

  Lemma mesi_InvExcl_ext_out:
    forall oss orqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := orqs;
                        bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    dest; split.

    - clear H2.
      red; intros.
      destruct H2.
      apply MsgsP_other_midx_deqMsgs_inv in H3.
      + specialize (H (conj H2 H3)); dest.
        split.
        * red; intros.
          specialize (H _ H5).
          destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
          destruct H.
          { left.
            red in H; dest.
            repeat split; [assumption..|].
            apply MsgsP_deqMsgs; assumption.
          }
          { right.
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
          }
        * apply MsgsP_deqMsgs; assumption.

      + destruct H1.
        simpl; eapply DisjList_SubList; [eassumption|].
        eapply DisjList_comm, DisjList_SubList.
        * eapply SubList_trans;
            [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
          { solve_SubList. }
          { specialize (H0 eidx); simpl in H0.
            rewrite Heost in H0; simpl in H0.
            eassumption.
          }
        * apply tree2Topo_minds_merss_disj.

    - clear H.
      red; intros.
      specialize (H2 H).
      red; intros.
      specialize (H2 _ H3).
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
      destruct H2.
      + left.
        red in H2; dest.
        repeat split; [assumption..|].
        apply MsgsP_deqMsgs; assumption.
      + right.
        destruct H2 as [idm ?]; dest.
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
          { inv H4; rewrite H7.
            solve_SubList.
          }
        }
  Qed.

  Corollary mesi_InvExcl_InvTrsOuts: InvTrsOuts impl (InvExcl topo).
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
      InvExcl topo st1 ->
      forall oidx ridx ins outs st2,
        SubList (idsOf ins) (sys_merqs impl) ->
        step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
        AtomicInv
          InvExclMsgOutPred
          ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
        InvExcl topo st2.
  Proof.
  Admitted.

  Ltac disc_bind_true :=
    repeat
      match goal with
      | |- _ <+- ?ov; _ =>
        first [match goal with
               | [H: ov = _ |- _] => rewrite H in *; simpl in *
               end
              |let Hov := fresh "H" in
               let v := fresh "v" in
               destruct ov as [v|] eqn:Hov; simpl in *; [|auto]]
      end.

  Ltac disc_rule_custom ::=
    try disc_AtomicInv.

  (*! Ltacs about [InvExcl] *)

  Ltac case_InvExcl_me_others :=
    match goal with
    | |- InvExcl _ _ => red; simpl; intros; mred; simpl
    end.

  Ltac case_InvObjOwned :=
    match goal with
    | [H: InvObjOwned _ _ _ _ _ |- InvObjOwned _ _ _ _ _] =>
      let Ho := fresh "H" in
      red; simpl; intros Ho; specialize (H Ho);
      red; intros; mred; simpl
    end.

  Ltac case_ObjInvalid_with oidx :=
    match goal with
    | |- ObjInvalid ?eidx _ _ =>
      destruct (idx_dec eidx oidx); subst
    end.

  Ltac case_ObjInvalid :=
    match goal with
    | [H: ObjInvalid _ _ _ |- ObjInvalid _ _ _] =>
      destruct H; [left|right]
    end.

  Ltac disc_InvExcl_this :=
    repeat
      match goal with
      | [H: InvExcl _ _ |- InvObjExcl0 ?oidx _ _ _ /\ _] =>
        specialize (H oidx); simpl in H
      | [He: _ <+- ?ov; _, Ho: ?ov = Some _ |- _] =>
        rewrite Ho in He; simpl in He; dest; split
      end.

  Ltac disc_InvExcl_others :=
    match goal with
    | [H: InvExcl _ _ |- _ <+- _@[?eidx]; _] =>
      specialize (H eidx); simpl in H;
      disc_bind_true; dest; split
    end.

  Ltac disc_ObjsInvalid oidx :=
    match goal with
    | [Hi: ObjsInvalid _ _ _ |- _] =>
      specialize (Hi oidx ltac:(auto)); disc_bind_true
    end.

  Ltac disc_InvObjExcl0 :=
    match goal with
    | [H: InvObjExcl0 _ _ _ _ |- InvObjExcl0 _ _ _ _] =>
      let He := fresh "H" in
      red; intros He; disc_ObjExcl0_msgs He;
      specialize (H He); dest
    end.

  Ltac derive_not_InvalidObj_not_in roidx :=
    match goal with
    | [H: ObjsInvalid (fun _ => ~ In _ ?inds) _ _ |- _] =>
      assert (In roidx inds)
        by (destruct (in_dec idx_dec roidx inds); [assumption|];
            exfalso;
            eapply ObjsInvalid_obj_status_false with (oidx:= roidx); eauto;
            simpl; solve_mesi)
    end.

  Ltac solve_InvObjExcl0_by_ObjExcl0_false :=
    red; intros; exfalso;
    match goal with
    | [H: ObjExcl0 _ _ _ |- _] =>
      red in H; dest; simpl in *; solve_mesi
    end.

  Local Hint Extern 0 (WfDTree topo) => apply tree2Topo_WfDTree.
  Ltac solve_by_topo_false :=
    match goal with
    | [H: ~ In ?oidx (subtreeIndsOf topo ?oidx) |- _] =>
      elim H; eapply parent_subtreeIndsOf_self_in; eauto; fail
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx, Hi: ~ In ?cidx (subtreeIndsOf topo ?oidx) |- _] =>
      elim Hi; apply subtreeIndsOf_child_in; auto; fail
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx, Hip: In ?pidx (subtreeIndsOf topo ?oidx), Hic: ~ In ?cidx (subtreeIndsOf topo ?oidx) |- _] =>
      elim Hic; eapply inside_child_in; eauto; fail
    end.

  Ltac solve_ObjInvalid0 :=
    match goal with
    | [H: ObjInvalid0 _ _ _ |- ObjInvalid0 _ _ _] =>
      destruct H; split; [assumption|solve_MsgsP]
    end.

  Ltac solve_ObjInvRs :=
    match goal with
    | [H: ObjInvRs _ _ |- ObjInvRs _ _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct H as [[midx msg] [? ?]];
      exists (midx, msg); split; [|assumption]
    end.

  Ltac solve_by_ObjsInvalid_false roidx :=
    exfalso;
    eapply ObjsInvalid_obj_status_false with (oidx:= roidx); eauto;
    simpl in *; solve_mesi.

  Lemma ObjsInvalid_deq_rqs:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI;
                                   mesiInvRq; mesiInvWRq]) rmsgs ->
        ObjsInvalid inP oss (deqMsgs (idsOf rmsgs) msgs).
  Proof.
    red; intros.
    specialize (H _ H3).
    disc_bind_true.
    case_ObjInvalid.
    - solve_ObjInvalid0.
    - solve_ObjInvRs.
      inv H5.
      apply deqMsgs_InMP; try assumption.
      simpl; intro Hx.
      rewrite Forall_forall in H2; specialize (H2 _ Hx).
      simpl in H2; rewrite H9 in H2.
      intuition discriminate.
  Qed.

  Lemma ObjsInvalid_enq_rqs:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall nmsgs,
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI;
                                   mesiInvRq; mesiInvWRq]) nmsgs ->
        ObjsInvalid inP oss (enqMsgs nmsgs msgs).
  Proof.
    red; intros.
    specialize (H _ H1).
    disc_bind_true.
    case_ObjInvalid.
    - solve_ObjInvalid0.
      apply MsgsP_other_msg_id_enqMsgs; [assumption|].
      simpl.
      apply (DisjList_spec_1 idx_dec); intros midx ?.
      apply in_map_iff in H4; destruct H4 as [[rmidx msg] [? ?]].
      simpl in *; subst.
      rewrite Forall_forall in H0; specialize (H0 _ H5); simpl in H0.
      intro Hx.
      repeat
        match goal with
        | [H: _ \/ _ |- _] => destruct H
        | [H1: _ = msg_id ?msg, H2: _ = msg_id ?msg |- _] =>
          rewrite <-H1 in H2; discriminate
        | [H: False |- False] => auto
        end.
    - solve_ObjInvRs.
      apply InMP_or_enqMsgs; auto.
  Qed.

  Lemma InvExcl_deq_rqs:
    forall oss porqs norqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI;
                                   mesiInvRq; mesiInvWRq]) rmsgs ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := norqs;
                        bst_msgs := deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    disc_bind_true; dest; split.
    - red; intros.
      destruct H5.
      apply MsgsP_other_msg_id_deqMsgs_inv in H6; try assumption.
      + specialize (H (conj H5 H6)); dest; split.
        * apply ObjsInvalid_deq_rqs; auto.
        * solve_MsgsP.
      + simpl.
        apply (DisjList_spec_1 idx_dec); intros midx ?.
        apply in_map_iff in H7; destruct H7 as [[rmidx msg] [? ?]].
        simpl in *; subst.
        rewrite Forall_forall in H2; specialize (H2 _ H8); simpl in H2.
        intro Hx; destruct Hx; [|auto].
        rewrite <-H7 in H2.
        intuition discriminate.
    - red; intros.
      specialize (H4 H5).
      apply ObjsInvalid_deq_rqs; auto.
  Qed.

  Lemma InvExcl_enq_rqs:
    forall oss porqs norqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall nmsgs,
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI;
                                   mesiInvRq; mesiInvWRq]) nmsgs ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := norqs;
                        bst_msgs := enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    disc_bind_true; dest; split.
    - disc_InvObjExcl0; split.
      + apply ObjsInvalid_enq_rqs; auto.
      + apply MsgsP_other_msg_id_enqMsgs; [assumption|].
        simpl.
        apply (DisjList_spec_1 idx_dec); intros midx ?.
        apply in_map_iff in H5; destruct H5 as [[rmidx msg] [? ?]].
        simpl in *; subst.
        rewrite Forall_forall in H0; specialize (H0 _ H6); simpl in H0.
        intro Hx.
        repeat
          match goal with
          | [H: _ \/ _ |- _] => destruct H
          | [H1: _ = msg_id ?msg, H2: _ = msg_id ?msg |- _] =>
            rewrite <-H1 in H2; discriminate
          | [H: False |- False] => auto
          end.
    - red; intros.
      specialize (H2 H3).
      apply ObjsInvalid_enq_rqs; auto.
  Qed.

  Lemma mesi_InvExcl_InvTrs: InvTrs impl (InvExcl topo).
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
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) Hr1) as Hpmcf.

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

        { (* [liGetSImmS] *)
          disc_rule_conds_ex.

          assert (NoRsI oidx msgs).
          { solve_NoRsI_base.
            solve_NoRsI_by_no_uplock oidx.
          }
          
          split.
          { admit. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this.
              { solve_InvObjExcl0_by_ObjExcl0_false. }
              { case_InvObjOwned.
                { solve_by_topo_false. }
                { disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H27.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_false oidx.
              }
              { case_InvObjOwned.
                { solve_by_ObjsInvalid_false oidx. }
                { derive_not_InvalidObj_not_in oidx.
                  disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H29.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }
          }
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex.

          assert (NoRsI oidx msgs).
          { solve_NoRsI_base.
            solve_NoRsI_by_no_uplock oidx.
          }

          split.
          { admit. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this.
              { solve_InvObjExcl0_by_ObjExcl0_false. }
              { case_InvObjOwned.
                { solve_by_topo_false. }
                { disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H27.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_false oidx.
              }
              { case_InvObjOwned.
                { solve_by_ObjsInvalid_false oidx. }
                { derive_not_InvalidObj_not_in oidx.
                  disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H29.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }
          }
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex.
          split.
          { admit. }
          { replace (oss +[oidx <- pos]) with oss by meq.
            repeat
              match goal with
              | [He: InvExcl _ {| bst_orqs := ?orqs |}
                 |- InvExcl _ {| bst_msgs := enqMP ?midx ?msg _ |}] =>
                eapply InvExcl_enq_rqs
                  with (porqs:= orqs) (nmsgs:= [(midx, msg)])
              | [He: InvExcl _ {| bst_orqs := ?orqs |},
                     Hf: FirstMPI _ (?midx, ?msg)
                 |- InvExcl _ {| bst_msgs := deqMP ?midx _ |}] =>
                eapply InvExcl_deq_rqs
                  with (porqs:= orqs) (rmsgs:= [(midx, msg)])
              end; [eassumption|..].
            { repeat constructor; intro; dest_in. }
            { repeat constructor; assumption. }
            { constructor; [|constructor].
              simpl; rewrite H12; tauto.
            }
            { constructor; [|constructor].
              simpl; tauto.
            }
          }
        }
        
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
    InvStep impl step_m (InvExcl topo).
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
    Invariant.InvReachable impl step_m (InvExcl topo).
  Proof.
    apply inv_reachable.
    - apply mesi_InvExcl_init.
    - apply mesi_InvExcl_step.
  Qed.

End InvExcl.

