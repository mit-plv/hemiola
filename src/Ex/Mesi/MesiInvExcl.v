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

  Lemma mesi_InvExcl_step:
    Invariant.InvStep impl step_m InvExcl.
  Proof.
  Admitted.

  Lemma mesi_InvExcl_ok:
    Invariant.InvReachable impl step_m InvExcl.
  Proof.
    apply inv_reachable.
    - apply mesi_InvExcl_init.
    - apply mesi_InvExcl_step.
  Qed.

End InvExcl.

