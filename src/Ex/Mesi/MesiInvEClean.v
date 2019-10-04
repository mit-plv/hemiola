Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Import Ex.Mesi.MesiInv Ex.Mesi.MesiInvExcl.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Definition ObjStE (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  mesiE = ost#[status] /\ NoRsI oidx msgs.

Definition ObjDirEClean (oss: OStates) (cv: nat) :=
  forall oidx,
    ost <+- oss@[oidx];
      (ost#[dir].(dir_st) = mesiE -> ost#[val] = cv).

Definition InvExclClean (st: MState) :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (ObjStE eidx eost (bst_msgs st) ->
       ObjDirEClean (bst_oss st) eost#[val]).

Existing Instance Mesi.ImplOStateIfc.

Section InvExclClean.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvExclClean_init:
    Invariant.InvInit impl InvExclClean.
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[eidx] as [eost|] eqn:Heost; simpl; auto.
    intros; exfalso.
    hnf in H; dest.
    destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc)).
    - subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
      inv i.
      + rewrite implOStatesInit_value_root in Heost by assumption.
        inv Heost; discriminate.
      + rewrite implOStatesInit_value_non_root in Heost by assumption.
        inv Heost; discriminate.
    - rewrite implOStatesInit_None in Heost by assumption.
      discriminate.
  Qed.

  Lemma mesi_InvExclClean_ext_in:
    forall oss orqs msgs,
      InvExclClean {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvExclClean {| bst_oss := oss;
                        bst_orqs := orqs;
                        bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    intros; apply H.
    red in H2; dest.
    split; [assumption|].
    do 2 (red in H3; red).
    apply MsgsP_enqMsgs_inv in H3; assumption.
  Qed.

  Lemma mesi_InvExclClean_ext_out:
    forall oss orqs msgs,
      InvExclClean {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvExclClean {| bst_oss := oss;
                        bst_orqs := orqs;
                        bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    intros; apply H.
    red in H2; dest.
    split; [assumption|].
    do 2 (red in H3; red).
    eapply MsgsP_other_midx_deqMsgs_inv in H3; [assumption|].

    specialize (H0 eidx); simpl in H0.
    rewrite Heost in H0; simpl in H0.
    simpl.
    apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
    - eapply SubList_trans;
        [|apply tree2Topo_obj_chns_minds_SubList; eauto].
      solve_SubList.
    - destruct H1.
      eapply DisjList_comm, DisjList_SubList; [eassumption|].
      apply DisjList_comm, tree2Topo_minds_merss_disj.
  Qed.

  Lemma InvExclClean_enqMP:
    forall oss orqs msgs,
      InvExclClean {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        InvExclClean {| bst_oss:= oss; bst_orqs:= orqs;
                        bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    intros; apply H.
    red in H0; dest.
    split; [assumption|].
    do 2 (red in H1; red).
    apply MsgsP_enqMP_inv in H1; assumption.
  Qed.

  Lemma InvExclClean_enqMsgs:
    forall oss orqs msgs,
      InvExclClean {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall nmsgs,
        InvExclClean {| bst_oss:= oss; bst_orqs:= orqs;
                        bst_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    intros; apply H.
    red in H0; dest.
    split; [assumption|].
    do 2 (red in H1; red).
    apply MsgsP_enqMsgs_inv in H1; assumption.
  Qed.

  Lemma InvExclClean_other_msg_id_deqMP:
    forall oss orqs msgs,
      InvExclClean {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        FirstMP msgs midx msg ->
        msg.(msg_id) <> mesiInvRs ->
        InvExclClean {| bst_oss:= oss; bst_orqs:= orqs;
                        bst_msgs:= deqMP midx msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    intros; apply H.
    red in H2; dest.
    split; [assumption|].
    do 2 (red in H3; red).
    eapply MsgsP_other_msg_id_deqMP_inv in H3; [eassumption..|].
    simpl; intro Hx; destruct Hx; auto.
  Qed.

  Lemma InvExclClean_other_msg_id_deqMsgs:
    forall oss orqs msgs,
      InvExclClean {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvRs) rmsgs ->
        InvExclClean {| bst_oss:= oss; bst_orqs:= orqs;
                        bst_msgs:= deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    intros; apply H.
    red in H3; dest.
    split; [assumption|].
    do 2 (red in H4; red).
    eapply MsgsP_other_msg_id_deqMsgs_inv in H4; [eassumption..|].
    simpl.
    apply (DisjList_spec_2 idx_dec); intros; dest_in.
    intro Hx.
    apply in_map_iff in Hx; destruct Hx as [[midx msg] ?]; dest; simpl in *.
    rewrite Forall_forall in H2; specialize (H2 _ H6).
    auto.
  Qed.

  Ltac simpl_InvExclClean_msgs_deqMP :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac simpl_InvExclClean_msgs_deqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    split; simpl_InvExclClean_msgs_deqMP.

  Ltac simpl_InvExclClean_msgs :=
    repeat
      (first [apply InvExclClean_enqMP
             |apply InvExclClean_enqMsgs
             |eapply InvExclClean_other_msg_id_deqMP; [|eassumption
                                                       |simpl_InvExclClean_msgs_deqMP]
             |apply InvExclClean_other_msg_id_deqMsgs; [|simpl_InvExclClean_msgs_deqMsgs]
             |assumption]).

  (* Ltac disc_bind_true := *)
  (*   repeat *)
  (*     match goal with *)
  (*     | |- _ <+- ?ov; _ => *)
  (*       let Hv := fresh "H" in *)
  (*       let v := fresh "v" in *)
  (*       destruct ov as [v|] eqn:Hv; simpl in *; [|auto] *)
  (*     end. *)

  (* Ltac disc_InvExclClean := *)
  (*   repeat *)
  (*     match goal with *)
  (*     | [Hi: InvExclClean _ _ |- InvExclClean _ _] => *)
  (*       let Hp := fresh "H" in *)
  (*       red; simpl; intros ? ? Hp; *)
  (*       specialize (Hi _ _ Hp); simpl in Hi; *)
  (*       mred; simpl; *)
  (*       try (exfalso; eapply parentIdxOf_not_eq; subst topo; eauto; fail) *)
  (*     | |- _ <+- _; _ => disc_bind_true *)
  (*     end. *)

  (* Ltac solve_InvExclClean_by_NoRqI := *)
  (*   repeat *)
  (*     match goal with *)
  (*     | [Hn: NoRqI ?oidx ?msgs, Hi: ObjInvWRq ?oidx ?msgs |- _] => *)
  (*       exfalso; eapply MsgExistsSig_MsgsNotExist_false; *)
  (*       [eassumption| |eassumption]; simpl; tauto *)
  (*     | [Hn: NoRqI ?oidx ?msgs, Hi: ObjInvRq ?oidx ?msgs |- _] => *)
  (*       exfalso; eapply MsgExistsSig_MsgsNotExist_false; *)
  (*       [eassumption| |eassumption]; simpl; tauto *)
  (*     end. *)

  (* Ltac solve_InvExclClean_by_downlock := *)
  (*   repeat *)
  (*     match goal with *)
  (*     | [Hn: ObjDirME _ _ _ |- _] => red in Hn; dest; mred; fail *)
  (*     | [Hn: ObjDirE _ _ _ |- _] => red in Hn; dest; mred; fail *)
  (*     end. *)

  (* Ltac solve_InvExclClean_by_diff_dir := *)
  (*   match goal with *)
  (*   | [Hn: ObjDirME _ _ _ |- _] => *)
  (*     red in Hn; dest; simpl in *; solve_mesi *)
  (*   | [Hn: ObjDirE _ _ _ |- _] => *)
  (*     red in Hn; dest; simpl in *; solve_mesi *)
  (*   end. *)

  (* Ltac solve_InvExclClean_by_silent := *)
  (*   match goal with *)
  (*   | [H: (_ -> _ -> ObjOwned _) /\ (_ -> _ -> ObjClean _ /\ _) |- _] => apply H *)
  (*   | [H: _ -> _ -> ObjOwned _ |- _] => apply H *)
  (*   | [H: _ -> _ -> ObjClean _ /\ _ |- _] => apply H *)
  (*   end; *)
  (*   try assumption; *)
  (*   repeat *)
  (*     match goal with *)
  (*     | [Hd: ObjDirME _ _ _ |- ObjDirME _ _ _] => *)
  (*       red in Hd; dest; simpl in *; *)
  (*       red; simpl; repeat split; solve [assumption|mred] *)
  (*     | [Hd: ObjDirE _ _ _ |- ObjDirE _ _ _] => *)
  (*       red in Hd; dest; simpl in *; *)
  (*       red; simpl; repeat split; solve [assumption|mred] *)
  (*     end. *)

  Lemma mesi_InvExclClean_step:
    Invariant.InvStep impl step_m InvExclClean.
  Proof.
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (mesi_InvExcl_ok H) as Hex.
    inv H1; [assumption
            |apply mesi_InvExclClean_ext_in; auto
            |apply mesi_InvExclClean_ext_out; auto
            |].

    simpl in H2; destruct H2; [subst|apply in_app_or in H1; destruct H1].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      assert (In (rootOf (fst (tree2Topo tr 0)))
                 (c_li_indices (snd (tree2Topo tr 0)))) as Hin.
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.
        dest_in.

        { disc_rule_conds_ex.
          simpl_InvExclClean_msgs.

          admit.
        }
        
        all: admit.

      }

      dest_in.
      all: admit.

    - (*! Cases for Li caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst; simpl in *.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_li_indices_tail_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.
      
      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.
        dest_in.
        all: admit.
      }

      dest_in.
      all: admit.

    - (*! Cases for L1 caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Do case analysis per a rule. *)
      dest_in.
      all: admit.
    
  Admitted.

  Lemma mesi_InvExclClean_ok:
    Invariant.InvReachable impl step_m InvExclClean.
  Proof.
    apply inv_reachable.
    - apply mesi_InvExclClean_init.
    - apply mesi_InvExclClean_step.
  Qed.

End InvExclClean.

