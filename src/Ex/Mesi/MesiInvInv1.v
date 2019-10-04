Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Import Ex.Mesi.MesiInv Ex.Mesi.MesiInvInv0.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Definition InvWB (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      orq <+- (bst_orqs st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirME porq post oidx -> ObjInvWRq oidx (bst_msgs st) ->
       ObjOwned ost).

Section InvWB.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvWB_init:
    Invariant.InvInit impl (InvWB topo).
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
    destruct (implORqsInit tr)@[oidx] as [orq|] eqn:Horq; simpl; auto.
    destruct (implOStatesInit tr)@[pidx] as [post|] eqn:Hpost; simpl; auto.
    destruct (implORqsInit tr)@[pidx] as [porq|] eqn:Hporq; simpl; auto.
    split; intros.
    - do 2 (red in H1); dest.
      do 2 (red in H1); dest_in.
    - do 2 (red in H1); dest.
      do 2 (red in H1); dest_in.
  Qed.

  Lemma mesi_InvWB_ext_in:
    forall oss orqs msgs,
      InvWB topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvWB topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H2); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.

    destruct H4 as [idm [? ?]].
    apply InMP_enqMsgs_or in H4.
    destruct H4; [|apply H; auto; do 2 red; eauto].
    apply in_map with (f:= idOf) in H4; simpl in H4.
    apply H1 in H4; simpl in H4.
    exfalso; eapply DisjList_In_1.
    - apply tree2Topo_minds_merqs_disj.
    - eassumption.
    - eapply tree2Topo_obj_chns_minds_SubList.
      + specialize (H0 oidx); simpl in H0.
        rewrite Host in H0; simpl in H0.
        eassumption.
      + destruct idm as [midx msg]; inv H5.
        simpl; tauto.
  Qed.

  Lemma mesi_InvWB_ext_out:
    forall oss orqs msgs,
      InvWB topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        InvWB topo {| bst_oss := oss;
                      bst_orqs := orqs;
                      bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H1); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.

    destruct H3 as [idm [? ?]].
    apply InMP_deqMsgs in H3.
    apply H; auto.
    do 2 red; eauto.
  Qed.

  Lemma InvWB_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvWB topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvWRq ->
        msg.(msg_id) <> mesiInvRq ->
        InvWB topo {| bst_oss:= oss; bst_orqs:= orqs;
                      bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    specialize (H _ _ H2).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.
    
    apply H; auto.
    destruct H4 as [idm [? ?]].
    apply InMP_enqMP_or in H4; destruct H4.
    - dest; subst.
      exfalso; inv H5; auto.
    - do 2 red; eauto.
  Qed.
  
  Lemma InvWB_other_msg_id_enqMsgs:
    forall oss orqs msgs,
      InvWB topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvWRq /\
                           (valOf idm).(msg_id) <> mesiInvRq) nmsgs ->
        InvWB topo {| bst_oss:= oss; bst_orqs:= orqs;
                      bst_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvWB_other_msg_id_enqMP; assumption.
  Qed.

  Lemma InvWB_deqMP:
    forall oss orqs msgs,
      InvWB topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx,
        InvWB topo {| bst_oss:= oss; bst_orqs:= orqs;
                      bst_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    specialize (H _ _ H0).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.

    apply H; auto.
    destruct H2 as [idm [? ?]].
    apply InMP_deqMP in H2.
    do 2 red; eauto.
  Qed.

  Lemma InvWB_deqMsgs:
    forall oss orqs msgs,
      InvWB topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall minds,
        InvWB topo {| bst_oss:= oss; bst_orqs:= orqs;
                      bst_msgs:= deqMsgs minds msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    specialize (H _ _ H0).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.

    intros.
    apply H; auto.
    destruct H2 as [idm [? ?]].
    apply InMP_deqMsgs in H2.
    do 2 red; eauto.
  Qed.

  Ltac simpl_InvWB_msgs_enqMP :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac simpl_InvWB_msgs_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    split; simpl_InvWB_msgs_enqMP.

  Ltac simpl_InvWB_msgs :=
    repeat
      (first [apply InvWB_other_msg_id_enqMP; [|simpl_InvWB_msgs_enqMP..]
             |apply InvWB_other_msg_id_enqMsgs; [|simpl_InvWB_msgs_enqMsgs]
             |apply InvWB_deqMP
             |apply InvWB_deqMsgs
             |assumption]).

  Ltac disc_bind_true :=
    repeat
      match goal with
      | |- _ <+- ?ov; _ =>
        let Hv := fresh "H" in
        let v := fresh "v" in
        destruct ov as [v|] eqn:Hv; simpl in *; [|auto]
      end.

  Ltac disc_InvWB :=
    repeat
      match goal with
      | [Hi: InvWB _ _ |- InvWB _ _] =>
        let Hp := fresh "H" in
        red; simpl; intros ? ? Hp;
        specialize (Hi _ _ Hp); simpl in Hi;
        mred; simpl;
        try (exfalso; eapply parentIdxOf_not_eq; subst topo; eauto; fail)
      | |- _ <+- _; _ => disc_bind_true
      end.

  Ltac solve_InvWB_by_NoRqI :=
    intros;
    repeat
      match goal with
      | [Hn: NoRqI ?oidx ?msgs, Hi: ObjInvWRq ?oidx ?msgs |- _] =>
        exfalso; eapply MsgExistsSig_MsgsNotExist_false;
        [eassumption| |eassumption]; simpl; tauto
      | [Hn: NoRqI ?oidx ?msgs, Hi: ObjInvRq ?oidx ?msgs |- _] =>
        exfalso; eapply MsgExistsSig_MsgsNotExist_false;
        [eassumption| |eassumption]; simpl; tauto
      end.

  Ltac solve_InvWB_by_downlock :=
    intros;
    repeat
      match goal with
      | [Hn: ObjDirME _ _ _ |- _] => red in Hn; dest; mred; fail
      | [Hn: ObjDirE _ _ _ |- _] => red in Hn; dest; mred; fail
      end.

  Ltac solve_InvWB_by_diff_dir :=
    intros;
    match goal with
    | [Hn: ObjDirME _ _ _ |- _] =>
      red in Hn; dest; simpl in *; solve_mesi
    | [Hn: ObjDirE _ _ _ |- _] =>
      red in Hn; dest; simpl in *; solve_mesi
    end.

  Ltac solve_InvWB_by_silent :=
    intros;
    match goal with
    | [H: _ -> _ -> ObjOwned _ |- _] => apply H; try assumption
    end;
    repeat
      match goal with
      | [Hd: ObjDirME _ _ _ |- ObjDirME _ _ _] =>
        red in Hd; dest; simpl in *;
        red; simpl; repeat split; solve [assumption|mred]
      | [Hd: ObjDirE _ _ _ |- ObjDirE _ _ _] =>
        red in Hd; dest; simpl in *;
        red; simpl; repeat split; solve [assumption|mred]
      end.

  Lemma mesi_InvWB_step:
    Invariant.InvStep impl step_m (InvWB topo).
  Proof. (* SKIP_PROOF_OFF *)
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr)
                  (reachable_steps H (steps_singleton H1))) as Hnmcf.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    pose proof (mesi_InvWBDir_ok H) as Hidir.
    inv H1; [assumption
            |apply mesi_InvWB_ext_in; auto
            |apply mesi_InvWB_ext_out; auto
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
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          derive_child_idx_in cidx.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { intros.
            red in H17; simpl in H17; dest; subst.
            assert (NoRqI oidx0 msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_rqUp oidx0).
            solve_InvWB_by_NoRqI.
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_downlock.
        }

        { disc_rule_conds_ex.
          derive_child_idx_in cidx.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { intros.
            red in H17; simpl in H17; dest; subst.
            assert (NoRqI oidx0 msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_rqUp oidx0).
            solve_InvWB_by_NoRqI.
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_downlock.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_downlock.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_diff_dir.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { solve_InvWB_by_diff_dir. }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_diff_dir.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { solve_InvWB_by_diff_dir. }
        }

      }

      dest_in.

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        { disc_MesiDownLockInv oidx Hmdl.
          intros; red in H0; dest; simpl in *; solve_mesi.
        }
        { solve_InvWB_by_diff_dir. }
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        { disc_MesiDownLockInv oidx Hmdl.
          derive_InvWBDir oidx.
          intros; specialize (Hidir (or_introl H18)); simpl in *; solve_mesi.
        }
        { intros.
          assert (NoRqI oidx0 msgs).
          { solve_NoRqI_base.
            (** TODO: need [solve_NoRqI_by_parent_lock] *)
            all: admit.
          }
          solve_InvWB_by_NoRqI.
        }
      }

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

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          derive_child_idx_in cidx.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { intros.
            red in H23; simpl in H23; dest; subst.
            assert (NoRqI oidx0 msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_rqUp oidx0).
            solve_InvWB_by_NoRqI.
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_silent.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_downlock.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_silent.
        }

        { disc_rule_conds_ex.
          derive_child_idx_in cidx.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { intros.
            red in H23; simpl in H23; dest; subst.
            assert (NoRqI oidx0 msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_rqUp oidx0).
            solve_InvWB_by_NoRqI.
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_silent.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_silent.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_silent.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_diff_dir.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { solve_InvWB_by_diff_dir. }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          solve_InvWB_by_diff_dir.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            solve_InvWB_by_NoRqI.
          }
          { solve_InvWB_by_diff_dir. }
        }

      }

      dest_in.

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        simpl_InvWB_msgs.
        disc_InvWB.
        { subst topo; disc_rule_conds_ex.
          assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).
          solve_InvWB_by_NoRqI.
        }
        { solve_InvWB_by_diff_dir. }
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        simpl_InvWB_msgs.
        disc_InvWB.
        { subst topo; disc_rule_conds_ex.
          assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).
          solve_InvWB_by_NoRqI.
        }
        { intros.
          (** TODO: need [solve_NoRqI_by_parent_lock] *)
          all: admit.
        }
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        { disc_MesiDownLockInv oidx Hmdl.
          intros; red in H0; dest; simpl in *; solve_mesi.
        }
        { solve_InvWB_by_diff_dir. }
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        { disc_MesiDownLockInv oidx Hmdl.
          derive_InvWBDir oidx.
          intros; specialize (Hidir (or_introl H25)); simpl in *; solve_mesi.
        }
        { intros.
          assert (NoRqI oidx0 msgs).
          { solve_NoRqI_base.
            (** TODO: need [solve_NoRqI_by_parent_lock] *)
            all: admit.
          }
          solve_InvWB_by_NoRqI.
        }
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.

        Ltac derive_downlock_by_rqDown cidx :=
          disc_MsgConflictsInv cidx;
          (* TODO: must be in [disc_MsgConflictsInv]? *)
          match goal with
          | [Hcf: forall _ _, parentIdxOf _ cidx = Some _ -> _,
               Hp: parentIdxOf _ cidx = Some ?pidx,
               Ho: _@[?pidx] = Some _ |- _] =>
            specialize (Hcf _ _ Hp Ho); destruct Hcf
          end;
          match goal with
          | [H: RqDownConflicts cidx _ _,
                Ht: msg_type ?rmsg = MRq,
                    Hr: FirstMPI _ (downTo cidx, ?rmsg) |- _] =>
            specialize (H (downTo cidx, rmsg) eq_refl Ht (FirstMP_InMP Hr)); dest
          end.

        subst topo; disc_rule_conds_ex.
        intros; derive_downlock_by_rqDown oidx; solve_InvWB_by_downlock.
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        solve_InvWB_by_downlock.
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        solve_InvWB_by_downlock.
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        { (** TODO: need [derive_downlock_by_child_uplock] *)
          all: admit.
        }
        { solve_InvWB_by_diff_dir. }
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        simpl_InvWB_msgs.
        disc_InvWB.
        { assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).
          solve_InvWB_by_NoRqI.
        }
        { (** TODO: need [solve_NoRqI_by_parent_lock] *)
          all: admit.
        }
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        simpl_InvWB_msgs.
        disc_InvWB.
        { assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).
          solve_InvWB_by_NoRqI.
        }
        { solve_InvWB_by_downlock. }
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        { disc_MesiDownLockInv oidx Hmdl.
          derive_InvWBDir oidx.
          intros; specialize (Hidir (or_introl H24)); simpl in *; solve_mesi.
        }
        { intros.
          assert (NoRqI oidx0 msgs).
          { solve_NoRqI_base.
            (** TODO: need [solve_NoRqI_by_parent_lock] *)
            all: admit.
          }
          solve_InvWB_by_NoRqI.
        }
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        subst topo; disc_rule_conds_ex.
        intros; derive_downlock_by_rqDown oidx; solve_InvWB_by_downlock.
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        solve_InvWB_by_downlock.
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        solve_InvWB_by_downlock.
      }

      { disc_rule_conds_ex.
        simpl_InvWB_msgs.
        disc_InvWB.
        { (** TODO: need [derive_downlock_by_child_uplock] *)
          all: admit.
        }
        { solve_InvWB_by_diff_dir. }
      }

      { (** [liInvRqUpUp] *)
        admit.
      }

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

      (* END_SKIP_PROOF_OFF *)
      
  Admitted.

End InvWB.

