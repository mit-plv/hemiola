Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Msi Ex.Msi.Msi Ex.Msi.MsiTopo.

Require Import Ex.Msi.MsiInv Ex.Msi.MsiInvInv0.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Msi.ImplOStateIfc.

Lemma getDir_I_ObjDirMTo_false:
  forall oidx (ost: OState) (orq: ORq Msg),
    getDir oidx (fst (snd (snd (snd ost)))) = msiI ->
    ObjDirM orq ost oidx -> False.
Proof.
  unfold getDir, ObjDirM; intros; dest.
  simpl in H.
  find_if_inside; [find_if_inside; [discriminate|auto]|].
  find_if_inside; [simpl in *; solve_msi|].
  simpl in *; solve_msi.
Qed.

Definition NoRsM (oidx: IdxT) (msgs: MessagePool Msg) :=
  MsgsNotExist [(downTo oidx, (MRs, msiRsM))] msgs.

Definition NoRsSI (oidx: IdxT) (msgs: MessagePool Msg) :=
  MsgsNotExist [(downTo oidx, (MRs, msiRsS));
                  (downTo oidx, (MRs, msiInvRs))] msgs.

Definition ObjInS (ost: OState) (orq: ORq Msg) :=
  (ost#[dir].(dir_st) <= msiI \/
   (ost#[dir].(dir_st) = msiS /\ orq@[downRq] = None)) ->
  msiS <= ost#[status] /\ ost#[owned] = true.

Definition InvDirM (topo: DTree) (st: State): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (st_oss st)@[oidx];
      orq <+- (st_orqs st)@[oidx];
      post <+- (st_oss st)@[pidx];
      porq <+- (st_orqs st)@[pidx];
      (ObjDirM porq post oidx ->
       NoRsM oidx (st_msgs st) ->
       (NoRsSI oidx (st_msgs st) /\ ObjInS ost orq)).

Section InvDirM.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma msi_InvDirM_init:
    Invariant.InvInit impl (InvDirM topo).
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
    destruct (implORqsInit tr)@[oidx] as [orq|] eqn:Horq; simpl; auto.
    destruct (implOStatesInit tr)@[pidx] as [post|] eqn:Hpost; simpl; auto.
    destruct (implORqsInit tr)@[pidx] as [porq|] eqn:Hporq; simpl; auto.
    intros; exfalso.
    red in H0; dest.
    destruct (in_dec idx_dec pidx (c_li_indices cifc ++ c_l1_indices cifc)).
    - subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
      inv i.
      + rewrite implOStatesInit_value_root in Hpost by assumption.
        inv Hpost.
        simpl in *; solve_msi.
      + rewrite implOStatesInit_value_non_root in Hpost by assumption.
        inv Hpost.
        simpl in *; solve_msi.
    - rewrite implOStatesInit_None in Hpost by assumption.
      discriminate.
  Qed.

  Lemma msi_InvDirM_ext_in:
    forall oss orqs msgs,
      InvDirM topo {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvDirM topo {| st_oss := oss; st_orqs := orqs; st_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H2); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.
    apply MsgsP_enqMsgs_inv in H4.
    specialize (H H3 H4); dest.
    split; [|assumption].
    apply MsgsP_other_midx_enqMsgs; [assumption|].
    destruct H1; simpl.
    eapply DisjList_SubList; [eassumption|].
    eapply DisjList_comm, DisjList_SubList.
    - eapply SubList_trans;
        [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
      + solve_SubList.
      + specialize (H0 oidx); simpl in H0.
        rewrite Host in H0; simpl in H0.
        eassumption.
    - apply tree2Topo_minds_merqs_disj.
  Qed.

  Lemma msi_InvDirM_ext_out:
    forall oss orqs msgs,
      InvDirM topo {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvDirM topo {| st_oss := oss;
                        st_orqs := orqs;
                        st_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H2); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.
    apply MsgsP_other_midx_deqMsgs_inv in H4.
    - specialize (H H3 H4); dest.
      split; [|assumption].
      apply MsgsP_deqMsgs; assumption.
    - destruct H1.
      simpl; eapply DisjList_SubList; [eassumption|].
      eapply DisjList_comm, DisjList_SubList.
      + eapply SubList_trans;
          [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
        * solve_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
      + apply tree2Topo_minds_merss_disj.
  Qed.

  Lemma InvDirM_enqMP:
    forall oss orqs msgs,
      InvDirM topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> msiInvRs ->
        msg.(msg_id) <> msiRsS ->
        InvDirM topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= enqMP midx msg msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H2); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.
    apply MsgsP_enqMP_inv in H4.
    specialize (H H3 H4); dest.
    split; [|assumption].
    apply MsgsP_other_msg_id_enqMP.
    - apply H; auto.
    - simpl; intro Hx.
      destruct Hx; auto.
      destruct H6; auto.
  Qed.
  
  Lemma InvDirM_enqMsgs:
    forall oss orqs msgs,
      InvDirM topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> msiInvRs /\
                           (valOf idm).(msg_id) <> msiRsS) nmsgs ->
        InvDirM topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvDirM_enqMP; assumption.
  Qed.

  Lemma InvDirM_deqMP:
    forall oss orqs msgs,
      InvDirM topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall midx msg,
        FirstMP msgs midx msg ->
        msg.(msg_id) <> msiRsM ->
        InvDirM topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvDirM; simpl; intros.
    specialize (H _ _ H2).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.
    eapply MsgsP_other_msg_id_deqMP_inv in H4; [|eassumption|simpl; intro; intuition].
    specialize (H H3 H4); dest.
    split; [|assumption].
    apply MsgsP_deqMP; assumption.
  Qed.

  Lemma InvDirM_deqMsgs:
    forall oss orqs msgs,
      InvDirM topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall rmsgs,
        Forall (FirstMPI msgs) rmsgs ->
        NoDup (idsOf rmsgs) ->
        Forall (fun idm => (valOf idm).(msg_id) <> msiRsM) rmsgs ->
        InvDirM topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    unfold InvDirM; simpl; intros.
    specialize (H _ _ H3).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.
    eapply MsgsP_other_msg_id_deqMsgs_inv in H5; try eassumption.
    - specialize (H H4 H5); dest.
      split; [|assumption].
      apply MsgsP_deqMsgs; assumption.
    - simpl.
      apply (DisjList_spec_1 idx_dec); intros.
      apply in_map_iff in H6; destruct H6 as [idm [? ?]].
      rewrite Forall_forall in H2; specialize (H2 _ H7); dest; subst.
      intro; dest_in; auto.
  Qed.

  Ltac solve_msg :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac solve_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    split; solve_msg.

  Ltac solve_deqMsgs_NoDup :=
    match goal with
    | [H: ValidMsgsIn _ ?msgs |- NoDup (idsOf ?msgs)] => apply H
    end.

  Ltac solve_deqMsgs_msg_id :=
    match goal with
    | [H: Forall (fun _ => msg_id _ = _) ?msgs |- Forall _ ?msgs] =>
      eapply Forall_impl; [|eapply H];
      simpl; intros; split; solve_msg
    end.
  
  Ltac simpl_InvDirM_msgs :=
    try match goal with
        | [Hr: idsOf _ = map fst ?rss |- context [map fst ?rss] ] => rewrite <-Hr
        end;
    repeat
      (first [apply InvDirM_enqMP; [|solve_msg..]
             |apply InvDirM_enqMsgs; [|solve_enqMsgs]
             |eapply InvDirM_deqMP; [|eassumption|solve_msg..]
             |apply InvDirM_deqMsgs; [|eassumption
                                      |solve_deqMsgs_NoDup
                                      |solve_deqMsgs_msg_id]
             |assumption]).

  Ltac disc_pre :=
    repeat
      match goal with
      | [Hi: InvDirM _ _ |- InvDirM _ _] =>
        let Hp := fresh "H" in
        red; simpl; intros ? ? Hp;
        specialize (Hi _ _ Hp); simpl in Hi;
        mred; simpl;
        try (exfalso; eapply parentIdxOf_not_eq; subst topo; eauto; fail)
      | |- _ <+- _; _ => disc_bind_true
      | |- _ -> _ => intros
      | [Hi: ObjDirM _ _ _ -> _, Ho: ObjDirM _ _ _ |- _] =>
        specialize (Hi Ho); dest
      | [Hi: NoRsM _ _ -> _, Hm: NoRsM _ _ |- _] =>
        specialize (Hi Hm); dest
      | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl); dest
      end.

  Ltac disc_NoRsM :=
    repeat
      match goal with
      | [H: ValidMsgsIn _ _ |- _] => destruct H
      | [H: ValidMsgsOut _ _ |- _] => destruct H
      | [Hr: idsOf _ = map fst _, H: NoRsM _ _ |- _] => rewrite <-Hr in H
      end;
    repeat
      match goal with
      | [H: NoRsM _ _ |- _] => disc_MsgsP H
      | [Hi: NoRsM _ ?msgs -> _ /\ _,  Hm: MsgsP _ ?msgs |- _] =>
        specialize (Hi Hm); dest
      end.

  Ltac disc :=
    disc_pre; disc_NoRsM.

  Ltac solve_NoRsSI_by_silent :=
    intros;
    solve_MsgsP;
    match goal with
    | [H: _ -> NoRsSI _ _ |- _] => apply H; auto; fail
    end.

  Ltac solve_ObjInS_valid :=
    try assumption;
    try match goal with
        | |- ObjInS _ _ => red; simpl; intuition solve_msi
        | [Ho:ObjInS _ _ |- ObjInS _ _] =>
          red in Ho; red; simpl in *;
          solve [intuition solve_msi|
                 intros; apply Ho; intuition solve_msi]
        end.

  Ltac disc_ObjDirM :=
    match goal with
    | [H: ObjDirM _ _ _ |- _] =>
      red in H; simpl in H; dest; subst
    end.

  Ltac solve_by_silent :=
    repeat
      match goal with
      | [H: _ -> _ -> ?p |- ?p] => apply H; auto
      | [H: ObjDirM _ _ _ |- ObjDirM _ _ _] => disc_ObjDirM; red; mred
      end.

  Ltac solve_by_NoRsM_false :=
    exfalso;
    match goal with
    | [Hn: NoRsM _ (enqMP ?midx ?msg ?msgs) |- _] =>
      specialize (Hn (midx, msg)
                     (InMP_or_enqMP
                        msgs (or_introl (conj eq_refl eq_refl))));
      red in Hn; unfold map in Hn;
      disc_caseDec Hn; auto
    end.

  Ltac solve_by_idx_false :=
    intros; subst topo; congruence.

  Ltac solve_by_dir_I :=
    intros; exfalso;
    eapply getDir_I_ObjDirMTo_false; eauto.

  Ltac solve_by_diff_dir :=
    intros;
    match goal with
    | [Hn: ObjDirM _ _ _ |- _] =>
      red in Hn; dest; simpl in *; solve_msi
    end.

  Ltac solve_valid :=
    split; [solve_NoRsSI_by_silent
           |disc_getDir; solve_ObjInS_valid].

  Ltac solve_by_NoRsSI_false :=
    exfalso;
    match goal with
    | [Hn: NoRsSI _ ?msgs, Hf: FirstMPI ?msgs (?midx, ?msg) |- _] =>
      specialize (Hn (midx, msg) (FirstMP_InMP Hf));
      solve_MsgsP_false Hn;
      auto
    end.

  Ltac solve_NoRsSI_by_rsDown oidx :=
    disc_MsgConflictsInv oidx;
    apply not_MsgExistsSig_MsgsNotExist;
    intros; dest_in;
    disc_MsgExistsSig;
    solve_RsDown_by_rsDown oidx.

  Ltac solve_by_child_downlock_to_parent oidx :=
    exfalso;
    disc_MsgConflictsInv oidx;
    match goal with
    | [Hp: ParentLockFreeConflicts oidx ?porq ?orq,
           Ho: ?orq@[downRq] = None,
               Hpo: ?porq@[downRq] = Some _ |- _] =>
      specialize (Hp Ho); rewrite Hpo in Hp;
      simpl in Hp; auto
    end.
  
  Lemma msi_InvDirM_step:
    Invariant.InvStep impl step_m (InvDirM topo).
  Proof. (* SKIP_PROOF_OFF *)
    red; intros.
    pose proof (footprints_ok
                  (msi_GoodORqsInit Htr)
                  (msi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (msi_InObjInds H) as Hioi.
    pose proof (msi_MsgConflictsInv
                  (@msi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (msi_InvWBDir_ok H) as Hwd.
    pose proof (MsiDownLockInv_ok H) as Hmdl.
    pose proof (msi_InvL1DirI_ok H) as Hl1d.
    inv H1; [assumption
            |apply msi_InvDirM_ext_in; auto
            |apply msi_InvDirM_ext_out; auto
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

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { disc_rule_conds_ex; disc.
          { split; [solve_NoRsSI_by_silent|].

            (* TODO: automate *)
            red in H22; red; simpl in *.
            intros; apply H22.
            rewrite H14 in *.
            assert (dir_st (fst (snd (snd (snd os)))) <= msiI \/
                    dir_st (fst (snd (snd (snd os)))) = msiS) by solve_msi.
            intuition idtac.
          }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsM; solve_valid.
            red in H22; red; simpl in *.
            intros.
            split; [solve_msi|].
            apply H22.
            left; solve_msi.
          }
          { disc_ObjDirM; discriminate. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsM; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { solve_valid. }
          { disc_ObjDirM; mred. }
        }

        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsM; solve_valid. }
          { disc_ObjDirM.
            solve_by_NoRsM_false.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsM; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { solve_valid. }
          { disc_ObjDirM; mred. }
        }
        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { solve_valid. }
          { disc_ObjDirM; mred. }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_dir_I. }
            { solve_valid. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { disc_getDir; solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_dir_I. }
            { solve_valid. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { disc_getDir; solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

      }

      dest_in.

      { disc_rule_conds_ex.
        disc_MsiDownLockInv oidx Hmdl.
        disc.
        { solve_valid. }
        { solve_by_diff_dir. }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { disc_rule_conds_ex.
        disc_MsiDownLockInv oidx Hmdl.
        disc_pre.
        { disc_NoRsM; solve_valid. }
        { disc_ObjDirM.
          solve_by_NoRsM_false.
        }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { disc_NoRsM; solve_valid. }
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

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { disc_rule_conds_ex; disc.
          { solve_valid.

            (* TODO: automate *)
            red in H28; red; simpl in *.
            intros; apply H28.
            rewrite H20 in *.
            assert (dir_st (fst (snd (snd (snd os)))) <= msiI \/
                    dir_st (fst (snd (snd (snd os)))) = msiS) by solve_msi.
            intuition idtac.
          }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsM; solve_valid.
            red in H28; red; simpl in *.
            intros.
            split; [solve_msi|].
            apply H28.
            left; solve_msi.
          }
          { disc_ObjDirM; discriminate. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsM; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { split; [solve_NoRsSI_by_silent|].
            (* TODO: automate *)
            red in H26; red; simpl in *; mred.
          }
          { solve_by_silent. }
        }
        
        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { solve_valid. }
          { solve_by_silent. }
        }

        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsM; solve_valid. }
          { disc_ObjDirM.
            solve_by_NoRsM_false.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsM; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { split; [solve_NoRsSI_by_silent|].
            (* TODO: automate *)
            red in H26; red; simpl in *; mred.
          }
          { solve_by_silent. }
        }

        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { solve_valid. }
          { solve_by_silent. }
        }
        { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
          { solve_valid. }
          { solve_by_silent. }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_dir_I. }
            { solve_valid. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { disc_getDir; solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_dir_I. }
            { solve_valid. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { disc_getDir; solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

      }

      dest_in.

      { (* [liGetSRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { solve_by_NoRsSI_false. }
        { solve_by_diff_dir. }
        { destruct (idx_dec cidx oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { (* [liDownSRsUpDownM] *)
        disc_rule_conds_ex.
        disc_MsiDownLockInv oidx Hmdl.
        disc.
        { solve_valid. }
        { solve_by_diff_dir. }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { (* [liDownSImm] *)
        disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirM.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { (* [liDownSRqDownDownM] *)
        disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; mred. }
      }

      { (* [liDownSRsUpUp] *)
        disc_rule_conds_ex.
        disc_MsiDownLockInv oidx Hmdl.
        simpl_InvDirM_msgs; disc.
        { disc_ObjDirM.
          remember (dir_excl _) as oidx; clear Heqoidx.
          disc_MsgConflictsInv oidx.
          solve_by_child_downlock_to_parent oidx.
        }
        { solve_by_diff_dir. }
      }

      { (* [liGetMRsDownDownDirI] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc_pre.
        { split.
          { solve_MsgsP; solve_NoRsSI_by_rsDown oidx. }
          { solve_ObjInS_valid. }
        }
        { disc_ObjDirM; solve_by_NoRsM_false. }
        { destruct (idx_dec cidx oidx0); subst.
          { solve_by_idx_false. }
          { disc_NoRsM; solve_valid. }
        }
      }

      { (* [liGetMRsDownRqDownDirS] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        simpl_InvDirM_msgs.
        disc.
        { split.
          { solve_MsgsP.
            solve_NoRsSI_by_rsDown oidx.
          }
          { (* TODO: automate *)
            red; simpl; intros.
            destruct H36; [solve_msi|].
            dest; mred.
          }
        }
        { disc_ObjDirM; mred. }
        { solve_valid. }
      }
      
      { (* [liDownIRsUpDown] *)
        disc_rule_conds_ex.
        disc_MsiDownLockInv oidx Hmdl.
        disc_pre.
        { disc_NoRsM; solve_valid. }
        { disc_ObjDirM; solve_by_NoRsM_false. }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { disc_NoRsM; solve_valid. }
        }
      }

      { (* [liDownIImm] *)
        disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirM.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { (* [liDownIRqDownDownDirS] *)
        disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; mred. }
      }
      { (* [liDownIRqDownDownDirM] *)
        disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; mred. }
      }

      { (* [liDownIRsUpUp] *)
        disc_rule_conds_ex.
        disc_MsiDownLockInv oidx Hmdl.
        simpl_InvDirM_msgs; disc.
        { subst topo; disc_rule_conds_ex.
          disc_ObjDirM.
          remember (dir_excl _) as oidx; clear Heqoidx.
          disc_MsgConflictsInv oidx.
          solve_by_child_downlock_to_parent oidx.
        }
        { solve_by_diff_dir. }
        { split; [solve_NoRsSI_by_silent|assumption]. }
      }

      { (* [liInvRqUpUp] *)
        disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; solve_msi. }
      }

      { (* [liInvRqUpUpWB] *)
        disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; solve_msi. }
      }

      { (* [liInvRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_InvWBDir oidx.
        assert (ObjInvRs oidx msgs) as Hirs.
        { do 2 red.
          eexists; split; [apply FirstMP_InMP; eassumption|].
          unfold sigOf; simpl; congruence.
        }
        specialize (Hwd (or_intror (or_intror Hirs))); clear Hirs.
        derive_footprint_info_basis oidx.
        simpl_InvDirM_msgs.
        disc.
        { exfalso.
          specialize (H0 (downTo oidx, rmsg) (FirstMP_InMP H20)).
          move H0 at bottom.

          (* TODO: fix [solve_by_NoRsSI_false] *)
          red in H0; unfold map in H0.
          rewrite caseDec_head_neq in H0.
          2: {
            unfold sigOf; simpl.
            intro Hx; inv Hx.
            rewrite H21 in H34.
            discriminate.
          }
          rewrite caseDec_head_eq in H0 by (unfold sigOf; simpl; congruence).
          auto.
        }
        { disc_ObjDirM; solve_msi. }
      }

      { (* [liPushImm] *)
        disc_rule_conds_ex; disc.
        split; [solve_NoRsSI_by_silent|].

        red in H24; red; simpl in *; intros; exfalso.
        specialize (H24 H27).
        destruct H27; dest.
        { solve_msi. }
        { congruence. }
      }
      
    - (*! Cases for L1 caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Discharge an invariant that holds only for L1 caches. *)
      red in Hl1d; simpl in Hl1d.
      rewrite Forall_forall in Hl1d; specialize (Hl1d _ H2).
      simpl in H5; rewrite H5 in Hl1d; simpl in Hl1d.

      (** Do case analysis per a rule. *)
      dest_in.

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc. }

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { split; [solve_NoRsSI_by_silent|].
          red in H22; red; simpl in *; mred.
        }
        { solve_by_silent. }
      }
      
      { disc_rule_conds_ex; simpl_InvDirM_msgs.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { solve_by_NoRsSI_false. }
        { solve_by_diff_dir. }
      }

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirM.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc. }

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; solve_msi. }
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc_pre.
        { split.
          { solve_MsgsP; solve_NoRsSI_by_rsDown oidx. }
          { solve_ObjInS_valid. }
        }
        { disc_ObjDirM; solve_msi. }
        { destruct (idx_dec (l1ExtOf oidx) oidx0); subst.
          { exfalso.
            subst topo.
            rewrite tree2Topo_l1_ext_parent in H3 by assumption.
            congruence.
          }
          { disc_NoRsM; solve_valid. }
        }
      }

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirM.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; solve_msi. }
      }

      { disc_rule_conds_ex; simpl_InvDirM_msgs; disc.
        { solve_valid. }
        { disc_ObjDirM; solve_msi. }
      }

      { (* [liInvRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_InvWBDir oidx.
        assert (ObjInvRs oidx msgs) as Hirs.
        { do 2 red.
          eexists; split; [apply FirstMP_InMP; eassumption|].
          unfold sigOf; simpl; congruence.
        }
        specialize (Hwd (or_intror (or_intror Hirs))); clear Hirs.
        derive_footprint_info_basis oidx.
        simpl_InvDirM_msgs.
        disc.
        { exfalso.
          specialize (H0 (downTo oidx, rmsg) (FirstMP_InMP H20)).
          move H0 at bottom.

          (* TODO: fix [solve_by_NoRsSI_false] *)
          red in H0; unfold map in H0.
          rewrite caseDec_head_neq in H0.
          2: {
            unfold sigOf; simpl.
            intro Hx; inv Hx.
            rewrite H21 in H34.
            discriminate.
          }
          rewrite caseDec_head_eq in H0 by (unfold sigOf; simpl; congruence).
          auto.
        }
        { disc_ObjDirM; solve_msi. }
      }
      
      (* END_SKIP_PROOF_OFF *)
  Qed.

  Theorem msi_InvDirM_ok:
    InvReachable impl step_m (InvDirM topo).
  Proof.
    eapply inv_reachable.
    - typeclasses eauto.
    - apply msi_InvDirM_init.
    - apply msi_InvDirM_step.
  Qed.
  
End InvDirM.

Definition InvWB (topo: DTree) (st: State): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (st_oss st)@[oidx];
      orq <+- (st_orqs st)@[oidx];
      post <+- (st_oss st)@[pidx];
      porq <+- (st_orqs st)@[pidx];
      (ObjDirM porq post oidx ->
       ObjInvWRq oidx (st_msgs st) ->
       msiS <= ost#[status]).

Section InvWB.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Theorem msi_InvWB_ok:
    InvReachable impl step_m (InvWB topo).
  Proof.
    red; intros.
    pose proof (msi_InObjInds H) as Ho.
    pose proof (msi_MsgConflictsInv (@msi_RootChnInv_ok _ Htr) H) as Hm.
    pose proof (msi_InvDirM_ok H) as Hd.
    pose proof (msi_InvWBDir_ok H) as Hw.
    red; intros.
    specialize (Ho oidx).
    specialize (Hm oidx).
    specialize (Hd _ _ H0).
    specialize (Hw oidx).

    destruct (st_oss ist)@[oidx] as [ost|] eqn:Host; simpl in *; auto.
    destruct (st_orqs ist)@[oidx] as [orq|] eqn:Horq; simpl in *; auto.
    destruct (st_oss ist)@[pidx] as [post|] eqn:Hpost; simpl in *; auto.
    destruct (st_orqs ist)@[pidx] as [porq|] eqn:Hporq; simpl in *; auto.

    specialize (Hm _ Ho eq_refl); dest.
    intros.
    specialize (Hw (or_introl H7)).

    assert (NoRsM oidx (st_msgs ist)) as Hnrs.
    { destruct H7 as [[rqUp rqm] ?]; dest; inv H8.
      apply not_MsgExistsSig_MsgsNotExist.
      intros; dest_in.
      destruct H9 as [[rsDown rsm] ?]; dest; inv H9.
      specialize (H2 (rqUpFrom oidx, rqm) eq_refl H7); dest.
      eapply H10 with (rsDown:= (downTo oidx, rsm)); eauto.
    }
    specialize (Hd H6 Hnrs); dest.

    red in H9.
    assert (ost#[dir].(dir_st) <= msiI) as Hdi by solve_msi.
    specialize (H9 (or_introl Hdi)).
    destruct H9; dest; simpl in *; solve_msi.
  Qed.

End InvWB.

