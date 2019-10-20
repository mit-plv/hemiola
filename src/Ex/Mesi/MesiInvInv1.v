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

Lemma getDir_I_ObjDirMETo_false:
  forall oidx (ost: OState) (orq: ORq Msg),
    getDir oidx (fst (snd (snd (snd ost)))) = mesiI ->
    ObjDirME orq ost oidx -> False.
Proof.
  unfold getDir, ObjDirME; intros; dest.
  simpl in H.
  do 2 (find_if_inside; [find_if_inside; [discriminate|auto]|]).
  do 2 (find_if_inside; [simpl in *; solve_mesi|]).
  discriminate.
Qed.

Definition NoRsME (oidx: IdxT) (msgs: MessagePool Msg) :=
  MsgsNotExist [(downTo oidx, (MRs, mesiRsM));
                  (downTo oidx, (MRs, mesiRsE))] msgs.

Definition NoRsSI (oidx: IdxT) (msgs: MessagePool Msg) :=
  MsgsNotExist [(downTo oidx, (MRs, mesiRsS));
                  (downTo oidx, (MRs, mesiInvRs))] msgs.

Definition ObjInS (ost: OState) (orq: ORq Msg) :=
  (ost#[dir].(dir_st) <= mesiI \/
   (ost#[dir].(dir_st) = mesiS /\ orq@[downRq] = None)) ->
  (ost#[status] = mesiS /\ ost#[owned] = true) \/
  mesiE <= ost#[status].

Definition InvDirME (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      orq <+- (bst_orqs st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirME porq post oidx ->
       NoRsME oidx (bst_msgs st) ->
       (NoRsSI oidx (bst_msgs st) /\ ObjInS ost orq)).

Section InvDirME.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvDirME_init:
    Invariant.InvInit impl (InvDirME topo).
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
        simpl in *; solve_mesi.
      + rewrite implOStatesInit_value_non_root in Hpost by assumption.
        inv Hpost.
        simpl in *; solve_mesi.
    - rewrite implOStatesInit_None in Hpost by assumption.
      discriminate.
  Qed.

  Lemma mesi_InvDirME_ext_in:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvDirME topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := enqMsgs eins msgs |}.
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

  Lemma mesi_InvDirME_ext_out:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvDirME topo {| bst_oss := oss;
                         bst_orqs := orqs;
                         bst_msgs := deqMsgs (idsOf eouts) msgs |}.
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

  Lemma InvDirME_enqMP:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvRs ->
        msg.(msg_id) <> mesiRsS ->
        InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs;
                         bst_msgs:= enqMP midx msg msgs |}.
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
  
  Lemma InvDirME_enqMsgs:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvRs /\
                           (valOf idm).(msg_id) <> mesiRsS) nmsgs ->
        InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs;
                         bst_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvDirME_enqMP; assumption.
  Qed.

  Lemma InvDirME_deqMP:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        FirstMP msgs midx msg ->
        msg.(msg_id) <> mesiRsM ->
        msg.(msg_id) <> mesiRsE ->
        InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs;
                         bst_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvDirME; simpl; intros.
    specialize (H _ _ H3).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros.
    eapply MsgsP_other_msg_id_deqMP_inv in H5; [|eassumption|simpl; intro; intuition].
    specialize (H H4 H5); dest.
    split; [|assumption].
    apply MsgsP_deqMP; assumption.
  Qed.

  Lemma InvDirME_deqMsgs:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall rmsgs,
        Forall (FirstMPI msgs) rmsgs ->
        NoDup (idsOf rmsgs) ->
        Forall (fun idm => (valOf idm).(msg_id) <> mesiRsM /\
                           (valOf idm).(msg_id) <> mesiRsE) rmsgs ->
        InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs;
                         bst_msgs:= deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    unfold InvDirME; simpl; intros.
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
  
  Ltac simpl_InvDirME_msgs :=
    repeat
      (first [apply InvDirME_enqMP; [|solve_msg..]
             |apply InvDirME_enqMsgs; [|solve_enqMsgs]
             |eapply InvDirME_deqMP; [|eassumption|solve_msg..]
             |apply InvDirME_deqMsgs; [|eassumption
                                       |solve_deqMsgs_NoDup
                                       |solve_deqMsgs_msg_id]
             |assumption]).

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

  Ltac disc_pre :=
    repeat
      match goal with
      | [Hi: InvDirME _ _ |- InvDirME _ _] =>
        let Hp := fresh "H" in
        red; simpl; intros ? ? Hp;
        specialize (Hi _ _ Hp); simpl in Hi;
        mred; simpl;
        try (exfalso; eapply parentIdxOf_not_eq; subst topo; eauto; fail)
      | |- _ <+- _; _ => disc_bind_true
      | |- _ -> _ => intros
      | [Hi: ObjDirME _ _ _ -> _, Ho: ObjDirME _ _ _ |- _] =>
        specialize (Hi Ho); dest
      | [Hi: NoRsME _ _ -> _, Hm: NoRsME _ _ |- _] =>
        specialize (Hi Hm); dest
      | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl); dest
      end.

  Ltac disc_NoRsME :=
    repeat
      match goal with
      | [H: ValidMsgsIn _ _ |- _] => destruct H
      | [H: ValidMsgsOut _ _ |- _] => destruct H
      end;
    repeat
      match goal with
      | [H: NoRsME _ _ |- _] => disc_MsgsP H
      | [Hi: NoRsME _ ?msgs -> _ /\ _,  Hm: MsgsP _ ?msgs |- _] =>
        specialize (Hi Hm); dest
      end.

  Ltac disc :=
    disc_pre; disc_NoRsME.

  Ltac solve_NoRsSI_by_silent :=
    intros;
    solve_MsgsP;
    match goal with
    | [H: _ -> NoRsSI _ _ |- _] => apply H; auto; fail
    end.

  Ltac solve_ObjInS_valid :=
    try assumption;
    try match goal with
        | |- ObjInS _ _ => red; simpl; intuition solve_mesi
        | [Ho:ObjInS _ _ |- ObjInS _ _] =>
          red in Ho; red; simpl in *;
          solve [intuition solve_mesi|
                 intros; apply Ho; intuition solve_mesi]
        end.

  Ltac disc_ObjDirME :=
    match goal with
    | [H: ObjDirME _ _ _ |- _] =>
      red in H; simpl in H; dest; subst
    end.

  Ltac solve_by_silent :=
    repeat
      match goal with
      | [H: _ -> _ -> ?p |- ?p] => apply H; auto
      | [H: ObjDirME _ _ _ |- ObjDirME _ _ _] => disc_ObjDirME; red; mred
      end.

  Ltac solve_by_NoRsME_false :=
    exfalso;
    match goal with
    | [Hn: NoRsME _ (enqMP ?midx ?msg ?msgs) |- _] =>
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
    eapply getDir_I_ObjDirMETo_false; eauto.

  Ltac solve_by_diff_dir :=
    intros;
    match goal with
    | [Hn: ObjDirME _ _ _ |- _] =>
      red in Hn; dest; simpl in *; solve_mesi
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
  
  Lemma mesi_InvDirME_step:
    Invariant.InvStep impl step_m (InvDirME topo).
  Proof. (* SKIP_PROOF_OFF *)
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (mesi_InvWBDir_ok H) as Hwd.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    pose proof (mesi_InvL1DirI_ok H) as Hl1d.
    inv H1; [assumption
            |apply mesi_InvDirME_ext_in; auto
            |apply mesi_InvDirME_ext_out; auto
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
            assert (dir_st (fst (snd (snd (snd os)))) <= mesiI \/
                    dir_st (fst (snd (snd (snd os)))) = mesiS) by solve_mesi.
            intuition idtac.
          }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }
        
        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsME; solve_valid. }
          { disc_ObjDirME.
            solve_by_NoRsME_false.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsME; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
          { solve_valid. }
          { disc_ObjDirME; mred. }
        }

        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsME; solve_valid. }
          { disc_ObjDirME.
            solve_by_NoRsME_false.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsME; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
          { solve_valid. }
          { disc_ObjDirME; mred. }
        }
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
          { solve_valid. }
          { disc_ObjDirME; mred. }
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
          { solve_by_diff_dir. }
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
        disc_MesiDownLockInv oidx Hmdl.
        disc.
        { solve_valid. }
        { solve_by_diff_dir. }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        disc_pre.
        { disc_NoRsME; solve_valid. }
        { disc_ObjDirME.
          solve_by_NoRsME_false.
        }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { disc_NoRsME; solve_valid. }
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
            assert (dir_st (fst (snd (snd (snd os)))) <= mesiI \/
                    dir_st (fst (snd (snd (snd os)))) = mesiS) by solve_mesi.
            intuition idtac.
          }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsME; solve_valid. }
          { disc_ObjDirME.
            solve_by_NoRsME_false.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsME; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
          { split; [solve_NoRsSI_by_silent|].
            (* TODO: automate *)
            red in H26; red; simpl in *; mred.
          }
          { solve_by_silent. }
        }
        
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
          { solve_valid. }
          { solve_by_silent. }
        }

        { disc_rule_conds_ex; disc_pre.
          { disc_NoRsME; solve_valid. }
          { disc_ObjDirME.
            solve_by_NoRsME_false.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { disc_NoRsME; solve_valid. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
          { split; [solve_NoRsSI_by_silent|].
            (* TODO: automate *)
            red in H26; red; simpl in *; mred.
          }
          { solve_by_silent. }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
          { solve_valid. }
          { solve_by_silent. }
        }
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
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
          { solve_by_diff_dir. }
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

      { (* [liGetSRsDownDownS] *)
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

      { (* [liGetSRsDownDownE] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc_pre.
        { split.
          { solve_MsgsP; solve_NoRsSI_by_rsDown oidx. }
          { solve_ObjInS_valid. }
        }
        { disc_ObjDirME; solve_by_NoRsME_false. }
        { destruct (idx_dec cidx oidx0); subst.
          { solve_by_idx_false. }
          { disc_NoRsME; solve_valid. }
        }
      }

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        disc.
        { solve_valid. }
        { solve_by_diff_dir. }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { (* [liDownSImm] *)
        disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirME.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { (* [liDownSRqDownDownME] *)
        disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; mred. }
      }

      { (* [liDownSRsUpUp] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirME_msgs; disc.
        { disc_ObjDirME.
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
        { disc_ObjDirME; solve_by_NoRsME_false. }
        { destruct (idx_dec cidx oidx0); subst.
          { solve_by_idx_false. }
          { disc_NoRsME; solve_valid. }
        }
      }

      { (* [liGetMRsDownRqDownDirS] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        simpl_InvDirME_msgs.
        disc.
        { split.
          { solve_MsgsP.
            solve_NoRsSI_by_rsDown oidx.
          }
          { (* TODO: automate *)
            red; simpl; intros.
            destruct H34; [solve_mesi|].
            dest; mred.
          }
        }
        { disc_ObjDirME; mred. }
        { solve_valid. }
      }
      
      { (* [liDownIRsUpDown] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        disc_pre.
        { disc_NoRsME; solve_valid. }
        { disc_ObjDirME; solve_by_NoRsME_false. }
        { destruct (idx_dec x oidx0); subst.
          { solve_by_idx_false. }
          { disc_NoRsME; solve_valid. }
        }
      }

      { (* [liDownIImm] *)
        disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirME.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { (* [liDownIRqDownDownDirS] *)
        disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; mred. }
      }
      { (* [liDownIRqDownDownDirME] *)
        disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; mred. }
      }

      { (* [liDownIRsUpUp] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirME_msgs; disc.
        { subst topo; disc_rule_conds_ex.
          disc_ObjDirME.
          remember (dir_excl _) as oidx; clear Heqoidx.
          disc_MsgConflictsInv oidx.
          solve_by_child_downlock_to_parent oidx.
        }
        { solve_by_diff_dir. }
      }

      { (* [liInvRqUpUp] *)
        disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; solve_mesi. }
      }

      { (* [liInvRqUpUpWB] *)
        disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; solve_mesi. }
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
        simpl_InvDirME_msgs.
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
        { disc_ObjDirME; solve_mesi. }
      }

      { (* [liPushImm] *)
        disc_rule_conds_ex; disc.
        split; [solve_NoRsSI_by_silent|].

        red in H23; red; simpl in *; intros; exfalso.
        specialize (H23 H26).
        destruct H23; dest.
        { destruct H18; [solve_mesi|dest; congruence]. }
        { destruct H18; solve_mesi. }
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

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc. }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { split; [solve_NoRsSI_by_silent|].
          red in H22; red; simpl in *; mred.
        }
        { solve_by_silent. }
      }
      
      { disc_rule_conds_ex; simpl_InvDirME_msgs.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { solve_by_NoRsSI_false. }
        { solve_by_diff_dir. }
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
        { disc_ObjDirME; solve_mesi. }
        { destruct (idx_dec (l1ExtOf oidx) oidx0); subst.
          { exfalso.
            subst topo.
            rewrite tree2Topo_l1_ext_parent in H3 by assumption.
            congruence.
          }
          { disc_NoRsME; solve_valid. }
        }
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirME.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        solve_valid.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc. }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; solve_mesi. }
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
        { disc_ObjDirME; solve_mesi. }
        { destruct (idx_dec (l1ExtOf oidx) oidx0); subst.
          { exfalso.
            subst topo.
            rewrite tree2Topo_l1_ext_parent in H3 by assumption.
            congruence.
          }
          { disc_NoRsME; solve_valid. }
        }
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirME.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; solve_mesi. }
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc.
        { solve_valid. }
        { disc_ObjDirME; solve_mesi. }
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
        simpl_InvDirME_msgs.
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
        { disc_ObjDirME; solve_mesi. }
      }
      
      (* END_SKIP_PROOF_OFF *)
  Qed.

  Theorem mesi_InvDirME_ok:
    InvReachable impl step_m (InvDirME topo).
  Proof.
    apply inv_reachable.
    - apply mesi_InvDirME_init.
    - apply mesi_InvDirME_step.
  Qed.
  
End InvDirME.

Definition InvWB (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      orq <+- (bst_orqs st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirME porq post oidx ->
       ObjInvWRq oidx (bst_msgs st) ->
       mesiS <= ost#[status]).

Section InvWB.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Theorem mesi_InvWB_ok:
    InvReachable impl step_m (InvWB topo).
  Proof.
    red; intros.
    pose proof (mesi_InObjInds H) as Ho.
    pose proof (mesi_MsgConflictsInv (@mesi_RootChnInv_ok _ Htr) H) as Hm.
    pose proof (mesi_InvDirME_ok H) as Hd.
    pose proof (mesi_InvWBDir_ok H) as Hw.
    red; intros.
    specialize (Ho oidx).
    specialize (Hm oidx).
    specialize (Hd _ _ H0).
    specialize (Hw oidx).

    destruct (bst_oss ist)@[oidx] as [ost|] eqn:Host; simpl in *; auto.
    destruct (bst_orqs ist)@[oidx] as [orq|] eqn:Horq; simpl in *; auto.
    destruct (bst_oss ist)@[pidx] as [post|] eqn:Hpost; simpl in *; auto.
    destruct (bst_orqs ist)@[pidx] as [porq|] eqn:Hporq; simpl in *; auto.

    specialize (Hm _ Ho eq_refl); dest.
    intros.
    specialize (Hw (or_introl H5)).

    assert (NoRsME oidx (bst_msgs ist)) as Hnrs.
    { destruct H5 as [[rqUp rqm] ?]; dest; inv H6.
      apply not_MsgExistsSig_MsgsNotExist.
      intros; dest_in.
      { destruct H7 as [[rsDown rsm] ?]; dest; inv H7.
        specialize (H2 (rqUpFrom oidx, rqm) eq_refl H5); dest.
        eapply H8 with (rsDown:= (downTo oidx, rsm)); eauto.
      }
      { destruct H7 as [[rsDown rsm] ?]; dest; inv H7.
        specialize (H2 (rqUpFrom oidx, rqm) eq_refl H5); dest.
        eapply H8 with (rsDown:= (downTo oidx, rsm)); eauto.
      }
    }
    specialize (Hd H4 Hnrs); dest.

    red in H7.
    assert (ost#[dir].(dir_st) <= mesiI) as Hdi by solve_mesi.
    specialize (H7 (or_introl Hdi)).
    destruct H7; dest; simpl in *; solve_mesi.
  Qed.

End InvWB.

Definition InvNWB (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      orq <+- (bst_orqs st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirE porq post oidx ->
       ObjInvRq oidx (bst_msgs st) ->
       NoRsSI oidx (bst_msgs st) /\ mesiS <= ost#[status]).

Section InvNWB.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Theorem mesi_InvNWB_ok:
    InvReachable impl step_m (InvNWB topo).
  Proof.
    red; intros.
    pose proof (mesi_InObjInds H) as Ho.
    pose proof (mesi_MsgConflictsInv (@mesi_RootChnInv_ok _ Htr) H) as Hm.
    pose proof (mesi_InvDirME_ok H) as Hd.
    pose proof (mesi_InvWBDir_ok H) as Hw.
    red; intros.
    specialize (Ho oidx).
    specialize (Hm oidx).
    specialize (Hd _ _ H0).
    specialize (Hw oidx).

    destruct (bst_oss ist)@[oidx] as [ost|] eqn:Host; simpl in *; auto.
    destruct (bst_orqs ist)@[oidx] as [orq|] eqn:Horq; simpl in *; auto.
    destruct (bst_oss ist)@[pidx] as [post|] eqn:Hpost; simpl in *; auto.
    destruct (bst_orqs ist)@[pidx] as [porq|] eqn:Hporq; simpl in *; auto.

    specialize (Hm _ Ho eq_refl); dest.
    intros.
    specialize (Hw (or_intror (or_introl H5))).

    assert (NoRsME oidx (bst_msgs ist)) as Hnrs.
    { destruct H5 as [[rqUp rqm] ?]; dest; inv H6.
      apply not_MsgExistsSig_MsgsNotExist.
      intros; dest_in.
      { destruct H7 as [[rsDown rsm] ?]; dest; inv H7.
        specialize (H2 (rqUpFrom oidx, rqm) eq_refl H5); dest.
        eapply H8 with (rsDown:= (downTo oidx, rsm)); eauto.
      }
      { destruct H7 as [[rsDown rsm] ?]; dest; inv H7.
        specialize (H2 (rqUpFrom oidx, rqm) eq_refl H5); dest.
        eapply H8 with (rsDown:= (downTo oidx, rsm)); eauto.
      }
    }

    assert (ObjDirME porq post oidx).
    { red in H4; dest.
      red; repeat split; [|assumption..].
      solve_mesi.
    }
    specialize (Hd H6 Hnrs); dest.

    split; [assumption|].
    red in H8.
    assert (ost#[dir].(dir_st) <= mesiI) as Hdi by solve_mesi.
    specialize (H8 (or_introl Hdi)).
    destruct H8; dest; simpl in *; solve_mesi.
  Qed.

End InvNWB.

