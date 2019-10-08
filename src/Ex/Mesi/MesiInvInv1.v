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

Definition ObjDirMETo (ost: OState) (cidx: IdxT) :=
  mesiE <= ost#[dir].(dir_st) <= mesiM /\
  ost#[dir].(dir_excl) = cidx.

Lemma getDir_I_ObjDirMETo_false:
  forall oidx (ost: OState),
    getDir oidx (fst (snd (snd (snd ost)))) = mesiI ->
    ObjDirMETo ost oidx -> False.
Proof.
  unfold getDir, ObjDirMETo; intros; dest.
  simpl in H.
  do 2 (find_if_inside; [find_if_inside; [discriminate|auto]|]).
  do 2 (find_if_inside; [simpl in *; solve_mesi|]).
  discriminate.
Qed.

Definition InvDirME (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    _ <+- (bst_oss st)@[oidx]; (* need to know the existence of the child object *)
      _ <+- (bst_orqs st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      (ObjDirMETo post oidx -> NoRsI oidx (bst_msgs st)).

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
    intros; specialize (H H3); dest.

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
        InvDirME topo {| bst_oss := oss;
                         bst_orqs := orqs;
                         bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H1); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    intros; specialize (H H2); dest.
    apply MsgsP_deqMsgs; assumption.
  Qed.

  Lemma InvDirME_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvRs ->
        InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs;
                         bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H1); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    intros.
    apply MsgsP_other_msg_id_enqMP.
    - apply H; auto.
    - simpl; intro Hx.
      destruct Hx; auto.
  Qed.
  
  Lemma InvDirME_other_msg_id_enqMsgs:
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
    apply InvDirME_other_msg_id_enqMP; assumption.
  Qed.

  Lemma InvDirME_deqMP:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx,
        InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs;
                         bst_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvDirME; simpl; intros.
    specialize (H _ _ H0).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    intros; specialize (H H1); dest.
    apply MsgsP_deqMP; assumption.
  Qed.

  Lemma InvDirME_deqMsgs:
    forall oss orqs msgs,
      InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall minds,
        InvDirME topo {| bst_oss:= oss; bst_orqs:= orqs;
                      bst_msgs:= deqMsgs minds msgs |}.
  Proof.
    unfold InvDirME; simpl; intros.
    specialize (H _ _ H0).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    intros; specialize (H H1); dest.
    apply MsgsP_deqMsgs; assumption.
  Qed.

  Ltac simpl_InvDirME_msgs_enqMP :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac simpl_InvDirME_msgs_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    split; simpl_InvDirME_msgs_enqMP.

  Ltac simpl_InvDirME_msgs :=
    repeat
      (first [apply InvDirME_other_msg_id_enqMP; [|simpl_InvDirME_msgs_enqMP..]
             |apply InvDirME_other_msg_id_enqMsgs; [|simpl_InvDirME_msgs_enqMsgs]
             |apply InvDirME_deqMP
             |apply InvDirME_deqMsgs
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

  Ltac disc_InvDirME :=
    repeat
      match goal with
      | [Hi: InvDirME _ _ |- InvDirME _ _] =>
        let Hp := fresh "H" in
        red; simpl; intros ? ? Hp;
        specialize (Hi _ _ Hp); simpl in Hi;
        mred; simpl;
        try (exfalso; eapply parentIdxOf_not_eq; subst topo; eauto; fail)
      | |- _ <+- _; _ => disc_bind_true
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
    (* pose proof (mesi_MsgConflictsInv *)
    (*               (@mesi_RootChnInv_ok _ Htr) *)
    (*               (reachable_steps H (steps_singleton H1))) as Hnmcf. *)
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    (* pose proof (mesi_InvWBDir_ok H) as Hidir. *)
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

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
        
        { (* [liGetSImmME] *)
          disc_rule_conds_ex; disc_InvDirME.
          { Ltac solve_InvDirME_by_silent :=
              intros;
              solve_MsgsP;
              match goal with
              | [H: _ -> NoRsI _ _ |- _] => apply H; auto
              end;
              fail.

              solve_InvDirME_by_silent.
          }
          { intros.
            red in H10; simpl in H10; dest; subst.
            derive_child_idx_in oidx0.
            assert (NoRsI oidx0 msgs)
              by (solve_NoRsI_base; solve_NoRsI_by_rqUp oidx0).
            solve_MsgsP.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { Ltac solve_InvDirME_by_idx_false :=
                intros; subst topo; congruence.
                
                solve_InvDirME_by_idx_false.
            }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { intros.
            red in H10; simpl in H10; dest; subst.
            derive_child_idx_in oidx0.
            assert (NoRsI oidx0 msgs)
              by (solve_NoRsI_base; solve_NoRsI_by_rqUp oidx0).
            solve_MsgsP.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { destruct (idx_dec cidx oidx0); subst.
            { Ltac solve_InvDirME_by_dir_I :=
                intros; exfalso;
                eapply getDir_I_ObjDirMETo_false; eauto.

                solve_InvDirME_by_dir_I.
            }
            { solve_InvDirME_by_silent. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { Ltac solve_InvDirME_by_diff_dir :=
              intros;
              match goal with
              | [Hn: ObjDirMETo _ _ |- _] =>
                red in Hn; dest; simpl in *; solve_mesi
              end.

            solve_InvDirME_by_diff_dir.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { Ltac disc_getDir :=
              try match goal with
                  | [H: getDir _ _ = _ |- _] =>
                    first [apply getDir_M_imp in H; destruct H
                          |apply getDir_E_imp in H; destruct H
                          |apply getDir_S_imp in H; destruct H]
                  | [H: mesiE <= getDir _ _ |- _] =>
                    apply getDir_ME_imp in H; destruct H
                  end.

            disc_getDir.
            solve_InvDirME_by_diff_dir.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { solve_InvDirME_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_dir_I. }
            { solve_InvDirME_by_silent. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { disc_getDir.
            solve_InvDirME_by_diff_dir.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { subst topo; disc_rule_conds_ex. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { solve_InvDirME_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

      }

      dest_in.

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME.
        solve_InvDirME_by_diff_dir.
      }

      { disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirME_msgs.
        disc_InvDirME.

        intros.
        red in H20; simpl in H20; dest; subst.
        derive_child_idx_in oidx0.

        solve_NoRsI_base.

        Ltac solve_NoRsI_by_parent_lock oidx :=
          disc_MsgConflictsInv oidx;
          match goal with
          | [Hmcfp: ParentLockConflicts _ oidx _ _,
                    Hin: InMPI _ (downTo oidx, ?msg) |- _] =>
            specialize (Hmcfp ltac:(red; mred; simpl; eauto));
            destruct Hmcfp as [Hmcfp _];
            eapply (Hmcfp (downTo oidx, msg)); eauto
          end.

        solve_NoRsI_by_parent_lock oidx0.
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

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { intros.
            red in H18; simpl in H18; dest; subst.
            derive_child_idx_in oidx0.
            assert (NoRsI oidx0 msgs)
              by (solve_NoRsI_base; solve_NoRsI_by_rqUp oidx0).
            solve_MsgsP.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { intros.
            red in H18; simpl in H18; dest; subst.
            derive_child_idx_in oidx0.
            assert (NoRsI oidx0 msgs)
              by (solve_NoRsI_base; solve_NoRsI_by_rqUp oidx0).
            solve_MsgsP.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
        { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_dir_I. }
            { solve_InvDirME_by_silent. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { solve_InvDirME_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { disc_getDir.
            solve_InvDirME_by_diff_dir.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { solve_InvDirME_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_dir_I. }
            { solve_InvDirME_by_silent. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { disc_getDir.
            solve_InvDirME_by_diff_dir.
          }
          { destruct (idx_dec cidx oidx0); subst.
            { subst topo; disc_rule_conds_ex. }
            { solve_InvDirME_by_silent. }
          }
        }

        { disc_rule_conds_ex; disc_InvDirME.
          { solve_InvDirME_by_silent. }
          { solve_InvDirME_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_InvDirME_by_idx_false. }
            { solve_InvDirME_by_silent. }
          }
        }

      }

      dest_in.

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME.
        solve_InvDirME_by_diff_dir.
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        simpl_InvDirME_msgs.
        disc_InvDirME.

        intros.
        red in H29; simpl in H29; dest; subst.
        derive_child_idx_in oidx0.
        solve_NoRsI_base.
        solve_NoRsI_by_parent_lock oidx0.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME.
        solve_InvDirME_by_diff_dir.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME.
        solve_InvDirME_by_diff_dir.
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        simpl_InvDirME_msgs.
        disc_InvDirME.

        intros.
        red in H29; simpl in H29; dest; subst.
        derive_child_idx_in oidx0.
        solve_NoRsI_base.
        solve_NoRsI_by_parent_lock oidx0.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }

      { disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirME_msgs.
        disc_InvDirME.

        intros.
        red in H26; simpl in H26; dest; subst.
        derive_child_idx_in oidx0.
        solve_NoRsI_base.
        solve_NoRsI_by_parent_lock oidx0.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME.
        solve_InvDirME_by_diff_dir.
      }

      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      { disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME. }
      
    - (*! Cases for L1 caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Do case analysis per a rule. *)
      dest_in.
      all: disc_rule_conds_ex; simpl_InvDirME_msgs; disc_InvDirME.

      (* END_SKIP_PROOF_OFF *)
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
       (ost#[dir].(dir_st) <= mesiS \/ ObjInvWRq oidx (bst_msgs st)) ->
       mesiS <= ost#[status]).

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
    intros; specialize (H H3); dest.
    split; [assumption|intros].
    destruct H5 as [idm [? ?]].
    apply InMP_enqMsgs_or in H5.
    destruct H5; [|apply H4; auto; do 2 red; eauto].
    apply in_map with (f:= idOf) in H5; simpl in H5.
    apply H1 in H5; simpl in H5.
    exfalso; eapply DisjList_In_1.
    - apply tree2Topo_minds_merqs_disj.
    - eassumption.
    - eapply tree2Topo_obj_chns_minds_SubList.
      + specialize (H0 oidx); simpl in H0.
        rewrite Host in H0; simpl in H0.
        eassumption.
      + destruct idm as [midx msg]; inv H6.
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
    intros; specialize (H H2); dest.
    split; [assumption|intros].
    destruct H4 as [idm [? ?]].
    apply InMP_deqMsgs in H4.
    apply H3; auto.
    do 2 red; eauto.
  Qed.

  Lemma InvWB_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvWB topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvWRq ->
        InvWB topo {| bst_oss:= oss; bst_orqs:= orqs;
                      bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    specialize (H _ _ H1).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros; specialize (H H2); dest.
    split; [assumption|intros].
    apply H3; auto.
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
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvWRq) nmsgs ->
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
    intros; specialize (H H1); dest.
    split; [assumption|intros].
    destruct H3 as [idm [? ?]].
    apply InMP_deqMP in H3.
    apply H2; do 2 red; eauto.
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
    intros; specialize (H H1); dest.
    split; [assumption|intros].
    destruct H3 as [idm [? ?]].
    apply InMP_deqMsgs in H3.
    apply H2; do 2 red; eauto.
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
    simpl_InvWB_msgs_enqMP.

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
        first [match goal with
               | [H: ov = _ |- _] => rewrite H in *; simpl in *
               end
              |let Hov := fresh "H" in
               let v := fresh "v" in
               destruct ov as [v|] eqn:Hov; simpl in *; [|auto]]
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
          mred.
        }

        { disc_rule_conds_ex.
          derive_child_idx_in cidx.
          simpl_InvWB_msgs.
          disc_InvWB.
          { intros; split.
            { intros; red; simpl.
              destruct (fst (snd os)); intuition solve_mesi.
            }
            { assert (NoRqI oidx msgs)
                by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
              solve_InvWB_by_NoRqI.
            }
          }
          { intros.
            red in H17; simpl in H17; dest; subst.
            split.
            {

              Ltac derive_uplock_by_rqUp cidx :=
                disc_MsgConflictsInv cidx;
                (* TODO: must be in [disc_MsgConflictsInv]? *)
                match goal with
                | [Hcf: forall _ _, parentIdxOf _ cidx = Some _ -> _,
                     Hp: parentIdxOf _ cidx = Some ?pidx,
                     Ho: _@[?pidx] = Some _ |- _] =>
                  specialize (Hcf _ _ Hp Ho); destruct Hcf
                end;
                match goal with
                | [H: RqUpConflicts cidx _ _,
                      Hr: FirstMPI _ (rqUpFrom cidx, ?rmsg) |- _] =>
                  specialize (H (rqUpFrom cidx, rmsg) eq_refl (FirstMP_InMP Hr)); dest
                end.

                derive_uplock_by_rqUp oidx0.

                destruct (v0@[upRq]); [intros; discriminate|exfalso; auto].
            }
            { assert (NoRqI oidx0 msgs)
                by (solve_NoRqI_base; solve_NoRqI_by_rqUp oidx0).
              solve_InvWB_by_NoRqI.
            }
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { mred. }
          { solve_InvWB_by_downlock. }
        }

        { disc_rule_conds_ex.
          derive_child_idx_in cidx.
          simpl_InvWB_msgs.
          disc_InvWB.
          { intros; split.
            { intros; red; simpl.
              destruct (fst (snd os)); intuition solve_mesi.
            }
            { assert (NoRqI oidx msgs)
                by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
              solve_InvWB_by_NoRqI.
            }
          }
          { intros.
            red in H17; simpl in H17; dest; subst.
            split.
            { derive_uplock_by_rqUp oidx0.
              destruct (v0@[upRq]); [intros; discriminate|exfalso; auto].
            }
            { assert (NoRqI oidx0 msgs)
                by (solve_NoRqI_base; solve_NoRqI_by_rqUp oidx0).
              solve_InvWB_by_NoRqI.
            }
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { mred. }
          { solve_InvWB_by_downlock. }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { mred. }
          { solve_InvWB_by_downlock. }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          mred.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { intros; split.
            { intros.
              admit.
            }
            { intros; apply H0; auto. }
          }
          { solve_InvWB_by_diff_dir. }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          mred.
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

