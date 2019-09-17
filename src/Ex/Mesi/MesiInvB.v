Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** Move to [TopoTemplate.v] *)
Lemma tree2Topo_root_not_in_tl_li:
  forall tr (Htr: tr <> Node nil) bidx,
    ~ In (rootOf (fst (tree2Topo tr bidx))) (tl (c_li_indices (snd (tree2Topo tr bidx)))).
Proof.
  intros.
  pose proof (tree2Topo_WfCIfc tr bidx).
  destruct H as [? _].
  rewrite c_li_indices_head_rootOf in H by assumption.
  inv H.
  intro Hx; elim H2.
  apply in_or_app; left; assumption.
Qed.

Lemma tree2Topo_root_not_in_l1:
  forall tr (Htr: tr <> Node nil) bidx,
    ~ In (rootOf (fst (tree2Topo tr bidx))) (c_l1_indices (snd (tree2Topo tr bidx))).
Proof.
  intros.
  pose proof (tree2Topo_WfCIfc tr bidx).
  destruct H as [? _].
  rewrite c_li_indices_head_rootOf in H by assumption.
  inv H.
  intro Hx; elim H2.
  apply in_or_app; right; assumption.
Qed.

Lemma tree2Topo_root_not_l1ExtOf:
  forall tr (Htr: tr <> Node nil) bidx oidx,
    In oidx (c_l1_indices (snd (tree2Topo tr bidx))) ->
    l1ExtOf oidx <> rootOf (fst (tree2Topo tr bidx)).
Proof.
  intros.
  assert (In (rqUpFrom (l1ExtOf oidx)) (c_merqs (snd (tree2Topo tr bidx)))).
  { rewrite c_merqs_l1_rqUpFrom.
    apply in_map_iff.
    eexists; repeat split.
    assumption.
  }
  assert (In (rqUpFrom (rootOf (fst (tree2Topo tr bidx))))
             (c_minds (snd (tree2Topo tr bidx)))).
  { eapply tree2Topo_obj_chns_minds_SubList.
    { rewrite c_li_indices_head_rootOf by assumption.
      left; reflexivity.
    }
    { simpl; tauto. }
  }
  intro Hx; rewrite Hx in H0.
  eapply DisjList_In_1; [apply tree2Topo_minds_merqs_disj| |]; eauto.
Qed.

Existing Instance Mesi.ImplOStateIfc.

Section Footprints.
  Variable topo: DTree.

  Definition DownLockFromChild (oidx: IdxT) (rqid: RqInfo Msg) :=
    exists cidx,
      rqid.(rqi_midx_rsb) = Some (downTo cidx) /\
      parentIdxOf topo cidx = Some oidx.

  Definition DownLockFromParent (oidx: IdxT) (rqid: RqInfo Msg) :=
    rqid.(rqi_midx_rsb) = Some (rqUpFrom oidx).

  Definition MesiFootprintsInv (st: MState): Prop :=
    forall oidx,
      orq <+- (bst_orqs st)@[oidx];
        rqid <+- orq@[downRq];
        rmsg <+- rqid.(rqi_msg);
        match case rmsg.(msg_id) on idx_dec default True with
        | mesiRqS: DownLockFromChild oidx rqid
        | mesiRqM: DownLockFromChild oidx rqid
        | mesiDownRqS: DownLockFromParent oidx rqid
        | mesiDownRqI: DownLockFromParent oidx rqid
        end.

End Footprints.

Section FootprintsOk.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Theorem mesi_footprints_ok:
    InvReachable impl step_m (MesiFootprintsInv topo).
  Proof.
  Admitted.

End FootprintsOk.

Ltac exfalso_downlock_from oidx Hinv :=
  specialize (Hinv oidx); simpl in Hinv;
  disc_rule_conds_ex;
  repeat
    match goal with
    | [Hrqi: rqi_msg _ = Some ?msg, Hmsg: msg_id ?msg = _ |- _] =>
      rewrite Hmsg in Hinv; simpl in Hinv
    | [Hdfc: DownLockFromChild _ _ _ |- _] =>
      red in Hdfc; dest; disc_rule_conds_ex
    | [Hdfp: DownLockFromParent _ _ |- _] =>
      red in Hdfp; dest; disc_rule_conds_ex; solve_midx_false
    end.

Section InvProof.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_RootChnInv_init:
    Invariant.InvInit impl (RootChnInv tr 0).
  Proof.
    do 2 (red; simpl).
    intros.
    intro Hx; do 2 (red in Hx).
    dest_in.
  Qed.

  Ltac disc_RootChnInv :=
    intros;
    let Hx := fresh "H" in
    intro Hx;
    repeat
      match goal with
      | [H: In _ (subtreeChildrenIndsOf _ _) |- _] =>
        apply subtreeChildrenIndsOf_parentIdxOf in H; auto
      | [Hm: InMPI (enqMsgs _ _) _ |- _] =>
        apply InMP_enqMsgs_or in Hm; destruct Hm
      | [Hinv: _ -> _ -> ~ InMPI _ _,  Hm: InMP _ _ (deqMsgs _ _) |- _] =>
        apply InMP_deqMsgs in Hm; eapply Hinv; eauto
      | [H: In (idOf ?idm, valOf ?idm) _ |- _] =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        destruct idm as [midx msg]; simpl in *
      end;
    disc_rule_conds_ex.

  Ltac solve_RootChnInv :=
    repeat
      match goal with
      | [H1: In _ ?l, H2: SubList ?l (subtreeChildrenIndsOf _ _) |- _] =>
        apply H2 in H1
      | [H: In _ (subtreeChildrenIndsOf _ _) |- _] =>
        apply subtreeChildrenIndsOf_parentIdxOf in H; auto
      | [H: In _ (map _ _) |- _] => apply in_map_iff in H; dest
      | [H: (_, _) = (_, _) |- _] => inv H
      | [H: _ \/ _ \/ _ |- _] => destruct H as [|[|]]; try discriminate
      | [H: rqUpFrom _ = rqUpFrom _ |- _] => inv H
      | [H: rsUpFrom _ = rsUpFrom _ |- _] => inv H
      | [H: downTo _ = downTo _ |- _] => inv H

      | [H: parentIdxOf _ ?oidx = Some ?oidx |- _] =>
        exfalso; eapply parentIdxOf_not_eq; eauto
      | [H1: ?oidx = rootOf _, H2: parentIdxOf _ ?oidx = Some _ |- _] => rewrite H1 in H2
      | [H: parentIdxOf _ (rootOf _) = Some _ |- _] =>
        eapply parentIdxOf_child_not_root; eauto
      | [H: In (rootOf _) (tl (c_li_indices _)) |- _] =>
        exfalso; eapply tree2Topo_root_not_in_tl_li; eauto
      | [H: In (rootOf _) (c_l1_indices _) |- _] =>
        exfalso; eapply tree2Topo_root_not_in_l1; eauto
      | [H1: In ?oidx (c_l1_indices _), H2: l1ExtOf ?oidx = rootOf _ |- _] =>
        eapply tree2Topo_root_not_l1ExtOf; eauto
      end.

  Lemma mesi_RootChnInv_step:
    Invariant.InvStep impl step_m (RootChnInv tr 0).
  Proof.
    red; intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_footprints_ok H) as Hmftinv.
    inv H1; [assumption|..].

    1: {
      red; simpl; intros.
      intro Hx; apply InMP_enqMsgs_or in Hx.
      destruct Hx; [|eapply H0; eauto].
      apply in_map with (f:= idOf) in H4; simpl in H4.
      apply H3 in H4; simpl in H4.
      eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * rewrite c_li_indices_head_rootOf by assumption.
          left; reflexivity.
        * destruct H1 as [|[|]]; rewrite H1; simpl; tauto.
    }

    1: {
      red; simpl; intros.
      intro Hx; apply InMP_deqMsgs in Hx.
      eapply H0; eauto.
    }

    simpl in H2; destruct H2; [subst|apply in_app_or in H1; destruct H1].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      unfold RootChnInv in *; simpl in *.
      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.
        dest_in; try (disc_RootChnInv; solve_RootChnInv; fail).
      }

      dest_in.
      { disc_RootChnInv.
        red in Hmftinv; simpl in Hmftinv.
        specialize (Hmftinv oidx).
        disc_rule_conds_ex.
        rewrite H4 in Hmftinv.
        simpl in Hmftinv; destruct Hmftinv as [cidx [? ?]].
        rewrite Hidx in H7; inv H7.
        solve_RootChnInv.
      }
      { disc_RootChnInv.
        move Hmftinv at bottom.
        red in Hmftinv; simpl in Hmftinv.
        specialize (Hmftinv oidx).
        disc_rule_conds_ex.
        rewrite H9 in Hmftinv.
        simpl in Hmftinv; destruct Hmftinv as [cidx [? ?]].
        rewrite Hidx in H10; inv H10.
        solve_RootChnInv.
      }

    - (*! Cases for Li caches *)
      unfold RootChnInv in *; simpl in *.

      (** Do case analysis per a rule. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst; simpl in *.
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.
        dest_in; abstract (disc_RootChnInv; solve_RootChnInv; fail).
      }

      dest_in.
      all: try (disc_RootChnInv; solve_RootChnInv; fail).
      all: try (disc_RootChnInv;
                derive_footprint_info_basis oidx;
                derive_child_chns cidx;
                disc_rule_conds_ex;
                solve_RootChnInv;
                fail).
      all: try (disc_RootChnInv;
                derive_footprint_info_basis oidx;
                [|exfalso_downlock_from oidx Hmftinv;
                  derive_child_chns x;
                  solve_midx_false];
                derive_child_chns upCIdx;
                disc_rule_conds_ex;
                solve_RootChnInv;
                fail).

      { disc_RootChnInv.
        derive_footprint_info_basis oidx.
        1: {
          exfalso_downlock_from oidx Hmftinv.
          derive_child_chns (obj_idx upCObj).
          disc_rule_conds_ex.
        }
        eapply edgeDownTo_Some in H10; eauto; dest.
        derive_child_chns oidx.
        disc_rule_conds_ex.
        solve_RootChnInv.
      }
      { disc_RootChnInv.
        derive_footprint_info_basis oidx.
        1: {
          exfalso_downlock_from oidx Hmftinv.
          derive_child_chns (obj_idx upCObj).
          disc_rule_conds_ex.
        }
        eapply edgeDownTo_Some in H17; eauto; dest.
        derive_child_chns oidx.
        disc_rule_conds_ex.
        solve_RootChnInv.
      }

    - (*! Cases for L1 caches *)
      unfold RootChnInv in *; simpl in *.

      (** Do case analysis per a rule. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.
      dest_in; try (disc_RootChnInv; solve_RootChnInv; fail).

      + disc_RootChnInv.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        solve_RootChnInv.
      + disc_RootChnInv.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        solve_RootChnInv.
      + disc_RootChnInv.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        solve_RootChnInv.

        Unshelve.
        all: assumption.
  Qed.

  Theorem mesi_RootChnInv_ok:
    InvReachable impl step_m (RootChnInv tr 0).
  Proof.
    apply inv_reachable.
    - apply mesi_RootChnInv_init.
    - apply mesi_RootChnInv_step.
  Qed.
  
End InvProof.

