Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock.
Require Import RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(* Section RqRsDown. *)
(*   Context {oifc: OStateIfc}. *)
(*   Variables (dtr: DTree) *)
(*             (sys: System oifc). *)
(*   Hypothesis (Hrrs: RqRsSys dtr sys). *)

(*   Definition NoRqRsDown (st: MState oifc) := *)
(*     forall cidx pobj, *)
(*       In pobj sys.(sys_objs) -> *)
(*       parentIdxOf dtr cidx = Some (obj_idx pobj) -> *)
(*       forall down, *)
(*         edgeDownTo dtr cidx = Some down -> *)
(*         forall rqdm rsdm, *)
(*           rqdm.(msg_type) = MRq -> *)
(*           FirstMP st.(bst_msgs) down rqdm -> *)
(*           rsdm.(msg_type) = MRs -> *)
(*           InMP down rsdm st.(bst_msgs) -> *)
(*           False. *)
  
(*   Ltac disc_rule_custom ::= *)
(*     try disc_footprints_ok. *)
  
(*   Lemma noRqRsDown_InvInit: *)
(*     InvInit sys NoRqRsDown. *)
(*   Proof. *)
(*     do 2 red; intros. *)
(*     simpl in *. *)
(*     inv H5. *)
(*   Qed. *)

(*   Lemma noRqRsDown_InvStep: *)
(*     InvStep sys step_m NoRqRsDown. *)
(*   Proof. *)
(*     destruct Hrrs as [? [? ?]]; red; intros. *)
(*     pose proof (footprints_ok H0 H2) as Hftinv. *)
(*     pose proof (downLockInv_ok H0 H H2) as Hdlinv. *)

(*     (* inv_step; simpl in *. *) *)
(*     (* good_rqrs_rule_get rule. *) *)
(*     (* good_rqrs_rule_cases rule. *) *)
(*    Admitted. *)

(* End RsDownBlock. *)

Section RqUpStart.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).
  
  Definition NonRqUpL (lbl: MLabel) :=
    match lbl with
    | RlblEmpty _ => True
    | RlblIns _ => True
    | RlblOuts _ => True
    | RlblInt _ _ _ routs => forall oidxTo, ~ RqUpMsgs dtr oidxTo routs
    end.

  Ltac disc_NonRqUpL :=
    repeat
      match goal with
      | [ |- NonRqUpL _] => red
      | [ |- forall _, ~ RqUpMsgs _ _ _] =>
        let oidxTo := fresh "oidxTo" in
        let Hx := fresh "H" in
        intros oidxTo Hx
      | [H: RqUpMsgs _ _ _ |- _] =>
        let cidx := fresh "cidx" in
        let rqUp := fresh "rqUp" in
        destruct H as [cidx [rqUp ?]]; dest
      | [H: _ :: _ = _ :: _ |- _] => inv H; simpl in *
      | [H1: ?t = MRq, H2: ?t = MRs |- _] => rewrite H1 in H2; discriminate
      end.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok.

  Lemma rqUp_start_ok_base:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      (exists roidx, RqUpMsgs dtr roidx routs) \/
      NonRqUpL (RlblInt oidx ridx rins routs).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      right; disc_NonRqUpL.
    - disc_rule_conds.
      right; disc_NonRqUpL.

    - disc_rule_conds.
      + left.
        pose proof (rqEdgeUpFrom_Some H _ H6).
        destruct H14 as [rsUp [down [pidx ?]]]; dest.
        eexists; red.
        do 2 eexists; eauto.
      + right; disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H20; [|left; reflexivity].
        destruct H20 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
      + right; disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H6; [|left; reflexivity].
        destruct H6 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + right; disc_NonRqUpL.
      + right; disc_NonRqUpL.
      + right; disc_NonRqUpL.

    - disc_rule_conds.
      right; disc_NonRqUpL; subst.
      eapply RqRsDownMatch_rq_rs in H20; [|left; reflexivity].
      destruct H20 as [rcidx [rsUp ?]]; dest.
      solve_midx_false.
  Qed.

  Lemma rqUp_start_ok_end:
    forall rqUp cidx roidx inits ruins pruhst ruouts,
      msg_type (valOf rqUp) = MRq ->
      parentIdxOf dtr cidx = Some roidx ->
      rqEdgeUpFrom dtr cidx = Some (idOf rqUp) ->
      Atomic msg_dec inits ruins pruhst ruouts [rqUp] ->
      forall oidx ridx routs st1 st2,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx [rqUp] routs) st2 ->
        exists ruhst nhst,
          RlblInt oidx ridx [rqUp] routs :: pruhst = nhst ++ ruhst /\
          (ruhst = nil \/
           (exists roidx0 rqUps ruins0 ruouts0,
               RqUpMsgs dtr roidx0 rqUps /\
               Atomic msg_dec inits ruins0 ruhst ruouts0 rqUps /\
               (nhst = nil \/
                (exists nins nouts, Atomic msg_dec rqUps nins nhst nouts routs)))) /\
          Forall NonRqUpL nhst.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H6).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      eexists pruhst, [_].
      repeat ssplit.
      + reflexivity.
      + right; do 4 eexists.
        repeat ssplit; try eassumption.
        * red; do 2 eexists.
          repeat ssplit; eauto.
        * right; do 2 eexists.
          econstructor.
      + constructor; [|constructor].
        disc_NonRqUpL; subst.

    - exfalso; disc_rule_conds.
      solve_midx_false.

    - disc_rule_conds.
      + eexists (_ :: pruhst), nil.
        repeat ssplit.
        * reflexivity.
        * right.
          pose proof (rqEdgeUpFrom_Some H _ H11).
          destruct H7 as [rsUp [down [pidx ?]]]; dest.
          exists pidx, [(rqTo, rqtm)]; do 2 eexists.
          repeat ssplit.
          { red; do 2 eexists.
            repeat ssplit; eauto.
          }
          { econstructor; try reflexivity; try eassumption.
            { discriminate. }
            { apply SubList_refl. }
            { rewrite removeL_nil; reflexivity. }
          }
          { left; reflexivity. }
        * constructor.
      + eexists pruhst, [_].
        repeat ssplit.
        * reflexivity.
        * right; do 4 eexists.
          repeat ssplit; try eassumption.
          { red; do 2 eexists.
            repeat ssplit; eauto.
          }
          { right; do 2 eexists.
            econstructor.
          }
        * constructor; [|constructor].
          disc_NonRqUpL; subst.
          eapply RqRsDownMatch_rq_rs in H27; [|left; reflexivity].
          destruct H27 as [rcidx [rsUp ?]]; dest.
          solve_midx_false.
      + exfalso; solve_midx_false.

    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds.
  Qed.

  Lemma nonRqUpL_label_outs_no_rqUp:
    forall oidx ridx rins routs st1 st2,
      Reachable (steps step_m) sys st1 ->
      NonRqUpL (RlblInt oidx ridx rins routs) ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      Forall (fun out => forall oidxTo, ~ RqUpMsgs dtr oidxTo [out]) routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2) as Hfinv.
    inv_step.
    
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      repeat constructor.
      disc_NonRqUpL.
    - disc_rule_conds.
      repeat constructor.
      disc_NonRqUpL.
    - disc_rule_conds.
      + pose proof (rqEdgeUpFrom_Some H _ H6).
        destruct H14 as [rsUp [down [pidx ?]]]; dest.
        elim (H3 pidx).
        do 2 eexists; eauto.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H5; simpl in H5.
        disc_NonRqUpL.
        eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
        destruct H20 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H7; simpl in H7.
        disc_NonRqUpL.
        eapply RqRsDownMatch_rq_rs in H6; [|eassumption].
        destruct H6 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
    - good_footprint_get (obj_idx obj).
      disc_rule_conds;
        try (repeat constructor; disc_NonRqUpL; fail).
    - disc_rule_conds.
      apply Forall_forall; intros [midx msg] ?.
      apply in_map with (f:= idOf) in H5; simpl in H5.
      disc_NonRqUpL.
      eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
      destruct H20 as [rcidx [rsUp ?]]; dest.
      solve_midx_false.
  Qed.

  Lemma nonRqUpL_atomic_msg_outs_no_rqUp:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      Forall NonRqUpL hst ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall st2,
          steps step_m sys st1 hst st2 ->
          Forall (fun eout => forall oidxTo, ~ RqUpMsgs dtr oidxTo [eout]) eouts.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps.
      inv H.
      eapply nonRqUpL_label_outs_no_rqUp; eauto.
    - inv_steps.
      inv H5.
      apply Forall_app.
      + apply forall_removeL; eauto.
      + eapply nonRqUpL_label_outs_no_rqUp;
          try eapply H10; eauto.
  Qed.

  Lemma nonRqUp_ins_nonRqUpL:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      Forall (fun rin => forall oidxTo, ~ RqUpMsgs dtr oidxTo [rin]) rins ->
      NonRqUpL (RlblInt oidx ridx rins routs).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds; disc_NonRqUpL.
    - disc_rule_conds; disc_NonRqUpL.
    - disc_rule_conds.
      + elim (H24 (obj_idx obj)).
        do 2 eexists; eauto.
      + disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H21; [|left; reflexivity].
        destruct H21 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
      + disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H7; [|left; reflexivity].
        destruct H7 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
    - disc_rule_conds; disc_NonRqUpL.
    - disc_rule_conds.
      disc_NonRqUpL; subst.
      eapply RqRsDownMatch_rq_rs in H21; [|left; reflexivity].
      destruct H21 as [rcidx [rsUp ?]]; dest.
      solve_midx_false.
  Qed.

  Lemma rqUp_start_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        exists ruhst nhst,
          hst = nhst ++ ruhst /\
          (ruhst = nil \/
           exists roidx rqUps ruins ruouts,
             RqUpMsgs dtr roidx rqUps /\
             Atomic msg_dec inits ruins ruhst ruouts rqUps /\
             (nhst = nil \/
              exists nins nouts, Atomic msg_dec rqUps nins nhst nouts eouts)) /\
          Forall NonRqUpL nhst.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.

    - inv_steps.
      eapply rqUp_start_ok_base in H9; [|eassumption].
      destruct H9.
      + destruct H3 as [roidx ?].
        eexists; exists nil.
        repeat ssplit.
        * reflexivity.
        * right; do 4 eexists.
          repeat ssplit; eauto.
          econstructor.
        * constructor.
      + exists nil; eexists.
        repeat ssplit.
        * rewrite app_nil_r; reflexivity.
        * left; reflexivity.
        * constructor; auto.

    - inv_steps.
      specialize (IHAtomic _ _ H8 H10).
      destruct IHAtomic as [pruhst [pnhst ?]]; dest; subst.
      destruct H6; subst.

      + exists nil.
        exists (RlblInt oidx ridx rins routs :: pnhst).
        repeat rewrite app_nil_r in *.
        repeat ssplit.
        * reflexivity.
        * left; reflexivity.
        * constructor; [|assumption].
          eapply nonRqUpL_atomic_msg_outs_no_rqUp in H2; try eassumption.
          eapply SubList_forall in H4; [|eassumption].
          assert (Reachable (steps step_m) sys st3) by eauto; clear H8.
          eapply nonRqUp_ins_nonRqUpL; eauto.

      + destruct H5 as [roidx [rqUps [ruins [ruouts ?]]]]; dest.
        destruct H9; subst.

        * simpl in *.
          pose proof (atomic_unique H2 H6); dest; subst; clear H2.
          red in H5; destruct H5 as [cidx [rqUp ?]]; dest; subst.
          assert (rins = [rqUp]); subst.
          { inv_step; inv H23.
            destruct rins; [elim H3; reflexivity|].
            pose proof (H4 i (or_introl eq_refl)); Common.dest_in.
            destruct rins; [reflexivity|].
            specialize (H4 i0 (or_intror (or_introl eq_refl))); Common.dest_in.
            red in H12; simpl in H12.
            inv H12; elim H15; left; reflexivity.
          }
          pose proof (reachable_steps H8 H10).
          rewrite removeL_nil; simpl.
          eapply rqUp_start_ok_end; eauto.

        * destruct H9 as [pnins [pnouts ?]].
          exists pruhst, (RlblInt oidx ridx rins routs :: pnhst).
          repeat ssplit.
          { reflexivity. }
          { right; exists roidx, rqUps, ruins, ruouts.
            repeat ssplit; try assumption.
            right; do 2 eexists.
            econstructor; eauto.
          }
          { constructor; [|assumption].
            assert (Reachable (steps step_m) sys st3) by eauto.
            eapply steps_split in H10; [|reflexivity].
            destruct H10 as [sti [? ?]].
            eapply nonRqUpL_atomic_msg_outs_no_rqUp in H9;
              [|assumption
               |eapply reachable_steps; [|eapply H10]; assumption
               |eassumption].
            eapply SubList_forall in H4; [|eassumption].
            eapply nonRqUp_ins_nonRqUpL; try eapply H12; eauto.
          }
  Qed.

End RqUpStart.

Lemma parent_parent_in_False:
  forall dtr (Hwf: WfDTree dtr) oidx1 oidx2 oidx3,
    parentIdxOf dtr oidx1 = Some oidx2 ->
    parentIdxOf dtr oidx2 = Some oidx3 ->
    In oidx3 (subtreeIndsOf dtr oidx1) ->
    False.
Proof.
  intros.
  pose proof (subtreeIndsOf_child_in Hwf _ H).
  pose proof (subtreeIndsOf_child_SubList Hwf _ H0).
  apply H3 in H2.
  pose proof (subtreeIndsOf_In_each_other_eq Hwf _ _ H1 H2); subst.
  eapply parentIdxOf_asym; eassumption.
Qed.

Section Separation.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

  Definition RqRsMsgFrom (oidx: IdxT) (idm: Id Msg) :=
    rqEdgeUpFrom dtr oidx = Some (idOf idm) \/
    rsEdgeUpFrom dtr oidx = Some (idOf idm) \/
    (exists cidx,
        parentIdxOf dtr cidx = Some oidx /\
        edgeDownTo dtr cidx = Some (idOf idm)).

  Lemma RqRsMsgFrom_rqEdgeUpFrom_eq:
    forall oidx1 oidx2 midx msg,
      RqRsMsgFrom oidx1 (midx, msg) ->
      rqEdgeUpFrom dtr oidx2 = Some midx ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - repeat disc_rule_minds; auto.
    - solve_midx_false.
    - destruct H2 as [cidx [? ?]].
      solve_midx_false.
  Qed.

  Lemma RqRsMsgFrom_rsEdgeUpFrom_eq:
    forall oidx1 oidx2 midx msg,
      RqRsMsgFrom oidx1 (midx, msg) ->
      rsEdgeUpFrom dtr oidx2 = Some midx ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - solve_midx_false.
    - repeat disc_rule_minds; auto.
    - destruct H2 as [cidx [? ?]].
      solve_midx_false.
  Qed.

  Lemma RqRsMsgFrom_edgeDownTo_eq:
    forall oidx1 cidx oidx2 midx msg,
      RqRsMsgFrom oidx1 (midx, msg) ->
      edgeDownTo dtr cidx = Some midx ->
      parentIdxOf dtr cidx = Some oidx2 ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - solve_midx_false.
    - solve_midx_false.
    - destruct H2 as [rcidx [? ?]].
      repeat disc_rule_minds; auto.
  Qed.

  Ltac disc_RqRsMsgFrom :=
    match goal with
    | [H: exists _, RqRsMsgFrom _ _ /\ _ |- _] =>
      let oidx := fresh "oidx" in
      destruct H as [oidx [? ?]]
    | [H1: rqEdgeUpFrom _ ?oidx1 = Some ?rqUp,
       H2: RqRsMsgFrom ?oidx2 (?rqUp, _) |- _] =>
      eapply RqRsMsgFrom_rqEdgeUpFrom_eq in H2; [|eapply H1]; subst
    | [H1: rsEdgeUpFrom _ ?oidx1 = Some ?rsUp,
       H2: RqRsMsgFrom ?oidx2 (?rsUp, _) |- _] =>
      eapply RqRsMsgFrom_rsEdgeUpFrom_eq in H2; [|eapply H1]; subst
    | [H1: edgeDownTo _ ?cidx = Some ?down,
       H2: parentIdxOf _ ?cidx = Some ?oidx1,
       H3: RqRsMsgFrom ?oidx2 (?down, _) |- _] =>
      eapply RqRsMsgFrom_edgeDownTo_eq in H3; [|eapply H1|eapply H2]; subst
    end.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_RqRsMsgFrom.
  
  Lemma step_msg_outs:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      Forall (RqRsMsgFrom oidx) routs.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.
    - disc_rule_conds.
      constructor; [|constructor].
      right; right; eauto.
    - disc_rule_conds.
      constructor; [|constructor].
      right; left; eauto.
    - disc_rule_conds.
      + constructor; [|constructor].
        left; eauto.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H5.
        eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
        destruct H20 as [cidx [rsUp ?]]; dest.
        right; right; eauto.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H7.
        eapply RqRsDownMatch_rq_rs in H6; [|eassumption].
        destruct H6 as [cidx [rsUp ?]]; dest.
        right; right; eauto.
    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + constructor; [|constructor].
        right; right; eauto.
      + constructor; [|constructor].
        right; right; eauto.
      + constructor; [|constructor].
        right; left; eauto.
    - disc_rule_conds.
      apply Forall_forall; intros [midx msg] ?.
      apply in_map with (f:= idOf) in H5.
      eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
      destruct H20 as [cidx [rsUp ?]]; dest.
      right; right; eauto.
  Qed.

  Lemma atomic_msg_outs_bounded:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cover,
          SubList (oindsOf hst) cover ->
          Forall (fun eout =>
                    exists oidx,
                      RqRsMsgFrom oidx eout /\ In oidx cover) eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - inv_steps.
      apply step_msg_outs in H10; [|assumption].
      eapply Forall_impl; [|eassumption].
      intros idm ?.
      exists oidx; split; auto.
      apply SubList_singleton_In; assumption.
    - inv_steps.
      apply SubList_cons_inv in H10; dest.
      specialize (IHAtomic _ _ H8 H11 _ H6).
      apply Forall_app.
      + apply forall_removeL; assumption.
      + apply step_msg_outs in H13; [|eauto].
        eapply Forall_impl; [|eassumption].
        intros idm ?.
        exists oidx; split; auto.
  Qed.

  Corollary atomic_msg_outs_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        Forall (fun eout =>
                  exists oidx,
                    RqRsMsgFrom oidx eout /\ In oidx (oindsOf hst)) eouts.
  Proof.
    intros.
    eapply atomic_msg_outs_bounded in H; try eassumption.
    apply SubList_refl.
  Qed.

  Corollary atomic_rqUp_out_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rqUp,
          rqEdgeUpFrom dtr oidx = Some rqUp ->
          In rqUp (idsOf eouts) ->
          In oidx (oindsOf hst).
  Proof.
    intros.
    eapply atomic_msg_outs_in_history in H; try eassumption.
    apply in_map_iff in H3; destruct H3 as [[rrqUp rqm] [? ?]].
    simpl in *; subst.
    rewrite Forall_forall in H.
    specialize (H _ H4); destruct H as [roidx [? ?]].
    disc_RqRsMsgFrom; assumption.
  Qed.

  Corollary atomic_rsUp_out_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rsUp,
          rsEdgeUpFrom dtr oidx = Some rsUp ->
          In rsUp (idsOf eouts) ->
          In oidx (oindsOf hst).
  Proof.
    intros.
    eapply atomic_msg_outs_in_history in H; try eassumption.
    apply in_map_iff in H3; destruct H3 as [[rrsUp rsm] [? ?]].
    simpl in *; subst.
    rewrite Forall_forall in H.
    specialize (H _ H4); destruct H as [roidx [? ?]].
    disc_RqRsMsgFrom; assumption.
  Qed.

  Corollary atomic_down_out_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall pidx oidx down,
          edgeDownTo dtr oidx = Some down ->
          parentIdxOf dtr oidx = Some pidx ->
          In down (idsOf eouts) ->
          In pidx (oindsOf hst).
  Proof.
    intros.
    eapply atomic_msg_outs_in_history in H; try eassumption.
    apply in_map_iff in H4; destruct H4 as [[rdown dm] [? ?]].
    simpl in *; subst.
    rewrite Forall_forall in H.
    specialize (H _ H5); destruct H as [roidx [? ?]].
    disc_RqRsMsgFrom; assumption.
  Qed.
  
  Lemma atomic_msg_outs_disj:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cover,
          DisjList (oindsOf hst) cover ->
          Forall (fun eout =>
                    exists oidx,
                      RqRsMsgFrom oidx eout /\ ~ In oidx cover) eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - inv_steps.
      apply step_msg_outs in H10; [|assumption].
      eapply Forall_impl; [|eassumption].
      intros idm ?.
      exists oidx; split; auto.
      specialize (H4 oidx); destruct H4; auto.
      elim H4; left; reflexivity.
    - inv_steps.
      apply DisjList_cons in H10; dest.
      specialize (IHAtomic _ _ H8 H11 _ H6).
      apply Forall_app.
      + apply forall_removeL; assumption.
      + apply step_msg_outs in H13; [|eauto].
        eapply Forall_impl; [|eassumption].
        intros idm ?.
        exists oidx; split; auto.
  Qed.

  (*! Separation by an unvisited object *)
  
  Lemma step_separation_inside_child_ok:
    forall cidx oidx pidx,
      parentIdxOf dtr cidx = Some pidx ->
      oidx <> pidx ->
      forall st1 st2 ridx rins routs,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        Forall
          (fun eout =>
             exists oidx,
               RqRsMsgFrom oidx eout /\
               In oidx (subtreeIndsOf dtr cidx)) rins ->
        In oidx (subtreeIndsOf dtr cidx).
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    pose proof (footprints_ok H0 H4).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.
    - disc_rule_conds.
      destruct H.
      eapply inside_parent_in; try eapply H; try eassumption.
      intro Hx; subst.
      disc_rule_conds; auto.
    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H26).
      destruct H.
      destruct H8 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_RqRsMsgFrom.
      eapply inside_child_in in H21; try eassumption.

    - disc_rule_conds.
      + destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.
      + destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.
      + pose proof (edgeDownTo_Some H _ H5).
        destruct H.
        destruct H14 as [rqUp [rsUp [rpidx ?]]]; dest.
        disc_RqRsMsgFrom.
        eapply inside_child_in in H10; try eassumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct i as [midx msg]; simpl in *.
        pose proof (edgeDownTo_Some H _ H11).
        destruct H21 as [rqUp [rsUp [rpidx ?]]]; dest.
        destruct H.
        disc_RqRsMsgFrom.
        eapply inside_child_in in H28; try eassumption.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   In rcidx (subtreeIndsOf dtr cidx)).
        { rewrite <-H32 in H25.
          pose proof (RqRsDownMatch_rs_not_nil H25).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H25; [|left; reflexivity].
          destruct H25 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H6; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H9 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   In rcidx (subtreeIndsOf dtr cidx)).
        { rewrite <-H32 in H10.
          pose proof (RqRsDownMatch_rs_not_nil H10).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H10; [|left; reflexivity].
          destruct H10 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H6; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H14 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H34).
      destruct H.
      destruct H6 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_RqRsMsgFrom.
      eapply inside_child_in in H25; try eassumption.
  Qed.

  Lemma step_separation_outside_ok:
    forall soidx oidx,
      oidx <> soidx ->
      forall st1 st2 ridx rins routs,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        Forall
          (fun eout =>
             exists oidx,
               RqRsMsgFrom oidx eout /\
               ~ In oidx (subtreeIndsOf dtr soidx)) rins ->
        ~ In oidx (subtreeIndsOf dtr soidx).
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    pose proof (footprints_ok H0 H3).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      destruct H.
      eapply outside_parent_out in H5; try eassumption.
    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H25).
      destruct H.
      destruct H7 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_rule_conds.
      eapply outside_child_in in H5; try eassumption.
      clear -H2 H5; firstorder.

    - disc_rule_conds.
      + destruct H; eapply outside_parent_out in H16; try eassumption.
      + destruct H; eapply outside_parent_out in H7; try eassumption.
      + pose proof (edgeDownTo_Some H _ H4).
        destruct H.
        destruct H13 as [rqUp [rsUp [rpidx ?]]]; dest.
        disc_rule_conds.
        eapply outside_child_in in H9; try eassumption.
        clear -H2 H9; firstorder.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct i as [midx msg]; simpl in *.
        pose proof (edgeDownTo_Some H _ H10).
        destruct H20 as [rqUp [rsUp [rpidx ?]]]; dest.
        destruct H.
        disc_rule_conds.
        eapply outside_child_in in H27; try eassumption.
        clear -H2 H27; firstorder.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   ~ In rcidx (subtreeIndsOf dtr soidx)).
        { rewrite <-H31 in H24.
          pose proof (RqRsDownMatch_rs_not_nil H24).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H24; [|left; reflexivity].
          destruct H24 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H5; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H8 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply outside_parent_out in H29; try eassumption.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   ~ In rcidx (subtreeIndsOf dtr soidx)).
        { rewrite <-H31 in H9.
          pose proof (RqRsDownMatch_rs_not_nil H9).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H9; [|left; reflexivity].
          destruct H9 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H5; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H13 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply outside_parent_out in H25; try eassumption.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H33).
      destruct H.
      destruct H5 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_rule_conds.
      eapply outside_child_in in H24; try eassumption.
      clear -H2 H24; firstorder.
  Qed.
  
  Lemma atomic_separation_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall soidx,
          ~ In soidx (oindsOf hst) ->
          (exists cidx,
              parentIdxOf dtr cidx = Some soidx /\
              SubList (oindsOf hst) (subtreeIndsOf dtr cidx)) \/
          DisjList (oindsOf hst) (subtreeIndsOf dtr soidx).
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - destruct (in_dec eq_nat_dec oidx (subtreeIndsOf dtr soidx)).
      + left.
        destruct H.
        eapply subtreeIndsOf_composed in i; [|assumption].
        destruct i; subst; [intuition idtac|].
        destruct H6 as [cidx [? ?]].
        exists cidx; split; auto.
        apply SubList_cons; [assumption|apply SubList_nil].
      + right; apply (DisjList_singleton_1 eq_nat_dec); assumption.
    - inv_steps.
      assert (oidx <> soidx /\ ~ In soidx (oindsOf hst)) by intuition idtac.
      dest.
      specialize (IHAtomic _ _ H8 H11 _ H6).
      destruct IHAtomic.
      + destruct H7 as [cidx ?]; dest.
        pose proof (atomic_msg_outs_bounded H2 H8 H11 H9).
        left; exists cidx.
        split; [assumption|].
        apply SubList_cons; [|assumption].
        eapply SubList_forall in H12; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_inside_child_ok; eauto.
      + pose proof (atomic_msg_outs_disj H2 H8 H11 H7).
        right.
        apply (DisjList_cons_inv eq_nat_dec); [assumption|].
        specialize (H7 oidx); destruct H7; [|assumption].
        eapply SubList_forall in H9; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_outside_ok; eauto.
  Qed.

  (** This lemma is a bit freaky but crucially used in the proof of 
   * the coverage invariant.
   *)
  Lemma atomic_non_visiting_rsUps_one:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall ruTo rsUps,
          ~ In ruTo (oindsOf hst) ->
          rsUps <> nil ->
          NoDup (idsOf rsUps) ->
          Forall (fun msg =>
                    exists cidx,
                      parentIdxOf dtr cidx = Some ruTo /\
                      rsEdgeUpFrom dtr cidx = Some (idOf msg)) rsUps ->
          SubList rsUps eouts ->
          exists cidx rsUp,
            rsUps = [rsUp] /\
            rsEdgeUpFrom dtr cidx = Some (idOf rsUp) /\
            SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    intros.
    
    destruct rsUps as [|[rsUp0 rsm0] rsUps]; [exfalso; auto|].
    destruct rsUps as [|[rsUp1 rsm1] rsUps].

    - inv H5; clear H10.
      destruct H9 as [cidx [? ?]].
      apply SubList_cons_inv in H6; dest; clear H8.
      pose proof (atomic_msg_outs_in_history H H0 H1).
      rewrite Forall_forall in H8.
      apply H8 in H6; destruct H6 as [oidx0 [? ?]].
      repeat disc_RqRsMsgFrom.
      
      eapply atomic_separation_ok in H; try eassumption.
      destruct H.
      + destruct H as [rcidx [? ?]].
        destruct (eq_nat_dec cidx rcidx); subst.
        * disc_rule_conds; eauto.
        * exfalso.
          apply H6 in H9.
          eapply subtreeIndsOf_other_child_not_in;
            try eapply Hrrs; try eassumption.
      + exfalso.
        specialize (H cidx).
        destruct H; [auto|].
        elim H.
        apply subtreeIndsOf_child_in; try eapply Hrrs; try assumption.

    - exfalso; clear H3.
      assert (rsUp0 <> rsUp1).
      { inv H4; inv H9.
        intro Hx; elim H8.
        unfold idOf in Hx; rewrite Hx.
        left; reflexivity.
      }
      clear H4.
      apply SubList_cons_inv in H6; dest.
      apply SubList_cons_inv in H6; dest.
      clear H7.
      inv H5; inv H10; clear H11.
      destruct H9 as [cidx0 [? ?]].
      destruct H8 as [cidx1 [? ?]].
      simpl in *.
      assert (cidx0 <> cidx1)
        by (intro Hx; subst; repeat disc_rule_minds; auto).

      pose proof (atomic_msg_outs_in_history H H0 H1).
      rewrite Forall_forall in H11.
      apply H11 in H4; destruct H4 as [oidx0 [? ?]].
      apply H11 in H6; destruct H6 as [oidx1 [? ?]].
      clear H11.
      repeat disc_RqRsMsgFrom.

      eapply atomic_separation_ok in H; try eassumption.
      destruct H.
      + destruct H as [cidx [? ?]].
        destruct (eq_nat_dec cidx cidx0); subst.
        * apply H4 in H13.
          destruct Hrrs as [[? _] _].
          generalize H13.
          eapply subtreeIndsOf_other_child_not_in; try eassumption.
          congruence.
        * apply H4 in H12.
          destruct Hrrs as [[? _] _].
          generalize H12.
          eapply subtreeIndsOf_other_child_not_in; try eassumption.
          congruence.
      + specialize (H cidx0).
        destruct H; [auto|].
        elim H.
        destruct Hrrs as [[? _] _].
        apply subtreeIndsOf_child_in; assumption.
  Qed.

  Corollary atomic_non_visiting_rsUp_one:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall ruTo cidx rsUp,
          ~ In ruTo (oindsOf hst) ->
          parentIdxOf dtr cidx = Some ruTo ->
          rsEdgeUpFrom dtr cidx = Some (idOf rsUp) ->
          In rsUp eouts ->
          SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply atomic_non_visiting_rsUps_one with (rsUps:= [rsUp]) in H2;
      try eassumption.
    - destruct H2 as [rcidx [rrsUp ?]]; dest.
      inv H2; disc_rule_minds.
      assumption.
    - discriminate.
    - repeat constructor; auto.
    - repeat constructor; eauto.
    - red; intros; Common.dest_in; assumption.
  Qed.


  (*! Separation by an RqDown message *)

  Ltac disc_rule_custom ::=
    try disc_footprints_ok.
  
  Lemma step_rqDown_ins_outs_disj:
    forall cidx rqDown,
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall st1 oidx ridx rins routs st2,
        Reachable (steps step_m) sys st1 ->
        InMPI (bst_msgs st1) rqDown ->
        ~ In rqDown rins ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        ~ In rqDown routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    assert (Reachable (steps step_m) sys st2).
    { eapply reachable_steps; [eassumption|].
      eapply steps_singleton; eassumption.
    }
    pose proof (downLockInv_ok H0 H H8); clear H8.
    inv_step.
    good_locking_get obj.
    disc_rule_conds.
    intro Hx; destruct rqDown as [rqDown rsdm]; simpl in *.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
    - disc_rule_conds.
    - disc_rule_conds.
      + solve_midx_false.
      + eapply RqRsDownMatch_rq_rs in H26;
          [|apply in_map with (f:= idOf) in Hx; simpl in Hx; eassumption].
        destruct H26 as [rcidx [rsUp ?]]; dest.
        repeat disc_rule_minds; subst.
        eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.

        destruct H23; solve_q.
        erewrite findQ_In_NoDup_enqMsgs by eassumption.
        solve_q.
        rewrite filter_app; simpl.
        rewrite H3; simpl.
        rewrite app_length; simpl.
        eapply rqsQ_length_ge_one in H5; [|assumption].
        unfold rqsQ in H5; simpl in H5.
        omega.
      + eapply RqRsDownMatch_rq_rs in H11;
          [|apply in_map with (f:= idOf) in Hx; simpl in Hx; eassumption].
        destruct H11 as [rcidx [rsUp ?]]; dest.
        repeat disc_rule_minds; subst.
        eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.

        destruct H23; solve_q.
        erewrite findQ_In_NoDup_enqMsgs by eassumption.
        apply parentIdxOf_not_eq in H12; [|apply Hrrs].
        solve_q.
        rewrite filter_app; simpl.
        rewrite H3; simpl.
        rewrite app_length; simpl.
        eapply rqsQ_length_ge_one in H5; [|assumption].
        unfold rqsQ in H5; simpl in H5.
        omega.

    - disc_rule_conds.
    - disc_rule_conds.
      eapply RqRsDownMatch_rq_rs in H26;
        [|apply in_map with (f:= idOf) in Hx; simpl in Hx; eassumption].
      destruct H26 as [rcidx [rsUp ?]]; dest.
      repeat disc_rule_minds; subst.
      eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.

      destruct H23; solve_q.
      erewrite findQ_In_NoDup_enqMsgs by eassumption.
      apply parentIdxOf_not_eq in H26; [|apply Hrrs].
      solve_q.
      rewrite filter_app; simpl.
      rewrite H3; simpl.
      rewrite app_length; simpl.
      eapply rqsQ_length_ge_one in H5; [|assumption].
      unfold rqsQ in H5; simpl in H5.
      omega.
  Qed.
  
  Lemma atomic_rqDown_inits_outs_disj:
    forall cidx rqDown,
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        ~ In rqDown inits ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          InMPI (bst_msgs st1) rqDown ->
          forall st2,
            steps step_m sys st1 hst st2 ->
            ~ In rqDown outs.
  Proof.
    induction 3; simpl; intros; subst.
    - inv_steps.
      eapply step_rqDown_ins_outs_disj; eauto.
    - inv_steps.
      specialize (IHAtomic H7 _ H8 H9 _ H11).
      intro Hx; apply in_app_or in Hx.
      destruct Hx; [auto|].
      eapply (atomic_messages_in_in msg_dec) in H9; try eassumption.
      eapply step_rqDown_ins_outs_disj in H13; eauto.
      intro Hx; elim IHAtomic.
      eapply atomic_eouts_in; eauto.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_RqRsMsgFrom.

  Lemma step_rqDown_separation_inside_false:
    forall cidx rqDown pidx,
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (bst_msgs st1) rqDown ->
        forall rins,
          Forall (fun rin =>
                    exists oidx,
                      RqRsMsgFrom oidx rin /\
                      In oidx (subtreeIndsOf dtr cidx)) rins ->
          forall ridx routs st2,
            NonRqUpL dtr (RlblInt pidx ridx rins routs) ->
            step_m sys st1 (RlblInt pidx ridx rins routs) st2 ->
            False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H5) as Hftinv.
    pose proof (downLockInv_ok H0 H H5) as Hdlinv.
    inv_step.
    good_locking_get obj.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      destruct (eq_nat_dec cidx cidx0); subst.
      + disc_rule_conds.
        eapply downLockInvORq_down_rqsQ_length_one_locked in H9;
          try eassumption;
          [|eapply rqsQ_length_ge_one with (msg:= valOf rqDown); eassumption].
        dest; congruence.
      + eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
        specialize (n cidx0); destruct n; auto.
        elim H7; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
        congruence.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H29).
      destruct H11 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False with (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.

    - disc_rule_conds.
      + pose proof (edgeDownTo_Some H _ H13).
        destruct H7 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        elim (H8 pidx).
        do 2 eexists; repeat split; eauto.
      + destruct (eq_nat_dec (obj_idx upCObj) cidx); subst.
        * disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_length_one_locked in H9;
            try eassumption;
            [|eapply rqsQ_length_ge_one with (msg:= valOf rqDown); eassumption].
          dest; congruence.
        * eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
          specialize (n (obj_idx upCObj)); destruct n; auto.
          elim H7; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.
      + pose proof (edgeDownTo_Some H _ H10).
        destruct H19 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct i as [rrsDown rrsm]; simpl in *.
        pose proof (edgeDownTo_Some H _ H16).
        destruct H25 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx1:= cidx) (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

      + pose proof H9. (* Duplicate [DownLockInvORq] to apply proper lemmas later. *)
        red in H9; mred.
        specialize (H9 _ H2).
        destruct H9 as [down [rsUp ?]]; dest.
        disc_rule_conds.
        destruct (in_dec eq_nat_dec rsUp rqi.(rqi_minds_rss)).
        * eapply RqRsDownMatch_rs_rq in H28; [|eassumption].
          destruct H28 as [rcidx [down ?]]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_rsUp_False
            with (cidx:= rcidx) in H12; try eassumption.
          { eapply rqsQ_length_ge_one; eassumption. }
          { rewrite <-H35 in i.
            apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]].
            simpl in *; subst.
            rewrite Forall_forall in H19; specialize (H19 _ H33).
            eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
        * red in H31; dest.
          destruct rqDown as [rqDown rqdm]; simpl in *.
          pose proof (rqsQ_length_ge_one _ _ _ H4 H6).
          simpl in H34; rewrite H9 in H34.
          simpl in H34; omega.

      + pose proof H9. (* Duplicate [DownLockInvORq] to apply proper lemmas later. *)
        red in H9; mred.
        specialize (H9 _ H2).
        destruct H9 as [down [rsUp ?]]; dest.
        disc_rule_conds.
        destruct (in_dec eq_nat_dec rsUp rqi.(rqi_minds_rss)).
        * eapply RqRsDownMatch_rs_rq in H13; [|eassumption].
          destruct H13 as [rcidx [down ?]]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_rsUp_False
            with (cidx:= rcidx) in H23; try eassumption.
          { eapply rqsQ_length_ge_one; eassumption. }
          { rewrite <-H35 in i.
            apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]].
            simpl in *; subst.
            rewrite Forall_forall in H19; specialize (H19 _ H29).
            eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
        * red in H28; dest.
          destruct rqDown as [rqDown rqdm]; simpl in *.
          pose proof (rqsQ_length_ge_one _ _ _ H4 H6).
          simpl in H31; rewrite H9 in H31.
          simpl in H31; omega.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H37).
      destruct H10 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False with (oidx1:= cidx) (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.
  Qed.

  Lemma step_rqDown_separation_outside_false:
    forall cidx pobj rqDown,
      In pobj sys.(sys_objs) ->
      parentIdxOf dtr cidx = Some (obj_idx pobj) ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (bst_msgs st1) rqDown ->
        forall rins,
          ~ In rqDown rins ->
          (forall rsDown,
              idOf rsDown = idOf rqDown ->
              msg_type (valOf rsDown) = MRs ->
              ~ In rsDown rins) ->
          Forall (fun rin =>
                    exists oidx,
                      RqRsMsgFrom oidx rin /\
                      ~ In oidx (subtreeIndsOf dtr cidx)) rins ->
          forall ridx routs st2,
            NonRqUpL dtr (RlblInt cidx ridx rins routs) ->
            step_m sys st1 (RlblInt cidx ridx rins routs) st2 ->
            False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H6) as Hftinv.
    pose proof (downLockInv_ok H0 H H6) as Hulinv.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      elim H12; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - disc_rule_conds.
      destruct rqDown as [rqDown rqdm]; simpl in *.
      assert (rqm <> rqdm) by (intro Hx; subst; elim H8; auto); clear H8.
      good_locking_get pobj.
      eapply downLockInvORq_down_rqsQ_length_two_False in H8; try eassumption.
      eapply rqsQ_length_two with (msg1:= rqm) (msg2:= rqdm); try eassumption.
      apply FirstMP_InMP; assumption.

    - disc_rule_conds.
      + elim H15; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + elim H13; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + destruct rqDown as [rqDown rqdm]; simpl in *.
        assert (rqi_msg rqi <> rqdm)
          by (intro Hx; subst; elim H8; auto); clear H8.
        good_locking_get pobj.
        eapply downLockInvORq_down_rqsQ_length_two_False in H8; try eassumption.
        eapply rqsQ_length_two
          with (msg1:= rqi_msg rqi) (msg2:= rqdm); try eassumption.
        apply FirstMP_InMP; assumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct i as [rrsDown rrsm]; simpl in *.
        disc_rule_conds.
        elim (H9 (idOf rqDown, rrsm) eq_refl H30).
        left; reflexivity.

      + rewrite <-H37 in H30.
        assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            red in H30; dest.
            destruct rqTos; [auto|].
            discriminate.
          }
          { eexists; left; reflexivity. }
        }
        destruct H14 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins)) by (apply in_map with (f:= idOf) in H14; assumption).
        eapply RqRsDownMatch_rs_rq in H30; [|eassumption].
        destruct H30 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H14).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H39; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

      + rewrite <-H37 in H15.
        assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            red in H15; dest.
            destruct rqTos; [auto|].
            discriminate.
          }
          { eexists; left; reflexivity. }
        }
        destruct H12 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins)) by (apply in_map with (f:= idOf) in H12; assumption).
        eapply RqRsDownMatch_rs_rq in H15; [|eassumption].
        destruct H15 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H12).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H35; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - disc_rule_conds.
      elim (H9 (idOf rqDown, rsm) eq_refl H14).
      left; reflexivity.
  Qed.

  Lemma atomic_rqDown_no_rsDown:
    forall cidx rqDown pidx,
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (bst_msgs st1) rqDown ->
          steps step_m sys st1 hst st2 ->
          ~ In rqDown inits ->
          forall rsDown,
            idOf rsDown = idOf rqDown ->
            msg_type (valOf rsDown) = MRs ->
            ~ In rsDown inits ->
            ~ In rsDown ins.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 4; simpl; intros; subst; [assumption|].

    pose proof (footprints_ok H0 H11) as Hftinv.
    
    inv_steps.
    intro Hx; apply in_app_or in Hx.
    destruct Hx; [eapply IHAtomic; eauto|].

  (* Since [In rsDown ins] and [~ In rsDown inits], we have [In rsDown outs].
   * [st2.(bst_msgs) = enqMsgs outs (deqMsgs ins st1.(bst_msgs))] and we know
   * [~ In rqDown inits] (which implies [~ In rqDown ins])...
   *)
  Admitted.

  Ltac disc_rule_custom ::=
    try disc_messages_in.

  Lemma step_outside_tree_init_not_inside:
    forall cidx down oidx,
      edgeDownTo dtr cidx = Some down ->
      ~ In oidx (subtreeIndsOf dtr cidx) ->
      forall st1 ridx rins routs st2,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        forall dmsg,
          ~ In (down, dmsg) rins.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply messages_in_cases in H5; eauto.
    destruct H5 as [|[|[|]]]; intro Hx.
    - disc_rule_conds; solve_midx_false.
    - disc_rule_conds.
      elim H3.
      eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
      congruence.
    - disc_rule_conds.
      apply in_map with (f:= idOf) in Hx; simpl in Hx.
      rewrite Forall_forall in H6.
      specialize (H6 _ Hx).
      destruct H6 as [rcidx [? ?]].
      solve_midx_false.
    - disc_rule_conds.
      elim H3.
      eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
      congruence.
  Qed.

  Lemma atomic_outside_tree_init_not_inside:
    forall cidx down hst,
      edgeDownTo dtr cidx = Some down ->
      DisjList (oindsOf hst) (subtreeIndsOf dtr cidx) ->
      forall inits ins outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall dmsg,
            ~ In (down, dmsg) inits.
  Proof.
    induction 3; simpl; subst; intros.
    - inv_steps.
      simpl in H0.
      specialize (H0 oidx).
      destruct H0; [elim H0; left; reflexivity|].
      eapply step_outside_tree_init_not_inside; eauto.
    - inv_steps.
      eapply IHAtomic; eauto.
      simpl in H0; apply DisjList_cons in H0; dest; assumption.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_RqRsMsgFrom.

  Lemma atomic_NonRqUp_rqDown_separation_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      Forall (NonRqUpL dtr) hst ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cidx pobj rqDown,
          In pobj sys.(sys_objs) ->
          parentIdxOf dtr cidx = Some (obj_idx pobj) ->
          edgeDownTo dtr cidx = Some (idOf rqDown) ->
          msg_type (valOf rqDown) = MRq ->
          InMPI s1.(bst_msgs) rqDown ->
          ~ In rqDown inits ->
          SubList (oindsOf hst) (subtreeIndsOf dtr cidx) \/
          DisjList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (atomic_rqDown_no_rsDown _ _ H7 H8 H9 H2 H4 H10 H5 H11) as Hrqrs.

    generalize dependent s2.
    generalize dependent s1.
    induction H2; simpl; intros; subst.
    - destruct (in_dec eq_nat_dec oidx (subtreeIndsOf dtr cidx)).
      + left; red; intros; Common.dest_in; assumption.
      + right; apply (DisjList_singleton_1 eq_nat_dec); assumption.
    - inv_steps.
      inv H3.
      assert (forall rsDown,
                 idOf rsDown = idOf rqDown ->
                 msg_type (valOf rsDown) = MRs ->
                 ~ In rsDown inits -> ~ In rsDown ins).
      { intros; intro Hx.
        eapply Hrqrs; eauto.
        apply in_or_app; auto.
      }
      specialize (IHAtomic H16 H11 H3); clear H3.
      specialize (IHAtomic _ H14 H15 _ H17).
      destruct IHAtomic.
      + left; apply SubList_cons; [|assumption].
        pose proof (atomic_msg_outs_bounded H2 H14 H17 H3).
        eapply SubList_forall in H10; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_inside_child_ok; eauto.
        eapply (atomic_messages_in_in msg_dec) in H11; try eassumption.
        intro Hx; subst.
        eapply step_rqDown_separation_inside_false; eauto.
      + right; apply (DisjList_cons_inv eq_nat_dec); [assumption|].
        pose proof (atomic_msg_outs_disj H2 H14 H17 H3).
        eapply SubList_forall in H10; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_outside_ok; eauto.
        pose proof (atomic_messages_in_in msg_dec H2 H17 _ H15 H11).
        intro Hx; subst.
        eapply step_rqDown_separation_outside_false with (rins:= rins); eauto.
        * clear H12.
          pose proof H2.
          eapply atomic_rqDown_inits_outs_disj in H12; eauto.
          intro Hx; apply H5 in Hx.
          elim H12.
          eapply atomic_eouts_in; eauto.
        * intros; intro Hx.
          eapply Hrqrs; eauto.
          { destruct rsDown as [rsDown rsdm]; simpl in *; subst.
            clear H12.
            eapply atomic_outside_tree_init_not_inside; eauto.
          }
          { apply in_or_app; auto. }
  Qed.
  
  (*! Separation by an RsDown message *)

  Lemma step_rsDown_ins_outs_disj:
    forall cidx cobj,
      In cobj sys.(sys_objs) ->
      cobj.(obj_idx) = cidx ->
      forall rsDown pidx,
        parentIdxOf dtr cidx = Some pidx ->
        edgeDownTo dtr cidx = Some (idOf rsDown) ->
        msg_type (valOf rsDown) = MRs ->
        forall st1 oidx ridx rins routs st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (bst_msgs st1) rsDown ->
          ~ In rsDown rins ->
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          ~ In rsDown routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    assert (Reachable (steps step_m) sys st2).
    { eapply reachable_steps; [eassumption|].
      eapply steps_singleton; eassumption.
    }
    pose proof (upLockInv_ok H0 H H11) as Hlinv; clear H11.
    pose proof (footprints_ok H0 H7) as Hfinv.
    inv_step.
    good_locking_get cobj.
    intro Hx.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
      solve_q.
      rewrite filter_app; simpl.
      rewrite H12; simpl.
      rewrite app_length; simpl.
      eapply rssQ_length_ge_one in H8; [|assumption].
      unfold rssQ in H8; simpl in H8.
      omega.

    - disc_rule_conds.
      solve_midx_false.

    - disc_rule_conds.
      + rewrite Forall_forall in H38; specialize (H38 _ Hx).
        simpl in H38; rewrite H38 in H6; discriminate.
      + rewrite Forall_forall in H38; specialize (H38 _ Hx).
        simpl in H38; rewrite H38 in H6; discriminate.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
        solve_q.
        apply parentIdxOf_not_eq in H4; [|apply Hrrs].
        solve_q.
        rewrite filter_app; simpl.
        rewrite H17; simpl.
        rewrite app_length; simpl.
        eapply rssQ_length_ge_one in H8; [|assumption].
        unfold rssQ in H8; simpl in H8.
        omega.
      + eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
        rewrite <-H35 in H28.
        solve_q.
        rewrite filter_app; simpl.
        rewrite H14; simpl.
        rewrite app_length; simpl.
        eapply rssQ_length_ge_one in H8; [|assumption].
        unfold rssQ in H8; simpl in H8.
        omega.
      + solve_midx_false.

    - disc_rule_conds.
      rewrite Forall_forall in H33; specialize (H33 _ Hx).
      simpl in H33; rewrite H33 in H6; discriminate.
  Qed.

  Lemma atomic_rsDown_inits_outs_disj:
    forall cidx cobj,
      In cobj sys.(sys_objs) ->
      cobj.(obj_idx) = cidx ->
      forall rsDown pidx,
        parentIdxOf dtr cidx = Some pidx ->
        edgeDownTo dtr cidx = Some (idOf rsDown) ->
        msg_type (valOf rsDown) = MRs ->
        forall inits ins hst outs eouts,
          Atomic msg_dec inits ins hst outs eouts ->
          ~ In rsDown inits ->
          forall st1,
            Reachable (steps step_m) sys st1 ->
            InMPI (bst_msgs st1) rsDown ->
            forall st2,
              steps step_m sys st1 hst st2 ->
              ~ In rsDown outs.
  Proof.
    induction 6; simpl; intros; subst.
    - inv_steps.
      eapply step_rsDown_ins_outs_disj; eauto.
    - inv_steps.
      specialize (IHAtomic H10 _ H11 H12 _ H9).
      intro Hx; apply in_app_or in Hx.
      destruct Hx; [auto|].
      assert (Reachable (steps step_m) sys st3) by eauto.
      eapply step_rsDown_ins_outs_disj with (rins:= rins); eauto.
      + eapply (atomic_messages_in_in msg_dec); eauto.
      + intro Hx; apply H6 in Hx.
        elim IHAtomic.
        eapply atomic_eouts_in; eauto.
  Qed.
  
  Lemma step_rsDown_separation_inside_false:
    forall cidx cobj,
      In cobj sys.(sys_objs) ->
      cobj.(obj_idx) = cidx ->
      forall rsDown pidx,
        parentIdxOf dtr cidx = Some pidx ->
        edgeDownTo dtr cidx = Some (idOf rsDown) ->
        msg_type (valOf rsDown) = MRs ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          InMPI (bst_msgs st1) rsDown ->
          forall rins,
            Forall (fun rin =>
                      exists oidx,
                        RqRsMsgFrom oidx rin /\
                        In oidx (subtreeIndsOf dtr cidx)) rins ->
            forall ridx routs st2,
              step_m sys st1 (RlblInt pidx ridx rins routs) st2 ->
              False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H7) as Hftinv.
    pose proof (upLockInv_ok H0 H H7) as Hulinv.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      destruct (eq_nat_dec cidx (obj_idx cobj)); subst.
      + disc_rule_conds.
        good_locking_get cobj.
        eapply upLockInvORq_rqUp_down_rssQ_False in H3; try eassumption.
        * eapply findQ_length_ge_one.
          apply FirstMP_InMP; eassumption.
        * eapply rssQ_length_ge_one; [|eassumption].
          assumption.
      + eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
        specialize (n cidx); destruct n; auto.
        elim H3; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
        congruence.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H28).
      destruct H10 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False with (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.

    - disc_rule_conds.
      + destruct (eq_nat_dec cidx (obj_idx cobj)); subst.
        * disc_rule_conds.
          good_locking_get cobj.
          eapply upLockInvORq_rqUp_down_rssQ_False in H3; try eassumption.
          { eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
          { eapply rssQ_length_ge_one; [|eassumption].
            assumption.
          }
        * eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
          specialize (n cidx); destruct n; auto.
          elim H9; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.
      + destruct (eq_nat_dec (obj_idx upCObj) (obj_idx cobj)); subst.
        * rewrite e in *.
          disc_rule_conds.
          good_locking_get cobj.
          eapply upLockInvORq_rqUp_down_rssQ_False in H9; try eassumption.
          { eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
          { eapply rssQ_length_ge_one; [|eassumption].
            assumption.
          }
        * eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
          specialize (n (obj_idx upCObj)); destruct n; auto.
          elim H9; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.
      + pose proof (edgeDownTo_Some H _ H3).
        destruct H14 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct i as [rrsDown rrsm]; simpl in *.
        pose proof (edgeDownTo_Some H _ H13).
        destruct H17 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx1:= obj_idx cobj) (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

      + (* Not possible for RsDown and RsUp to be together *)
        admit.
      + (* Not possible for RsDown and RsUp to be together *)
        admit.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H36).
      destruct H9 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False with (oidx1:= obj_idx cobj) (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.
      
  Admitted.

  Lemma step_rsDown_separation_outside_false:
    forall cidx rsDown,
      edgeDownTo dtr cidx = Some (idOf rsDown) ->
      msg_type (valOf rsDown) = MRs ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (bst_msgs st1) rsDown ->
        forall rins,
          ~ In rsDown rins ->
          Forall (fun rin =>
                    exists oidx,
                      RqRsMsgFrom oidx rin /\
                      ~ In oidx (subtreeIndsOf dtr cidx)) rins ->
          forall ridx routs st2,
            step_m sys st1 (RlblInt cidx ridx rins routs) st2 ->
            False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H4) as Hftinv.
    pose proof (upLockInv_ok H0 H H4) as Hulinv.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      elim H8; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - disc_rule_conds.
      (* Not possible for RqDown and RsDown in the same queue,
       * where RqDown is the first of the queue.
       *)
      admit.

    - disc_rule_conds.
      + elim H11; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + elim H9; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + (* Not possible for RqDown and RsDown in the same queue,
         * where RqDown is the first of the queue.
         *)
        admit.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct rsDown as [rsDown rsdm]; simpl in *.
        destruct i as [rsFrom rsfm]; simpl in *; subst.
        pose proof (rqEdgeUpFrom_Some H _ H11).
        destruct H12 as [rsUp [down [pidx ?]]]; dest.
        disc_rule_conds.
        assert (rsfm <> rsdm) by (intro Hx; subst; elim H6; auto); clear H6.
        good_locking_get obj.
        eapply upLockInvORq_down_rssQ_length_two_False in H6; try eassumption.
        eapply rssQ_length_two with (msg1:= rsfm) (msg2:= rsdm); try eassumption.
        apply FirstMP_InMP; assumption.

      + rewrite <-H33 in H26.
        assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            red in H26; dest.
            destruct rqTos; [auto|].
            discriminate.
          }
          { eexists; left; reflexivity. }
        }
        destruct H10 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins)) by (apply in_map with (f:= idOf) in H10; assumption).
        eapply RqRsDownMatch_rs_rq in H26; [|eassumption].
        destruct H26 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H7; specialize (H7 _ H10).
        destruct H7 as [oidx [? ?]].
        disc_rule_conds.
        elim H35; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

      + rewrite <-H33 in H11.
        assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            red in H11; dest.
            destruct rqTos; [auto|].
            discriminate.
          }
          { eexists; left; reflexivity. }
        }
        destruct H8 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins)) by (apply in_map with (f:= idOf) in H8; assumption).
        eapply RqRsDownMatch_rs_rq in H11; [|eassumption].
        destruct H11 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H7; specialize (H7 _ H8).
        destruct H7 as [oidx [? ?]].
        disc_rule_conds.
        elim H31; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - disc_rule_conds.
      destruct rsDown as [rsDown rsdm]; simpl in *.
      pose proof (edgeDownTo_Some H _ H2).
      destruct H8 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      assert (rsm <> rsdm) by (intro Hx; subst; elim H6; auto); clear H6.
      good_locking_get obj.
      eapply upLockInvORq_down_rssQ_length_two_False in H6; try eassumption.
      eapply rssQ_length_two with (msg1:= rsm) (msg2:= rsdm); try eassumption.
      apply FirstMP_InMP; assumption.

  Admitted.

  Lemma atomic_rsDown_separation_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cidx cobj,
          In cobj sys.(sys_objs) ->
          cobj.(obj_idx) = cidx ->
          forall rsDown pidx,
            parentIdxOf dtr cidx = Some pidx ->
            edgeDownTo dtr cidx = Some (idOf rsDown) ->
            msg_type (valOf rsDown) = MRs ->
            InMPI s1.(bst_msgs) rsDown ->
            ~ In rsDown inits ->
            SubList (oindsOf hst) (subtreeIndsOf dtr cidx) \/
            DisjList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - destruct (in_dec eq_nat_dec oidx (subtreeIndsOf dtr (obj_idx cobj))).
      + left; red; intros; Common.dest_in; assumption.
      + right; apply (DisjList_singleton_1 eq_nat_dec); assumption.
    - inv_steps.
      specialize (IHAtomic _ _ H8 H11 _ _ H10 eq_refl _ _ H12 H13 H14 H15 H16).
      destruct IHAtomic.
      + left; apply SubList_cons; [|assumption].
        pose proof (atomic_msg_outs_bounded H2 H8 H11 H5).
        eapply SubList_forall in H6; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_inside_child_ok; eauto.
        eapply (atomic_messages_in_in msg_dec) in H15; try eassumption.
        intro Hx; subst.
        eapply step_rsDown_separation_inside_false; eauto.
      + right; apply (DisjList_cons_inv eq_nat_dec); [assumption|].
        pose proof (atomic_msg_outs_disj H2 H8 H11 H5).
        eapply SubList_forall in H6; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_outside_ok; eauto.
        pose proof (atomic_messages_in_in msg_dec H2 H11 _ H15 H16).
        intro Hx; subst.
        eapply step_rsDown_separation_outside_false with (rins:= rins); eauto.
        clear H7; pose proof H2.
        eapply atomic_rsDown_inits_outs_disj in H7; eauto.
        intro Hx; eapply H4 in Hx.
        elim H7; eapply atomic_eouts_in; eauto.
  Qed.

  Corollary atomic_rsDown_separation_inside:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cidx cobj,
          In cobj sys.(sys_objs) ->
          cobj.(obj_idx) = cidx ->
          forall rsDown pidx,
            parentIdxOf dtr cidx = Some pidx ->
            edgeDownTo dtr cidx = Some (idOf rsDown) ->
            msg_type (valOf rsDown) = MRs ->
            InMPI s1.(bst_msgs) rsDown ->
            ~ In rsDown inits ->
            forall ioidx,
              In ioidx (oindsOf hst) ->
              In ioidx (subtreeIndsOf dtr cidx) ->
              SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    intros.
    eapply atomic_rsDown_separation_ok in H; eauto.
    destruct H; auto.
    exfalso.
    specialize (H ioidx); destruct H; auto.
  Qed.

  Corollary atomic_rsDown_separation_outside:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cidx cobj,
          In cobj sys.(sys_objs) ->
          cobj.(obj_idx) = cidx ->
          forall rsDown pidx,
            parentIdxOf dtr cidx = Some pidx ->
            edgeDownTo dtr cidx = Some (idOf rsDown) ->
            msg_type (valOf rsDown) = MRs ->
            InMPI s1.(bst_msgs) rsDown ->
            ~ In rsDown inits ->
            forall ioidx,
              In ioidx (oindsOf hst) ->
              ~ In ioidx (subtreeIndsOf dtr cidx) ->
              DisjList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    intros.
    eapply atomic_rsDown_separation_ok in H; eauto.
    destruct H; auto.
    exfalso.
    elim H10; auto.
  Qed.

End Separation.

