Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Msi Ex.Msi.Msi Ex.Msi.MsiTopo.

Require Export Ex.Msi.MsiInvB.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

#[global] Existing Instance Msi.ImplOStateIfc.

Section CoherenceUnit.
  Variables (oidx: IdxT)
            (orq: ORq Msg)
            (ost: OState)
            (msgs: MessagePool Msg).

  Definition NoRsI :=
    MsgsNotExist [(downTo oidx, (MRs, msiInvRs))] msgs.

  Definition NoRqI :=
    MsgsNotExist [(rqUpFrom oidx, (MRq, msiInvRq));
                    (rqUpFrom oidx, (MRq, msiInvWRq))] msgs.

  (** 0) Coherence: which values are in a coherent state *)

  Definition ImplOStateMSI (cv: nat): Prop :=
    msiS <= ost#[status] -> NoRsI -> ost#[val] = cv.

  Definition CohInvRq :=
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, msiInvWRq)) ->
      msiS <= ost#[status] -> msg_value (valOf idm) = ost#[val].

  Definition ObjInvRs :=
    MsgExistsSig (downTo oidx, (MRs, msiInvRs)) msgs.

  (** 1) Exclusiveness: if a coherence unit is exclusive, then all other units
   * are in an invalid status. *)

  Definition ObjExcl0 :=
    msiM <= ost#[status] /\ NoRsI.

  Definition ObjExcl :=
    ObjExcl0 \/
    MsgExistsSig (downTo oidx, (MRs, msiRsM)) msgs.

  (** 2) When directory status is M .. *)

  Definition ObjDirM (cidx: IdxT) :=
    ost#[dir].(dir_st) = msiM /\ ost#[dir].(dir_excl) = cidx /\
    orq@[downRq] = None.

  Definition ObjInvRq :=
    MsgExistsSig (rqUpFrom oidx, (MRq, msiInvRq)) msgs.

  Definition ObjInvWRq :=
    MsgExistsSig (rqUpFrom oidx, (MRq, msiInvWRq)) msgs.

  Section Facts.

    Lemma NoRsI_MsgExistsSig_InvRs_false:
      MsgExistsSig (downTo oidx, (MRs, msiInvRs)) msgs ->
      NoRsI -> False.
    Proof.
      intros.
      destruct H as [idm [? ?]].
      specialize (H0 _ H).
      unfold MsgP in H0.
      rewrite H1 in H0.
      unfold map, caseDec in H0.
      find_if_inside; auto.
    Qed.

  End Facts.

End CoherenceUnit.

Section Facts.

  Lemma RootChnInv_root_NoRsI:
    forall tr bidx st,
      RootChnInv tr bidx st ->
      NoRsI (rootOf (fst (tree2Topo tr bidx))) (st_msgs st).
  Proof.
    intros.
    do 3 red; intros.
    red; unfold map, fst, snd, caseDec.
    find_if_inside; auto.
    eapply H; [|eassumption].
    inv e; auto.
  Qed.

  Lemma RootChnInv_root_NoRqI:
    forall tr bidx st,
      RootChnInv tr bidx st ->
      NoRqI (rootOf (fst (tree2Topo tr bidx))) (st_msgs st).
  Proof.
    intros.
    do 3 red; intros.
    red; unfold map, fst, snd, caseDec.
    do 2 (find_if_inside; [eapply H; [|eassumption]; inv e; auto|]).
    auto.
  Qed.

End Facts.

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

Ltac disc_getDir :=
  try match goal with
      | [H: getDir _ _ = _ |- _] =>
        first [apply getDir_M_imp in H; destruct H
              |apply getDir_S_imp in H; destruct H]
      end.

Ltac solve_MsgsNotExist_base :=
  repeat
    match goal with
    | |- MsgsNotExist _ _ => red
    | |- MsgsP _ _ => red; intros
    | |- MsgP _ _ =>
      red; unfold map, caseDec, fst;
      repeat (find_if_inside; [simpl|auto])
    | [H: sigOf ?idm = _ |- _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct idm as [midx msg]; inv H
    end.

Ltac solve_NoRsI_base :=
  red; solve_MsgsNotExist_base.

Ltac solve_RsDown_by_no_uplock oidx :=
  try match goal with
      | [Hmcf: RsDownConflicts oidx _ ?msgs,
               Hinm: InMPI ?msgs (?midx, ?msg),
                     Hmt: msg_type ?msg = MRs |- _] =>
        specialize (Hmcf (midx, msg) eq_refl
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                Hinm); dest; auto
      end.

Ltac solve_NoRsI_by_no_uplock oidx :=
  disc_MsgConflictsInv oidx; solve_RsDown_by_no_uplock oidx.

Ltac solve_RsDown_by_parent_lock oidx :=
  try match goal with
      | [Hmcfp: ParentLockConflicts _ oidx _ _,
                Hin: InMPI _ (downTo oidx, ?msg) |- _] =>
        specialize (Hmcfp ltac:(red; mred; simpl; eauto));
        destruct Hmcfp as [Hmcfp _];
        eapply (Hmcfp (downTo oidx, msg)); eauto
      end.

Ltac solve_NoRsI_by_parent_lock oidx :=
  disc_MsgConflictsInv oidx; solve_RsDown_by_parent_lock oidx.

Ltac solve_RsDown_by_rqUp oidx :=
  repeat
    match goal with
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?rsd, ?msg),
                   Hmt: msg_type ?msg = MRs,
                        Hfmp: FirstMPI ?msgs (?rqu, ?rmsg) |- _] =>
      specialize (Hmcf (rsd, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm);
      let Hrqu := fresh "H" in
      destruct Hmcf as [_ [Hrqu _]];
      apply Hrqu with (rqUp:= (rqu, rmsg)); auto
    | |- InMPI _ _ => red; solve_in_mp
    end.

Ltac solve_NoRsI_by_rqUp oidx :=
  disc_MsgConflictsInv oidx; solve_RsDown_by_rqUp oidx.

Ltac solve_RsDown_by_rqDown oidx :=
  repeat
    match goal with
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRs |- _] =>
      specialize (Hmcf (midx, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm);
      let Hrqd := fresh "H" in
      destruct Hmcf as [_ [_ [_ [_ [Hrqd _]]]]];
      eapply Hrqd; try eassumption; try reflexivity; assumption
    end.

Ltac solve_NoRsI_by_rqDown oidx :=
  disc_MsgConflictsInv oidx; solve_RsDown_by_rqDown oidx.

Ltac solve_RsDown_by_rsDown oidx :=
  repeat
    match goal with
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRs,
                        Hfmp: FirstMPI ?msgs (?midx, ?rmsg) |- _] =>
      specialize (Hmcf (midx, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm);
      let Hrqd := fresh "H" in
      destruct Hmcf as [_ [_ [Hrqd _]]];
      eapply Hrqd with (rrsDown:= (midx, rmsg));
      try eassumption; try reflexivity
    | |- valOf (_, ?msg1) <> valOf (_, ?msg2) =>
      let Hx := fresh "H" in
      destruct msg1, msg2; simpl in *; intro Hx; inv Hx; discriminate
    | |- InMPI _ _ => red; solve_in_mp
    end.

Ltac solve_NoRsI_by_rsDown oidx :=
  disc_MsgConflictsInv oidx; solve_RsDown_by_rsDown oidx.

Ltac derive_NoRsI_by_no_uplock oidx msgs :=
  assert (NoRsI oidx msgs)
  by (solve_NoRsI_base; solve_NoRsI_by_no_uplock oidx).

Ltac derive_NoRsI_by_rqUp oidx msgs :=
  assert (NoRsI oidx msgs)
  by (solve_NoRsI_base; solve_NoRsI_by_rqUp oidx).

Ltac derive_NoRsI_by_rsDown oidx msgs :=
  assert (NoRsI oidx msgs)
  by (solve_NoRsI_base; solve_NoRsI_by_rsDown oidx).

Ltac derive_NoRsI_by_rqDown oidx msgs :=
  assert (NoRsI oidx msgs)
  by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).

Ltac solve_NoRqI_base :=
  red; solve_MsgsNotExist_base.

Ltac solve_NoRqI_by_no_locks oidx :=
  disc_MsgConflictsInv oidx;
  repeat
    match goal with
    | [Hmcf: RqUpConflicts oidx _ ?msgs, Hinm: InMPI ?msgs (?midx, ?msg) |- _] =>
      specialize (Hmcf (midx, msg) eq_refl Hinm); dest; auto
    end.

Ltac solve_NoRqI_by_rqUp oidx :=
  disc_MsgConflictsInv oidx;
  repeat
    match goal with
    | [Hmcf: RqUpConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hfmp: FirstMPI ?msgs (?midx, ?rmsg) |- _] =>
      specialize (Hmcf (midx, msg) eq_refl Hinm);
      let Hrqd := fresh "H" in
      destruct Hmcf as [_ [Hrqd _]];
      eapply Hrqd with (rrqUp:= (midx, rmsg));
      try eassumption; try reflexivity
    | |- valOf (_, ?msg1) <> valOf (_, ?msg2) =>
      let Hx := fresh "H" in
      destruct msg1, msg2; simpl in *; intro Hx; inv Hx; discriminate
    | |- InMPI _ _ => red; solve_in_mp
    end.

Ltac solve_NoRqI_by_rsDown oidx :=
  disc_MsgConflictsInv oidx;
  repeat
    match goal with
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hfmp: FirstMPI ?msgs (?down, ?msg),
                   Hmt: msg_type ?msg = MRs,
                        Hinm: InMPI ?msgs (?rqu, ?rmsg) |- _] =>
      apply FirstMP_InMP in Hfmp;
      specialize (Hmcf (down, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hfmp);
      let Hrqu := fresh "H" in
      destruct Hmcf as [_ [Hrqu _]];
      eapply Hrqu with (rqUp:= (rqu, rmsg));
      try eassumption; try reflexivity
    end.

Ltac derive_parent_downlock_by_RqDown oidx :=
  disc_MsgConflictsInv oidx;
  try match goal with
      | [Hmcf: ParentRqDownRsUpLocked _ _ ?msgs,
               Hf: FirstMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRq |- _] =>
        destruct Hmcf as [Hmcf _];
        specialize (Hmcf (midx, msg) eq_refl
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                (FirstMP_InMP Hf))
      end.

#[global] Hint Unfold NoRsI ImplOStateMSI: RuleConds.
