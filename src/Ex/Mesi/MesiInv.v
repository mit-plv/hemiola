Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLangEx RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Export Ex.Mesi.MesiInvB.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Section CoherenceUnit.
  Variables (oidx: IdxT)
            (orq: ORq Msg)
            (ost: OState)
            (msgs: MessagePool Msg).

  Definition NoRsI :=
    MsgsNotExist [(downTo oidx, (MRs, mesiInvRs))] msgs.

  Definition NoRqI :=
    MsgsNotExist [(rqUpFrom oidx, (MRq, mesiInvRq));
                    (rqUpFrom oidx, (MRq, mesiInvWRq))] msgs.

  (** 0) Coherence: which values are in a coherent state *)

  Definition ImplOStateMESI (cv: nat): Prop :=
    mesiS <= ost#[status] -> NoRsI -> ost#[val] = cv.

  Definition CohInvRq :=
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiInvWRq)) ->
      mesiS <= ost#[status] -> msg_value (valOf idm) = ost#[val].

  (** 1) Exclusiveness: if a coherence unit is exclusive, then all other units
   * are in an invalid status. *)
  
  Definition ObjExcl0 :=
    mesiE <= ost#[status] /\ NoRsI.

  Definition ObjExcl :=
    ObjExcl0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsE)) msgs \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsM)) msgs.

  Definition NoCohMsgs :=
    MsgsNotExist [(downTo oidx, (MRs, mesiRsS));
                    (downTo oidx, (MRs, mesiRsE));
                    (downTo oidx, (MRs, mesiRsM));
                    (rsUpFrom oidx, (MRs, mesiDownRsS))] msgs.

  Definition ObjInvalid0 :=
    ost#[status] <= mesiI /\ NoCohMsgs.

  Definition ObjInvRs :=
    MsgExistsSig (downTo oidx, (MRs, mesiInvRs)) msgs.
  
  Definition ObjInvalid :=
    ObjInvalid0 \/ ObjInvRs.

  (** 2) Clean "E" in MESI *)

  Definition ObjClean :=
    mesiS <= ost#[status] <= mesiE.

  Definition ObjDirME (cidx: IdxT) :=
    mesiE <= ost#[dir].(dir_st) /\ ost#[dir].(dir_excl) = cidx /\
    orq@[downRq] = None.

  Definition ObjDirE (cidx: IdxT) :=
    ost#[dir].(dir_st) = mesiE /\ ost#[dir].(dir_excl) = cidx /\
    orq@[downRq] = None.
  
  Definition ObjInvRq :=
    MsgExistsSig (rqUpFrom oidx, (MRq, mesiInvRq)) msgs.

  Definition ObjInvWRq :=
    MsgExistsSig (rqUpFrom oidx, (MRq, mesiInvWRq)) msgs.

  Section Facts.

    Lemma NoRsI_MsgExistsSig_InvRs_false:
      MsgExistsSig (downTo oidx, (MRs, mesiInvRs)) msgs ->
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
      NoRsI (rootOf (fst (tree2Topo tr bidx))) (bst_msgs st).
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
      NoRqI (rootOf (fst (tree2Topo tr bidx))) (bst_msgs st).
  Proof.
    intros.
    do 3 red; intros.
    red; unfold map, fst, snd, caseDec.
    do 2 (find_if_inside; [eapply H; [|eassumption]; inv e; auto|]).
    auto.
  Qed.
  
End Facts.

Ltac disc_getDir :=
  try match goal with
      | [H: getDir _ _ = _ |- _] =>
        first [apply getDir_M_imp in H; destruct H
              |apply getDir_E_imp in H; destruct H
              |apply getDir_S_imp in H; destruct H]
      | [H: mesiE <= getDir _ _ |- _] =>
        apply getDir_ME_imp in H; destruct H
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
      | [Hmcf: RqDownConflicts _ _ ?msgs,
               Hf: FirstMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRq |- _] =>
        specialize (Hmcf (midx, msg) eq_refl 
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                (FirstMP_InMP Hf)); dest
      end.

Ltac derive_MesiDownLockInv oidx :=
  match goal with
  | [Hdl: MesiDownLockInv _ _ |- _] =>
    specialize (Hdl oidx); simpl in Hdl;
    repeat
      match type of Hdl with
      | _ <+- ?ov; _ =>
        match goal with
        | [H: ov = Some _ |- _] => rewrite H in Hdl; simpl in Hdl
        end
      end;
    repeat
      match goal with
      | [H: msg_id ?rmsg = _ |- _] => rewrite H in Hdl
      end;
    simpl in Hdl; dest
  end.

Hint Unfold NoRsI ImplOStateMESI: RuleConds.

