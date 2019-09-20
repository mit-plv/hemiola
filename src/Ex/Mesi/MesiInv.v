Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

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
    MsgsNotExist [(rqUpFrom oidx, (MRq, mesiInvWRq));
                    (rqUpFrom oidx, (MRq, mesiPushWRq))] msgs.

  (** 0) Coherence: which values are in a coherent state *)

  Definition ImplOStateMESI (cv: nat): Prop :=
    mesiS <= ost#[status] -> NoRsI -> ost#[val] = cv.

  Definition ObjOwned :=
    mesiS <= ost#[status] /\ ost#[owned] = true.

  Definition CohInvRq :=
    ObjOwned ->
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiInvWRq)) ->
      msg_value (valOf idm) = ost#[val].

  Definition CohPushRq :=
    ObjOwned ->
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiPushWRq)) ->
      msg_value (valOf idm) = ost#[val].

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
                    (rsUpFrom oidx, (MRs, mesiDownRsS))] msgs.

  Definition ObjInvalid0 :=
    ost#[status] = mesiI /\ NoCohMsgs.

  Definition ObjInvalid :=
    ObjInvalid0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiInvRs)) msgs.

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

  Definition ObjRqWB :=
    MsgExistsSig (rqUpFrom oidx, (MRq, mesiInvWRq)) msgs \/
    MsgExistsSig (rqUpFrom oidx, (MRq, mesiPushWRq)) msgs.

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

Definition InvObjExcl0 (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ObjExcl0 oidx ost msgs -> NoCohMsgs oidx msgs.

Definition InvExcl (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_msgs st) /\
       (ObjExcl eidx eost (bst_msgs st) ->
        forall oidx,
          oidx <> eidx ->
          ost <+- (bst_oss st)@[oidx];
            ObjInvalid oidx ost (bst_msgs st))).

Definition InvWB (st: MState): Prop :=
  forall oidx,
    ost <+- (bst_oss st)@[oidx];
      (CohInvRq oidx ost (bst_msgs st) /\
       CohPushRq oidx ost (bst_msgs st)).

Definition InvWBChild (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirME porq post oidx ->
       ObjRqWB oidx (bst_msgs st) ->
       ObjOwned ost).

Definition InvNonWB (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirE porq post oidx ->
       ObjInvRq oidx (bst_msgs st) ->
       (ObjClean ost /\ ost#[val] = post#[val])).

Definition InvForSim (topo: DTree) (st: MState): Prop :=
  InvExcl st /\
  InvWB st /\ InvWBChild topo st /\ InvNonWB topo st /\
  MesiFootprintsInv topo st.

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

  Lemma InvExcl_excl_invalid:
    forall st (He: InvExcl st) msgs eidx eost,
      bst_msgs st = msgs ->
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx msgs ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        ObjInvalid oidx ost msgs.
  Proof.
    intros; subst.
    specialize (He eidx).
    disc_rule_conds_ex.
    unfold ObjExcl, ObjExcl0 in H5; simpl in H5.
    specialize (H5 (or_introl (conj H2 H1)) _ H3).
    solve_rule_conds_ex.
  Qed.

  Corollary InvExcl_excl_invalid_status:
    forall st (He: InvExcl st) eidx eost,
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx (bst_msgs st) ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        NoRsI oidx (bst_msgs st) ->
        ost#[status] = mesiI.
  Proof.
    intros.
    eapply InvExcl_excl_invalid in H1; eauto.
    destruct H1.
    - apply H1.
    - exfalso; eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
  Qed.
  
End Facts.

(** The invariants proof starts here -- *)

Lemma mesi_InvForSim_init:
  forall tr (Htr: tr <> Node nil),
    InvForSim (fst (tree2Topo tr 0)) (initsOf (impl Htr)).
Proof.
Admitted.

Lemma mesi_InvForSim_ok:
  forall tr (Htr: tr <> Node nil),
    InvStep (impl Htr) step_m (InvForSim (fst (tree2Topo tr 0))).
Proof.
Admitted.

Ltac solve_NoRsI_base :=
  repeat
    match goal with
    | |- NoRsI _ _ => do 3 red; intros
    | |- MsgP _ _ =>
      red; unfold map, caseDec, fst;
      repeat (find_if_inside; [simpl|auto])
    | [H: sigOf ?idm = _ |- _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct idm as [midx msg]; inv H
    end.

Ltac solve_NoRsI_by_no_locks oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRs |- _] =>
      specialize (Hmcf (midx, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm); dest; auto
    end.

Ltac solve_NoRsI_by_rqUp oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_li_indices _ ++ c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ Hin Horq);
      simpl in Hmcfi; destruct Hmcfi
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

Ltac solve_NoRsI_by_rqDown oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRs |- _] =>
      specialize (Hmcf (midx, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm);
      let Hrqd := fresh "H" in
      destruct Hmcf as [_ [_ [_ [Hrqd _]]]];
      eapply Hrqd; try eassumption; try reflexivity; assumption
    end.

Ltac solve_NoRsI_by_rsDown oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
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

Ltac solve_NoRqI_base :=
  repeat
    match goal with
    | |- NoRqI _ _ => do 3 red; intros
    | |- MsgP _ _ =>
      red; unfold map, caseDec, fst;
      repeat (find_if_inside; [simpl|auto])
    | [H: sigOf ?idm = _ |- _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct idm as [midx msg]; inv H
    end.

Ltac solve_NoRqI_by_no_locks oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RqUpConflicts oidx _ ?msgs, Hinm: InMPI ?msgs (?midx, ?msg) |- _] =>
      specialize (Hmcf (midx, msg) eq_refl Hinm); dest; auto
    end.

Ltac solve_NoRqI_by_rsDown oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
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

Ltac derive_ObjDirE oidx cidx :=
  match goal with
  | [Host: ?oss@[oidx] = Some ?ost,
           Horq: ?orqs@[oidx] = Some ?orq |- _] =>
    assert (ObjDirE orq ost cidx) by (repeat split; assumption)
  end.

Ltac derive_ObjDirME oidx cidx :=
  match goal with
  | [Host: ?oss@[oidx] = Some ?ost,
           Horq: ?orqs@[oidx] = Some ?orq |- _] =>
    assert (ObjDirME orq ost cidx) by (repeat split; assumption)
  end.

Ltac derive_ObjInvRq oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjInvRq oidx msgs)
      by (exists (rqUpFrom oidx, rmsg); split;
                 [red; simpl; solve_in_mp|unfold sigOf; simpl; congruence])
  end.

Ltac derive_ObjRqWB_inv oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjRqWB oidx msgs)
      by (left; eexists; split;
          [eapply FirstMP_InMP; eassumption
          |unfold sigOf; simpl; congruence])
  end.

Ltac derive_ObjRqWB_push oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjRqWB oidx msgs)
      by (right; eexists; split;
          [eapply FirstMP_InMP; eassumption
          |unfold sigOf; simpl; congruence])
  end.

Ltac disc_InvNonWB cidx Hinv :=
  repeat
    match goal with
    | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
      specialize (Hinv _ _ Hp); simpl in Hinv;
      disc_rule_conds_ex
    end.

Ltac disc_InvWBChild cidx Hinv :=
  match goal with
  | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
    specialize (Hinv _ _ Hp); simpl in Hinv;
    disc_rule_conds_ex
  end.

Ltac disc_InvWB_inv cidx Hinv :=
  specialize (Hinv cidx); simpl in Hinv;
  disc_rule_conds_ex;
  match goal with
  | [Hcoh: CohInvRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
    specialize (Hcoh Ho _ (FirstMP_InMP Hfm));
    unfold sigOf in Hcoh; simpl in Hcoh;
    specialize (Hcoh ltac:(congruence))
  end.

Ltac disc_InvWB_push cidx Hinv :=
  specialize (Hinv cidx); simpl in Hinv;
  disc_rule_conds_ex;
  match goal with
  | [Hcoh: CohPushRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
    specialize (Hcoh Ho _ (FirstMP_InMP Hfm));
    unfold sigOf in Hcoh; simpl in Hcoh;
    specialize (Hcoh ltac:(congruence))
  end.

Hint Unfold NoRsI ImplOStateMESI: RuleConds.
Hint Unfold InvForSim: RuleConds.

