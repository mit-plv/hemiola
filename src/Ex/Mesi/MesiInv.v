Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

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

Lemma MsgExistsSig_MsgsNotExist_false:
  forall msgs sigs,
    MsgsNotExist sigs msgs ->
    forall sig,
      In sig sigs ->
      MsgExistsSig sig msgs -> False.
Proof.
  intros.
  destruct H1 as [idm [? ?]]; subst.
  specialize (H _ H1); clear H1.
  induction sigs; [dest_in|].
  destruct (sig_dec (sigOf idm) a); subst.
  - red in H.
    do 2 rewrite map_cons in H.
    rewrite caseDec_head_eq in H by reflexivity.
    auto.
  - inv H0; [auto|].
    red in H.
    do 2 rewrite map_cons in H.
    rewrite caseDec_head_neq in H by assumption.
    auto.
Qed.

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

  Definition ObjOwned :=
    mesiS <= ost#[status] /\ ost#[owned] = true.

  Definition CohInvRq :=
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiInvWRq)) ->
      (ost#[dir].(dir_st) = mesiI /\
       (ObjOwned -> msg_value (valOf idm) = ost#[val])).

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

Definition InvWBCoh (st: MState): Prop :=
  forall oidx,
    ost <+- (bst_oss st)@[oidx];
      CohInvRq oidx ost (bst_msgs st).

Definition InvWB (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      ((ObjDirME porq post oidx -> ObjInvWRq oidx (bst_msgs st) ->
        ObjOwned ost) /\
       (ObjDirE porq post oidx -> ObjInvRq oidx (bst_msgs st) ->
        (ObjClean ost /\ ost#[val] = post#[val]))).

Definition InvForSim (topo: DTree) (st: MState): Prop :=
  InvExcl st /\
  InvWBCoh st /\ InvWB topo st /\
  MesiDownLockInv topo st.

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
              Hin: In oidx (c_li_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl Hin)) Horq);
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
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    dest; split; intros.
    - destruct H5 as [idm [? ?]].
      apply InMP_enqMsgs_or in H5.
      destruct H5; [|apply H; auto; do 2 red; eauto].
      apply in_map with (f:= idOf) in H5; simpl in H5.
      apply H1 in H5; simpl in H5.
      exfalso; eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
        * destruct idm as [midx msg]; inv H6.
          simpl; tauto.
    - destruct H5 as [idm [? ?]].
      apply InMP_enqMsgs_or in H5.
      destruct H5; [|apply H3; auto; do 2 red; eauto].
      apply in_map with (f:= idOf) in H5; simpl in H5.
      apply H1 in H5; simpl in H5.
      exfalso; eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
        * destruct idm as [midx msg]; inv H6.
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
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    dest; split; intros.
    - destruct H4 as [idm [? ?]].
      apply InMP_deqMsgs in H4.
      apply H; auto.
      do 2 red; eauto.
    - destruct H4 as [idm [? ?]].
      apply InMP_deqMsgs in H4.
      apply H2; auto.
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
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    dest; split; intros.
    - apply H; auto.
      destruct H5 as [idm [? ?]].
      apply InMP_enqMP_or in H5; destruct H5.
      + dest; subst.
        exfalso; inv H6; auto.
      + do 2 red; eauto.
    - apply H3; auto.
      destruct H5 as [idm [? ?]].
      apply InMP_enqMP_or in H5; destruct H5.
      + dest; subst.
        exfalso; inv H6; auto.
      + do 2 red; eauto.
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
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    dest; split; intros.
    - apply H; auto.
      destruct H3 as [idm [? ?]].
      apply InMP_deqMP in H3.
      do 2 red; eauto.
    - apply H1; auto.
      destruct H3 as [idm [? ?]].
      apply InMP_deqMP in H3.
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
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    dest; split; intros.
    - apply H; auto.
      destruct H3 as [idm [? ?]].
      apply InMP_deqMsgs in H3.
      do 2 red; eauto.
    - apply H1; auto.
      destruct H3 as [idm [? ?]].
      apply InMP_deqMsgs in H3.
      do 2 red; eauto.
  Qed.

  (* Lemma InvWB_update_status_NoRqI: *)
  (*   forall oss orqs msgs, *)
  (*     InvWB topo {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} -> *)
  (*     forall oidx (ost: OState) orq rqid, *)
  (*       NoRqI oidx msgs -> *)
  (*       orq@[downRq] = Some rqid -> *)
  (*       InvWB topo {| bst_oss:= oss +[oidx <- ost]; *)
  (*                     bst_orqs:= orqs +[oidx <- orq]; *)
  (*                     bst_msgs:= msgs |}. *)
  (* Proof. *)
  (*   unfold InvWB; simpl; intros. *)
  (*   specialize (H _ _ H2). *)
  (*   mred; simpl. *)
  (*   - exfalso. *)
  (*     apply parentIdxOf_not_eq in H2; [|apply mesi_WfDTree]. *)
  (*     auto. *)
  (*   - destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto. *)
  (*     destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto. *)
  (*     split; intros. *)
  (*     + exfalso. *)
  (*       destruct H4 as [idm [? ?]]. *)
  (*       specialize (H0 _ H4). *)
  (*       red in H0; rewrite H5 in H0. *)
  (*       unfold map in H0. *)
  (*       rewrite caseDec_head_neq in H0 by discriminate. *)
  (*       rewrite caseDec_head_eq in H0 by reflexivity. *)
  (*       auto. *)
  (*     + exfalso. *)
  (*       destruct H4 as [idm [? ?]]. *)
  (*       specialize (H0 _ H4). *)
  (*       red in H0; rewrite H5 in H0. *)
  (*       unfold map in H0. *)
  (*       rewrite caseDec_head_eq in H0 by reflexivity. *)
  (*       auto. *)
  (*   - destruct (oss@[oidx0]) as [ost0|] eqn:Host0; simpl in *; auto. *)
  (*     split; intros. *)
  (*     all: exfalso; red in H3; dest; congruence. *)
  (* Qed. *)

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

  Lemma mesi_InvWB_step:
    Invariant.InvStep impl step_m (InvWB topo).
  Proof.
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
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

          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).

            Ltac solve_InvWB_by_NoRqI :=
              repeat
                match goal with
                | [Hn: NoRqI ?oidx ?msgs, Hi: ObjInvWRq ?oidx ?msgs |- _] =>
                  exfalso; eapply MsgExistsSig_MsgsNotExist_false;
                  [eassumption| |eassumption]; simpl; tauto
                | [Hn: NoRqI ?oidx ?msgs, Hi: ObjInvRq ?oidx ?msgs |- _] =>
                  exfalso; eapply MsgExistsSig_MsgsNotExist_false;
                  [eassumption| |eassumption]; simpl; tauto
                end.

            split; intros.
            all: solve_InvWB_by_NoRqI.
          }
          { admit. (* must [oidx0 = cidx] by [ObjDirME]; then not [ObjInvWRq] .. *) }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.

          Ltac solve_InvWB_by_downlock :=
            repeat
              match goal with
              | [Hn: ObjDirME _ _ _ |- _] => red in Hn; dest; mred; fail
              | [Hn: ObjDirE _ _ _ |- _] => red in Hn; dest; mred; fail
              end.

          split; intros.
          all: solve_InvWB_by_downlock.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.

          { assert (NoRqI oidx msgs)
              by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
            split; intros.
            all: solve_InvWB_by_NoRqI.
          }
          { split; intros.
            { (* must [oidx0 = cidx] by [ObjDirME]; then not [ObjInvWRq] .. *)
              admit.
            }
            { Ltac solve_InvWB_by_diff_dir :=
                match goal with
                | [Hn: ObjDirME _ _ _ |- _] =>
                  red in Hn; dest; simpl in *; solve_mesi
                | [Hn: ObjDirE _ _ _ |- _] =>
                  red in Hn; dest; simpl in *; solve_mesi
                end.
                solve_InvWB_by_diff_dir.
            }
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          split; intros.
          all: solve_InvWB_by_downlock.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          split; intros.
          all: solve_InvWB_by_downlock.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          split; intros.
          all: solve_InvWB_by_diff_dir.
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
            split; intros.
            all: solve_InvWB_by_NoRqI.
          }
          { split; intros.
            all: solve_InvWB_by_diff_dir.
          }
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
        }

        { disc_rule_conds_ex.
          simpl_InvWB_msgs.
          disc_InvWB.
          split; intros.
          all: solve_InvWB_by_diff_dir.
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
            split; intros.
            all: solve_InvWB_by_NoRqI.
          }
          { split; intros.
            all: solve_InvWB_by_diff_dir.
          }
        }

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

End InvWB.

Section InvWBCoh.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvWBCoh_init:
    Invariant.InvInit impl InvWBCoh.
  Proof.
    do 2 (red; simpl).
    intros.
    destruct (implOStatesInit tr)@[oidx] as [orq|] eqn:Host; simpl; auto.
    destruct (in_dec idx_dec oidx (c_li_indices cifc ++ c_l1_indices cifc)).
    - subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
      inv i.
      + rewrite implOStatesInit_value_root in Host by assumption.
        inv Host.
        red; intros.
        do 2 (red in H); dest_in.
      + rewrite implOStatesInit_value_non_root in Host by assumption.
        inv Host.
        red; intros.
        do 2 (red in H0); dest_in.
    - rewrite implOStatesInit_None in Host by assumption.
      discriminate.
  Qed.

  Lemma mesi_InvWBCoh_ext_in:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvWBCoh {| bst_oss := oss; bst_orqs := orqs; bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    apply InMP_enqMsgs_or in H2.
    destruct H2; [|eapply H; eauto].
    apply in_map with (f:= idOf) in H2; simpl in H2.
    apply H1 in H2; simpl in H2.
    exfalso; eapply DisjList_In_1.
    - apply tree2Topo_minds_merqs_disj.
    - eassumption.
    - eapply tree2Topo_obj_chns_minds_SubList.
      + specialize (H0 oidx); simpl in H0.
        rewrite Host in H0; simpl in H0.
        eassumption.
      + destruct idm as [midx msg]; inv H3.
        simpl; tauto.
  Qed.

  Lemma mesi_InvWBCoh_ext_out:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        InvWBCoh {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros; apply InMP_deqMsgs in H1; auto.
  Qed.

  Lemma InvWBCoh_no_update:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (post nost: OState),
        oss@[oidx] = Some post ->
        nost#[val] = post#[val] ->
        nost#[owned] = post#[owned] ->
        nost#[status] = post#[status] ->
        nost#[dir].(dir_st) = post#[dir].(dir_st) ->
        InvWBCoh {| bst_oss:= oss +[oidx <- nost];
                 bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    mred; simpl; auto.
    specialize (H oidx).
    rewrite H0 in H; simpl in H.
    red; intros.
    specialize (H _ H5 H6); dest.
    split; [simpl in *; congruence|].
    unfold ObjOwned in *; intros; simpl in *; dest.
    rewrite H1.
    apply H7.
    split.
    - rewrite <-H3; assumption.
    - rewrite <-H2; assumption.
  Qed.

  Lemma InvWBCoh_update_status_NoRqI:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (ost: OState),
        NoRqI oidx msgs ->
        InvWBCoh {| bst_oss:= oss +[oidx <- ost];
                 bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    mred; simpl; auto.
    red; intros.
    specialize (H0 _ H1).
    red in H0; rewrite H2 in H0.
    unfold map in H0.
    rewrite caseDec_head_neq in H0 by discriminate.
    rewrite caseDec_head_eq in H0 by reflexivity.
    exfalso; auto.
  Qed.

  Lemma InvWBCoh_enqMP_valid:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx ost midx msg,
        oss@[oidx] = Some ost ->
        ost#[dir].(dir_st) = mesiI ->
        midx = rqUpFrom oidx ->
        msg.(msg_id) = mesiInvWRq ->
        msg.(msg_value) = ost#[val] ->
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    destruct (idx_dec oidx0 oidx); subst.
    - specialize (H oidx).
      rewrite H0 in *; simpl in *.
      red; intros.
      apply InMP_enqMP_or in H2; destruct H2.
      + dest; simpl in *.
        split; [assumption|].
        intros; inv H5; assumption.
      + apply H; auto.
    - specialize (H oidx0).
      destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
      red; intros.
      apply InMP_enqMP_or in H2; destruct H2.
      + exfalso; dest; subst.
        inv H5; rewrite H2 in H7; inv H7; auto.
      + apply H; auto.
  Qed.

  Lemma InvWBCoh_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvWRq ->
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    apply InMP_enqMP_or in H1; destruct H1; auto.
    dest; subst.
    destruct idm as [midx msg]; simpl in *.
    inv H2; exfalso; auto.
  Qed.
  
  Lemma InvWBCoh_other_msg_id_enqMsgs:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvWRq) nmsgs ->
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvWBCoh_other_msg_id_enqMP; assumption.
  Qed.

  Lemma InvWBCoh_deqMP:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx,
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros; apply InMP_deqMP in H0; auto.
  Qed.

  Lemma InvWBCoh_deqMsgs:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall minds,
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= deqMsgs minds msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros; apply InMP_deqMsgs in H0; auto.
  Qed.

  Ltac simpl_InvWBCoh_enqMP :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac simpl_InvWBCoh_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    simpl_InvWBCoh_enqMP.

  Ltac simpl_InvWBCoh :=
    repeat
      (first [apply InvWBCoh_other_msg_id_enqMP; [|simpl_InvWBCoh_enqMP..]
             |apply InvWBCoh_other_msg_id_enqMsgs; [|simpl_InvWBCoh_enqMsgs]
             |apply InvWBCoh_deqMP
             |apply InvWBCoh_deqMsgs
             |apply InvWBCoh_update_status_NoRqI; [|assumption]
             |eapply InvWBCoh_no_update; [|eauto; fail..]
             |assumption]).

  Ltac solve_InvWBCoh :=
    let oidx := fresh "oidx" in
    red; simpl; intros oidx;
    match goal with
    | [Hi: InvWBCoh _ |- _] =>
      specialize (Hi oidx); simpl in Hi
    end;
    mred; simpl;
    let Hin := fresh "H" in
    let Hsig := fresh "H" in
    red; intros ? Hin Hsig;
    match goal with
    | [Hc: CohInvRq _ _ _ |- _] =>
      specialize (Hc _ Hin Hsig); dest
    end;
    simpl in *;
    solve [exfalso; solve_mesi|
           (* this is so arbitrary, but it works for all the remains *)
           split; [solve_mesi|];
           unfold ObjOwned; simpl; intros; dest; discriminate].

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

  Lemma mesi_InvWBCoh_step:
    Invariant.InvStep impl step_m InvWBCoh.
  Proof.
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    inv H1; [assumption
            |apply mesi_InvWBCoh_ext_in; auto
            |apply mesi_InvWBCoh_ext_out; auto
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
        dest_in; disc_rule_conds_ex.

        all: try (simpl_InvWBCoh; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvWBCoh).
      }

      dest_in.
      { disc_rule_conds_ex.
        derive_MesiDownLockInv oidx.
        simpl_InvWBCoh; solve_InvWBCoh.
      }
      { disc_rule_conds_ex.
        derive_MesiDownLockInv oidx.
        simpl_InvWBCoh; solve_InvWBCoh.
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
        dest_in; disc_rule_conds_ex.

        all: try (simpl_InvWBCoh; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvWBCoh).
      }

      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvWBCoh; fail).
      all: try (assert (NoRqI oidx msgs)
                 by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                simpl_InvWBCoh).
      all: try (derive_footprint_info_basis oidx;
                assert (NoRqI oidx msgs)
                  by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx);
                simpl_InvWBCoh).
      all: try (simpl_InvWBCoh; solve_InvWBCoh; fail).
      all: try (derive_MesiDownLockInv oidx;
                simpl_InvWBCoh; solve_InvWBCoh; fail).
      { eapply InvWBCoh_enqMP_valid; eauto. }

    - (*! Cases for L1 caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Do case analysis per a rule. *)
      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvWBCoh; fail).
      all: try (assert (NoRqI oidx msgs)
                 by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                simpl_InvWBCoh).
      all: try (derive_footprint_info_basis oidx;
                assert (NoRqI oidx msgs)
                  by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx);
                simpl_InvWBCoh).
      all: try (simpl_InvWBCoh; solve_InvWBCoh; fail).
      { eapply InvWBCoh_enqMP_valid; eauto. }

  Qed.

  Theorem mesi_InvWBCoh_ok:
    InvReachable impl step_m InvWBCoh.
  Proof.
    apply inv_reachable.
    - apply mesi_InvWBCoh_init.
    - apply mesi_InvWBCoh_step.
  Qed.

End InvWBCoh.

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

Ltac derive_ObjInvWRq oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjInvWRq oidx msgs)
      by (eexists; split;
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

Ltac disc_InvWBCoh_inv cidx Hinv :=
  specialize (Hinv cidx); simpl in Hinv;
  disc_rule_conds_ex;
  match goal with
  | [Hcoh: CohInvRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
    specialize (Hcoh _ (FirstMP_InMP Hfm));
    unfold sigOf in Hcoh; simpl in Hcoh;
    specialize (Hcoh ltac:(congruence));
    destruct Hcoh as [_ Hcoh];
    specialize (Hcoh Ho)
  end.

Ltac disc_InvWB cidx Hinv :=
  match goal with
  | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
    specialize (Hinv _ _ Hp); simpl in Hinv;
    disc_rule_conds_ex
  end.

Hint Unfold NoRsI ImplOStateMESI: RuleConds.
Hint Unfold InvForSim: RuleConds.

