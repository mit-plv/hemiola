Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Topology Semantics StepT.
Require Import Simulation Synthesis PredMsg.

Require Import SingleValue.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(* [M.restrict] is used to define some predicates and we don't want it to be
 * unfolded during reductions. When [M.restrict] is applied to finite maps,
 * reduction tactics like [cbn] reduce it too much.
 *)
Global Opaque M.restrict.

Section RPreconds.

  Definition ImplOStatusM: RPrecond :=
    fun ost _ => ost@[statusIdx] = Some (VNat stM).

  Definition ImplOStatusS: RPrecond :=
    fun ost _ => ost@[statusIdx] = Some (VNat stS).
  
  Definition ImplOStatusI: RPrecond :=
    fun ost _ => ost@[statusIdx] = Some (VNat stI).

End RPreconds.
             
Section Predicates.

  Definition ImplStateI (ioss: OStates) :=
    forall oidx ost stt,
      ioss@[oidx] = Some ost ->
      ost@[statusIdx] = Some (VNat stt) ->
      stt = stI.

  Definition ImplStateMI (ioss: OStates) (v: Value) :=
    exists midx most,
      ioss@[midx] = Some most /\
      most@[statusIdx] = Some (VNat stM) /\
      most@[valueIdx] = Some v /\
      (forall oidx ost stt,
          oidx <> midx ->
          ioss@[oidx] = Some ost ->
          ost@[statusIdx] = Some (VNat stt) ->
          stt = stI).

  Definition ImplStateSI (ioss: OStates) (v: Value) :=
    (exists midx most,
        ioss@[midx] = Some most /\
        most@[statusIdx] = Some (VNat stS)) /\
    (forall oidx ost stt,
        ioss@[oidx] = Some ost ->
        ost@[statusIdx] = Some (VNat stt) ->
        match stt with
        | 0 (* stI *) => True
        | 1 (* stS *) => ost@[valueIdx] = Some v
        | 2 (* stM *) => False
        | _ => False
        end).

  Definition ImplStateMSI (ioss: OStates) (v: Value) :=
    ImplStateMI ioss v \/ ImplStateSI ioss v.

  (* NOTE: Here indeed binary predicates are required; if the predicate only
   * takes a poststate, then we cannot specify that the coherence value should
   * not be changed.
   *)
  (** --(.)--> [MSI(v) -> MSI(v)] --(v)--> *)
  Definition PredGet: PredOS :=
    fun inv poss outv noss =>
      ImplStateMSI poss outv /\ ImplStateMSI noss outv.

  (** --(v)--> [. -> MSI(v)] --(.)--> *)
  Definition PredSet: PredOS :=
    fun inv poss outv noss => ImplStateMI noss inv.

  (** --(.)--> [SI(v)|{tinds} -> SI(v)|{tinds}] --(v)--> *)
  Definition PredGetSI (tinds: list IdxT): PredOS :=
    fun inv poss outv noss =>
      ImplStateSI (M.restrict poss tinds) outv /\
      ImplStateSI (M.restrict noss tinds) outv.

  (** --(.)--> [. -> I|{tinds}] --(v)--> *)
  Definition PredSetI (tinds: list IdxT): PredOS :=
    fun _ _ _ noss =>
      ImplStateI (M.restrict noss tinds).

  Definition OPredGetS: OPred :=
    fun inv post outv nost =>
      nost@[statusIdx] = Some (VNat stS) /\
      nost@[valueIdx] = Some outv.

  Definition getRqFwdF (topo: Tree unit) (rqpmid: PMsgId TMsg): list (PMsgId TMsg) :=
    let from := mid_from (pmid_mid rqpmid) in
    let this := mid_to (pmid_mid rqpmid) in
    map (fun tofwds =>
           {| pmid_mid :=
                {| mid_addr :=
                     {| ma_from := this;
                        ma_to := fst tofwds;
                        ma_chn := rqChn |};
                   mid_tid := mid_tid (pmid_mid rqpmid) |};
              pmid_pred :=
                {| pred_os := PredGetSI (snd tofwds);
                   pred_mp := ⊤ |}
           |})
        (getFwds topo from this).
  
End Predicates.

Section Sim.
  Variables extIdx1 extIdx2: nat.
  Hypotheses (Hiext1: isExternal impl0 extIdx1 = true)
             (Hiext2: isExternal impl0 extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Notation spec := (spec extIdx1 extIdx2).

  (** Label mapping *)
  
  Definition svmIdxF (idx: IdxT): IdxT :=
    if idx ?<n (indicesOf impl0) then specIdx else idx.

  Definition svmMsgIdF (imid: MsgId): MsgId :=
    {| mid_addr := {| ma_from := svmIdxF (mid_from imid);
                      ma_to := svmIdxF (mid_to imid);
                      ma_chn :=
                        (mid_chn imid) + (if mid_from imid ==n extIdx1
                                          then 0
                                          else if mid_to imid ==n extIdx1
                                               then 0
                                               else numChns)
                   |};
       mid_tid := mid_tid imid |}.

  Definition svmMsgF (imsg: Msg): Msg :=
    {| msg_id := svmMsgIdF (msg_id imsg);
       msg_value := msg_value imsg |}.

  Definition svmP := LabelMap svmMsgF.

  (** Simulation between [TState]s *)

  Definition SpecState (soss: OStates) (v: Value) :=
    exists sost,
      soss@[specIdx] = Some sost /\
      sost@[valueIdx] = Some v.

  Definition SvmR (ioss soss: OStates): Prop :=
    exists cv,
      ImplStateMSI ioss cv /\ SpecState soss cv.

  Definition SvmSim (ist sst: TState) :=
    SvmR (tst_oss ist) (tst_oss sst) /\
    SimMP svmMsgF (tst_msgs ist) (tst_msgs sst).

End Sim.

Section Facts.

  Lemma impl_state_MI_SI_contra:
    forall ioss v1 v2,
      ImplStateMI ioss v1 ->
      ImplStateSI ioss v2 ->
      False.
  Proof.
    unfold ImplStateMI, ImplStateSI; intros; dest.
    specialize (H1 _ _ _ H H3); auto.
  Qed.

  Lemma impl_state_MI_restrict_SI_contra:
    forall ioss v1 v2 dom,
      dom <> nil ->
      ImplStateMI ioss v1 ->
      ImplStateSI (M.restrict ioss dom) v2 ->
      False.
  Proof.
    unfold ImplStateMI, ImplStateSI; intros; dest.
    assert (ioss@[x] = Some x0).
    { rewrite M.restrict_find in H1; findeq.
      { destruct (in_dec _ _ _); [auto|discriminate]. }
      { destruct (in_dec _ _ _); discriminate. }
    }
    destruct (x ==n x1); subst.
    - mred_find.
    - specialize (H6 _ _ _ n H7 H3); discriminate.
  Qed.

  Lemma impl_state_SI_value_eq:
    forall ioss v1,
      ImplStateSI ioss v1 ->
      forall v2,
        ImplStateSI ioss v2 ->
        v1 = v2.
  Proof.
    unfold ImplStateSI; intros; dest.
    specialize (H2 _ _ _ H H4).
    specialize (H1 _ _ _ H H4).
    simpl in *; mred_find.
    reflexivity.
  Qed.

  Lemma impl_state_restrict_SI_value_eq:
    forall ioss v1,
      ImplStateSI ioss v1 ->
      forall dom v2,
        dom <> nil ->
        ImplStateSI (M.restrict ioss dom) v2 ->
        v1 = v2.
  Proof.
    unfold ImplStateSI; intros; dest.
    assert (ioss@[x] = Some x0).
    { rewrite M.restrict_find in H1; findeq.
      { destruct (in_dec _ _ _); [auto|discriminate]. }
      { destruct (in_dec _ _ _); discriminate. }
    }
    specialize (H2 _ _ _ H1 H4).
    specialize (H3 _ _ _ H6 H4).
    simpl in *; mred_find.
    reflexivity.
  Qed.

  Lemma impl_state_MI_value_eq:
    forall ioss v1,
      ImplStateMI ioss v1 ->
      forall v2,
        ImplStateMI ioss v2 ->
        v1 = v2.
  Proof.
    unfold ImplStateMI; intros; dest.
    destruct (x ==n x1); subst.
    - mred_find; reflexivity.
    - specialize (H6 _ _ _ n H0 H1); discriminate.
  Qed.

  Lemma impl_state_MSI_value_eq:
    forall ioss v1,
      ImplStateMSI ioss v1 ->
      forall v2,
        ImplStateMSI ioss v2 ->
        v1 = v2.
  Proof.
    unfold ImplStateMSI; intros.
    destruct H, H0.
    - eauto using impl_state_MI_value_eq.
    - exfalso; eauto using impl_state_MI_SI_contra.
    - exfalso; eauto using impl_state_MI_SI_contra.
    - eauto using impl_state_SI_value_eq.
  Qed.

  Lemma impl_state_MSI_restrict_SI_value_eq:
    forall ioss v1,
      ImplStateMSI ioss v1 ->
      forall dom v2,
        dom <> nil ->
        ImplStateSI (M.restrict ioss dom) v2 ->
        v1 = v2.
  Proof.
    unfold ImplStateMSI (* ImplStateMI, ImplStateSI *); intros.
    destruct H.
    - exfalso; eauto using impl_state_MI_restrict_SI_contra.
    - eauto using impl_state_restrict_SI_value_eq.
  Qed.

  Lemma impl_state_status_S_restrict_SI:
    forall ioss dom cv,
      ImplStateSI (M.restrict ioss dom) cv ->
      forall oidx nos,
        M.KeysEquiv ioss (oidx :: dom) ->
        nos@[statusIdx] = Some (VNat stS) ->
        nos@[valueIdx] = Some cv ->
        ImplStateSI (ioss +[oidx <- nos]) cv.
  Proof.
    unfold ImplStateSI; simpl; intros.
    dest; split.
    - destruct (oidx ==n x); subst.
      + exists x, nos; split; auto.
        findeq.
      + exists x, x0; split; auto.
        rewrite M.restrict_find in H.
        destruct (in_dec _ _ _); [|discriminate].
        findeq.
    - intros.
      destruct (oidx ==n oidx0); subst.
      + mred; mred_find.
        reflexivity.
      + rewrite M.find_add_2 in H5 by auto.
        assert (M.In oidx0 ioss).
        { apply M.Map.Facts.P.F.in_find_iff.
          rewrite H5; discriminate.
        }
        apply H0 in H7; inv H7.
        * elim n; reflexivity.
        * eapply H3 with (oidx:= oidx0); eauto.
          rewrite M.restrict_find.
          destruct (in_dec _ _ _); auto.
          elim n0; assumption.
  Qed.

  Lemma impl_state_status_I_restrict_SI:
    forall ioss dom cv,
      ImplStateSI (M.restrict ioss dom) cv ->
      forall oidx nos,
        M.KeysEquiv ioss (oidx :: dom) ->
        ioss@[oidx] = Some nos ->
        nos@[statusIdx] = Some (VNat stI) ->
        nos@[valueIdx] = Some cv ->
        ImplStateSI ioss cv.
  Proof.
    unfold ImplStateSI; simpl; intros.
    dest; split.
    - exists x, x0; split; auto.
      rewrite M.restrict_find in H.
      destruct (in_dec _ _ _); [|discriminate].
      findeq.
    - intros.
      destruct (oidx ==n oidx0); subst.
      + mred; mred_find.
        simpl; auto.
      + eapply H4 with (oidx:= oidx0); eauto.
        rewrite M.restrict_find.
        destruct (in_dec _ _ _); auto.
        elim n0; clear n0.
        assert (In oidx0 (oidx :: dom)).
        { apply H0, M.Map.Facts.P.F.in_find_iff.
          rewrite H6; discriminate.
        }
        destruct H8; auto.
        elim n; assumption.
  Qed.

  Lemma impl_state_status_M_restrict_I:
    forall ioss cv,
      ImplStateMI ioss cv ->
      forall oidx dom nos,
        ~ In oidx dom ->
        ioss@[oidx] = Some nos ->
        nos@[statusIdx] = Some (VNat stM) ->
        ImplStateI (M.restrict ioss dom).
  Proof.
    unfold ImplStateMI, ImplStateI; intros; dest.
    rewrite M.restrict_find in H3.
    destruct (in_dec _ _ _); [|discriminate].
    destruct (oidx ==n x); subst.
    - destruct (oidx0 ==n x); subst.
      + elim H0; assumption.
      + eapply H7; eauto.
    - specialize (H7 _ _ _ n H1 H2).
      discriminate.
  Qed.

End Facts.

