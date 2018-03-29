Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.
Require Import Simulation Synthesis PredMsg.

Require Import SingleValue.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Inv.

  Definition SvmInv (ist: TState) :=
    (exists post pstt pv,
        (tst_oss ist)@[parentIdx] = Some post /\
        post@[statusIdx] = Some (VNat pstt) /\
        (pstt = stI \/ pstt = stS \/ pstt = stM) /\
        post@[valueIdx] = Some pv) /\
    (exists c1ost c1stt c1v,
        (tst_oss ist)@[child1Idx] = Some c1ost /\
        c1ost@[statusIdx] = Some (VNat c1stt) /\
        (c1stt = stI \/ c1stt = stS \/ c1stt = stM) /\
        c1ost@[valueIdx] = Some c1v) /\
    (exists c2ost c2stt c2v,
        (tst_oss ist)@[child2Idx] = Some c2ost /\
        c2ost@[statusIdx] = Some (VNat c2stt) /\
        (c2stt = stI \/ c2stt = stS \/ c2stt = stM) /\
        c2ost@[valueIdx] = Some c2v).

End Inv.

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
      poss = noss /\ ImplStateMSI poss outv.

  (** --(v)--> [. -> MSI(v)] --(.)--> *)
  Definition PredSet: PredOS :=
    fun inv poss outv noss => ImplStateMI noss inv.

  (** --(.)--> [SI(v)|{tinds} -> SI(v)|{tinds}] --(v)--> *)
  Definition PredGetSI (tinds: list IdxT): PredOS :=
    fun inv poss outv noss =>
      M.restrict poss tinds = M.restrict noss tinds /\
      ImplStateSI (M.restrict poss tinds) outv.

  (** --(.)--> [. -> I|{tinds}] --(v)--> *)
  Definition PredSetI (tinds: list IdxT): PredOS :=
    fun _ _ _ noss =>
      ImplStateI (M.restrict noss tinds).

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

End Facts.

