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

Section OStatesP.

  Definition OStatesP := OStates -> Prop.
  Definition OStateP := IdxT -> OState -> Prop.

  Definition OStateForallP (ostp: OStateP): OStatesP :=
    fun oss =>
      forall oidx,
        oss@[oidx] >>=[True] (fun ost => ostp oidx ost).

  Definition OStateExistsP (ostp: OStateP) (oidx: IdxT): OStatesP :=
    fun oss =>
      exists ost,
        oss@[oidx] = Some ost /\ ostp oidx ost.

  Theorem OStateForallP_reflect_1:
    forall oss dom,
      M.KeysEquiv oss dom ->
      forall ostp,
        OStateForallP ostp oss ->
        Forall (fun oidx =>
                  exists ost,
                    oss@[oidx] = Some ost /\ ostp oidx ost) dom.
  Proof.
    intros.
    apply Forall_forall; intros.
    eapply H in H1.
    apply M.F.P.F.in_find_iff in H1.
    specialize (H0 x).
    remember (oss@[x]) as oost.
    destruct oost as [ost|]; [|exfalso; auto].
    eauto.
  Qed.
  
  Theorem OStateForallP_reflect_2:
    forall oss dom,
      M.KeysEquiv oss dom ->
      forall ostp,
        Forall (fun oidx =>
                  oss@[oidx] >>=[True] (fun ost => ostp oidx ost)) dom ->
        OStateForallP ostp oss.
  Proof.
    intros; red; intros.
    remember (oss@[oidx]) as oost.
    destruct oost as [ost|]; simpl; auto.
    assert (M.In oidx oss).
    { apply M.F.P.F.in_find_iff.
      rewrite <-Heqoost; discriminate.
    }
    eapply H in H1.
    eapply Forall_forall in H0; eauto.
    rewrite <-Heqoost in H0; auto.
  Qed.

End OStatesP.

Section Predicates.

  Definition ImplStateI: OStatesP :=
    OStateForallP
      (fun oidx ost =>
         forall stt, 
           ost@[statusIdx] = Some (VNat stt) ->
           stt = stI).

  Definition ImplStateMI (v: Value): OStatesP :=
    fun ioss =>
      exists midx,
        OStateExistsP
          (fun oidx ost =>
             ost@[statusIdx] = Some (VNat stM) /\
             ost@[valueIdx] = Some v) midx ioss /\
        OStateForallP
          (fun oidx ost =>
             oidx <> midx ->
             forall stt,
               ost@[statusIdx] = Some (VNat stt) ->
               stt = stI) ioss.

  Definition ImplStateSI (v: Value): OStatesP :=
    fun ioss =>
      exists midx,
        OStateExistsP
          (fun oidx ost => ost@[statusIdx] = Some (VNat stS)) midx ioss /\
        OStateForallP
          (fun oidx ost =>
             forall stt,
               ost@[statusIdx] = Some (VNat stt) ->
               match stt with
               | 0 (* stI *) => True
               | 1 (* stS *) => ost@[valueIdx] = Some v
               | 2 (* stM *) => False
               | _ => False
               end) ioss.

  Definition ImplStateMSI (v: Value): OStatesP :=
    fun ioss => ImplStateMI v ioss \/ ImplStateSI v ioss.

  (* NOTE: Here indeed binary predicates are required; if the predicate only
   * takes a poststate, then we cannot specify that the coherence value should
   * not be changed.
   *)
  (** --(.)--> [MSI(v) -> MSI(v)] --(v)--> *)
  Definition PredGet: PredOS :=
    fun inv poss outv noss =>
      ImplStateMSI outv poss /\ ImplStateMSI outv noss.

  (** --(v)--> [. -> MSI(v)] --(.)--> *)
  Definition PredSet: PredOS :=
    fun inv poss outv noss => ImplStateMI inv noss.

  (** --(.)--> [SI(v)|{tinds} -> SI(v)|{tinds}] --(v)--> *)
  Definition PredGetSI (tinds: list IdxT): PredOS :=
    fun inv poss outv noss =>
      ImplStateSI outv (M.restrict poss tinds) /\
      ImplStateSI outv (M.restrict noss tinds).

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

  Definition SpecState (v: Value) (soss: OStates) :=
    exists sost,
      soss@[specIdx] = Some sost /\
      sost@[valueIdx] = Some v.

  Definition SvmR (ioss soss: OStates): Prop :=
    exists cv,
      ImplStateMSI cv ioss /\ SpecState cv soss.

  Definition SvmSim (ist sst: TState) :=
    SvmR (tst_oss ist) (tst_oss sst) /\
    SimMP svmMsgF (tst_msgs ist) (tst_msgs sst).

End Sim.

Section Facts.

  Lemma impl_state_MI_SI_contra:
    forall ioss v1 v2,
      ImplStateMI v1 ioss ->
      ImplStateSI v2 ioss ->
      False.
  Proof.
    unfold ImplStateMI, ImplStateSI; intros.
    dest; hnf in *; dest.
    specialize (H1 x0); rewrite H in H1; simpl in H1.
    specialize (H1 _ H4); auto.
  Qed.

  Lemma impl_state_MI_restrict_SI_contra:
    forall ioss v1 v2 dom,
      dom <> nil ->
      ImplStateMI v1 ioss ->
      ImplStateSI v2 (M.restrict ioss dom) ->
      False.
  Proof.
    unfold ImplStateMI, ImplStateSI; intros.
    dest; hnf in *; dest.
    assert (ioss@[x] = Some x1).
    { rewrite M.restrict_find in H1; findeq.
      { destruct (in_dec _ _ _); [auto|discriminate]. }
      { destruct (in_dec _ _ _); discriminate. }
    }
    destruct (x ==n x0); subst.
    - mred_find.
    - specialize (H3 x); rewrite H7 in H3; simpl in H3.
      specialize (H3 n _ H4); discriminate.
  Qed.
  
  Lemma impl_state_SI_value_eq:
    forall ioss v1,
      ImplStateSI v1 ioss ->
      forall v2,
        ImplStateSI v2 ioss ->
        v1 = v2.
  Proof.
    unfold ImplStateSI; intros.
    dest; hnf in *; dest.
    specialize (H2 x); rewrite H0 in H2; simpl in H2.
    specialize (H2 _ H3).
    specialize (H1 x); rewrite H0 in H1; simpl in H1.
    specialize (H1 _ H3).
    simpl in *; mred_find.
    reflexivity.
  Qed.

  Lemma impl_state_restrict_SI_value_eq:
    forall ioss v1,
      ImplStateSI v1 ioss ->
      forall dom v2,
        dom <> nil ->
        ImplStateSI v2 (M.restrict ioss dom) ->
        v1 = v2.
  Proof.
    unfold ImplStateSI; intros.
    dest; hnf in *; dest.
    assert (ioss@[x] = Some x1).
    { rewrite M.restrict_find in H1; findeq.
      { destruct (in_dec _ _ _); [auto|discriminate]. }
      { destruct (in_dec _ _ _); discriminate. }
    }
    specialize (H2 x); rewrite H1 in H2; simpl in H2.
    specialize (H2 _ H4).
    specialize (H3 x); rewrite H6 in H3; simpl in H3.
    specialize (H3 _ H4).
    simpl in *; mred_find.
    reflexivity.
  Qed.

  Lemma impl_state_MI_value_eq:
    forall ioss v1,
      ImplStateMI v1 ioss ->
      forall v2,
        ImplStateMI v2 ioss ->
        v1 = v2.
  Proof.
    unfold ImplStateMI; intros.
    dest; hnf in *; dest.
    destruct (x0 ==n x); subst.
    - mred_find; reflexivity.
    - specialize (H1 x0); rewrite H in H1; simpl in H1.
      specialize (H1 n _ H5); discriminate.
  Qed.

  Lemma impl_state_MSI_value_eq:
    forall ioss v1,
      ImplStateMSI v1 ioss ->
      forall v2,
        ImplStateMSI v2 ioss ->
        v1 = v2.
  Proof.
    unfold ImplStateMSI; intros.
    dest; hnf in *; dest.
    destruct H, H0.
    - eauto using impl_state_MI_value_eq.
    - exfalso; eauto using impl_state_MI_SI_contra.
    - exfalso; eauto using impl_state_MI_SI_contra.
    - eauto using impl_state_SI_value_eq.
  Qed.

  Lemma impl_state_MSI_restrict_SI_value_eq:
    forall ioss v1,
      ImplStateMSI v1 ioss ->
      forall dom v2,
        dom <> nil ->
        ImplStateSI v2 (M.restrict ioss dom) ->
        v1 = v2.
  Proof.
    unfold ImplStateMSI; intros.
    destruct H.
    - exfalso; eauto using impl_state_MI_restrict_SI_contra.
    - eauto using impl_state_restrict_SI_value_eq.
  Qed.

End Facts.

