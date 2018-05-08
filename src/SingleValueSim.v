Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Topology Semantics SemFacts StepT.
Require Import Invariant Simulation TrsSim SerialFacts.
Require Import Synthesis SynthesisTactics PredMsg Blocking.

Require Import SingleValue.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section RPreconds.

  Definition ImplOStatusM: RPrecond :=
    fun ost _ _ => ost@[statusIdx] = Some (VNat stM).

  Definition ImplOStatusS: RPrecond :=
    fun ost _ _ => ost@[statusIdx] = Some (VNat stS).
  
  Definition ImplOStatusI: RPrecond :=
    fun ost _ _ => ost@[statusIdx] = Some (VNat stI).

End RPreconds.

Section Predicates.

  Definition ImplStateI: OStatesFP :=
    OStateForallP
      (fun oidx ost =>
         forall stt, 
           ost@[statusIdx] = Some (VNat stt) ->
           stt = stI).

  Definition ImplStateMI (v: Value): OStatesFP :=
    fun inds ioss =>
      exists midx,
        In midx inds /\
        OStateExistsP
          (fun oidx ost =>
             ost@[statusIdx] = Some (VNat stM) /\
             ost@[valueIdx] = Some v) midx ioss /\
        OStateForallP
          (fun oidx ost =>
             oidx <> midx ->
             forall stt,
               ost@[statusIdx] = Some (VNat stt) ->
               stt = stI) inds ioss.

  Definition ImplStateSI (v: Value): OStatesFP :=
    fun inds ioss =>
      (exists midx,
          In midx inds /\
          OStateExistsP
            (fun oidx ost => ost@[statusIdx] = Some (VNat stS)) midx ioss) /\
      OStateForallP
        (fun oidx ost =>
           forall stt,
             ost@[statusIdx] = Some (VNat stt) ->
             match stt with
             | 0 (* stI *) => True
             | 1 (* stS *) => ost@[valueIdx] = Some v
             | 2 (* stM *) => False
             | _ => False
             end) inds ioss.

  Definition ImplStateMSI (v: Value): OStatesFP :=
    fun inds ioss => ImplStateMI v inds ioss \/ ImplStateSI v inds ioss.

  (* NOTE: Here indeed binary predicates are required; if the predicate only
   * takes a poststate, then we cannot specify that the coherence value should
   * not be changed.
   *)
  (** --(.)--> [MSI(v) -> MSI(v)] --(v)--> *)
  Definition PredGet (tinds: list IdxT): PredOS :=
    fun _ poss outv noss =>
      ImplStateMSI outv tinds poss /\ ImplStateMSI outv tinds noss.

  (** --(v)--> [. -> MSI(v)] --(.)--> *)
  Definition PredSet (tinds: list IdxT): PredOS :=
    fun inv _ _ noss => ImplStateMI inv tinds noss.

  (** --(.)--> [MSI(v)|{tinds} -> SI(v)|{tinds}] --(v)--> *)
  Definition PredGetSI (tinds: list IdxT): PredOS :=
    fun _ poss outv noss =>
      ImplStateMSI outv tinds poss /\
      ImplStateSI outv tinds noss.

  (** --(.)--> [. -> I|{tinds}] --(v)--> *)
  Definition PredSetI (tinds: list IdxT): PredOS :=
    fun _ _ _ noss =>
      ImplStateI tinds noss.

  Definition OPredGetS: OPred :=
    fun inv post outv nost =>
      nost@[statusIdx] = Some (VNat stS) /\
      nost@[valueIdx] = Some outv.

  (* Definition getRqFwdF (topo: Tree unit) (rqpmid: PMsgId TMsg): list (PMsgId TMsg) := *)
  (*   let from := mid_from (pmid_mid rqpmid) in *)
  (*   let this := mid_to (pmid_mid rqpmid) in *)
  (*   map (fun tofwds => *)
  (*          {| pmid_mid := *)
  (*               {| mid_addr := *)
  (*                    {| ma_from := this; *)
  (*                       ma_to := fst tofwds; *)
  (*                       ma_chn := rqChn |}; *)
  (*                  mid_tid := mid_tid (pmid_mid rqpmid) |}; *)
  (*             pmid_pred := *)
  (*               {| pred_os := PredGetSI (snd tofwds); *)
  (*                  pred_mp := ⊤ |} *)
  (*          |}) *)
  (*       (getFwds topo from this). *)
  
End Predicates.

Section Sim.
  Variables erq1 erq2 ers1 ers2: nat.
  Hypothesis (Hmvalid: NoDup ([c1pRq; c1pRs; pc1; c2pRq; c2pRs; pc2]
                                ++ [erq1; erq2; ers1; ers2])).

  Local Notation spec := (spec Hmvalid).
  Local Notation impl0 := (impl0 Hmvalid).

  (** Global invariants *)

  Definition SvmInvs :=
    ValidTrss impl0 /\i BlockedInv /\i ValidTidState.

  (** Simulation between [TState]s *)

  Definition SvmSpecState (v: Value) (soss: OStates) :=
    exists sost,
      soss@[specIdx] = Some sost /\
      sost@[valueIdx] = Some v.

  Definition SvmR (tinds: list IdxT): OStates -> OStates -> Prop :=
    fun ioss soss =>
      exists cv,
        ImplStateMSI cv tinds ioss /\ SvmSpecState cv soss.

  Definition SvmSpecORqs (sorqs: ORqs TMsg) :=
    exists sorq,
      sorqs@[specIdx] = Some sorq.

  Definition SvmSim {SysT} `{IsSystem SysT} (impl: SysT): TState -> TState -> Prop :=
    fun ist sst =>
      SvmR (oindsOf impl) (tst_oss ist) (tst_oss sst) /\
      SvmSpecORqs (tst_orqs sst) /\
      SimMP ist sst.

  Section Facts.

    Lemma SvmSim_init:
      SvmSim impl0 (initsOf impl0) (initsOf spec).
    Proof.
      repeat esplit.
      right; repeat econstructor;
        cbn; intros; inv H; cbn; reflexivity.
    Qed.

    Lemma SvmSim_MsgsSim:
      MsgsSim (SvmSim impl0).
    Proof.
    Admitted.

    Lemma SvmInvs_init:
      SvmInvs (initsOf impl0).
    Proof.
      repeat constructor.
      - hnf; intros.
        elim H.
      - apply ForallMP_emptyMP.
    Qed.

    (*! Correctness of the initial system *)

    Theorem impl0_synth_ok:
      SynthOk spec (SvmSim impl0) SvmInvs impl0.
    Proof.
      synthOk_init.
      - apply SvmSim_init.
      - apply SvmInvs_init.
      - split.
        + apply TrsSimulates_no_rules; try reflexivity.
          * apply InvStep_no_rules; [|reflexivity].
            repeat apply MsgsInv_invAnd.
            { admit. }
            { apply BlockedInv_MsgsInv. }
            { apply ValidTidState_MsgsInv. }
          * hnf; intros.
            destruct H; destruct H; assumption.
          * apply SvmSim_MsgsSim.
          * hnf; intros.
            destruct H; destruct H0; assumption.
        + apply InvStep_no_rules; [|reflexivity].
          repeat apply MsgsInv_invAnd.
          * admit.
          * apply BlockedInv_MsgsInv.
          * apply ValidTidState_MsgsInv.
      - apply serializable_no_rules; reflexivity.
    Admitted.

    Theorem impl0_ok:
      (steps step_t) # (steps step_t) |-- impl0 ⊑ spec.
    Proof.
      eapply synthOk_refinement.
      eapply impl0_synth_ok.
    Qed.
    
  End Facts.
  
End Sim.

Section Facts.

  Lemma impl_state_MI_SI_contra:
    forall tinds ioss v1 v2,
      ImplStateMI v1 tinds ioss ->
      ImplStateSI v2 tinds ioss ->
      False.
  Proof.
    unfold ImplStateMI, ImplStateSI; intros.
    dest; hnf in *; dest.
    ostatesfp_apply H H1.
    ostatesfp_red.
  Qed.

  Lemma impl_state_MI_restrict_SI_contra:
    forall tinds dom ioss v1 v2,
      dom <> nil ->
      SubList dom tinds ->
      ImplStateMI v1 tinds ioss ->
      ImplStateSI v2 dom ioss ->
      False.
  Proof.
    unfold ImplStateMI, ImplStateSI; intros.
    dest; hnf in *; dest.
    assert (In x tinds) by auto.
    destruct (x ==n x0); subst.
    - mred_find.
    - ostatesfp_apply H10 H6.
      ostatesfp_red.
  Qed.
  
  Lemma impl_state_SI_value_eq:
    forall tinds ioss v1,
      ImplStateSI v1 tinds ioss ->
      forall v2,
        ImplStateSI v2 tinds ioss ->
        v1 = v2.
  Proof.
    unfold ImplStateSI; intros.
    dest; hnf in *; dest.
    ostatesfp_apply H H1.
    ostatesfp_apply H H2.
    ostatesfp_red.
  Qed.

  Lemma impl_state_restrict_SI_value_eq:
    forall tinds ioss v1,
      ImplStateSI v1 tinds ioss ->
      forall dom v2,
        dom <> nil ->
        SubList dom tinds ->
        ImplStateSI v2 dom ioss ->
        v1 = v2.
  Proof.
    unfold ImplStateSI; intros.
    dest; hnf in *; dest.
    assert (In x tinds) by auto.
    ostatesfp_apply H9 H4.
    ostatesfp_apply H9 H3.
    ostatesfp_red.
  Qed.

  Lemma impl_state_MI_value_eq:
    forall tinds ioss v1,
      ImplStateMI v1 tinds ioss ->
      forall v2,
        ImplStateMI v2 tinds ioss ->
        v1 = v2.
  Proof.
    unfold ImplStateMI; intros.
    dest; hnf in *; dest.
    destruct (x0 ==n x); subst.
    - mred_find; reflexivity.
    - ostatesfp_apply H H2.
      ostatesfp_red.
  Qed.

  Lemma impl_state_MSI_value_eq:
    forall tinds ioss v1,
      ImplStateMSI v1 tinds ioss ->
      forall v2,
        ImplStateMSI v2 tinds ioss ->
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
    forall tinds ioss v1,
      ImplStateMSI v1 tinds ioss ->
      forall dom v2,
        dom <> nil ->
        SubList dom tinds ->
        ImplStateSI v2 dom ioss ->
        v1 = v2.
  Proof.
    unfold ImplStateMSI; intros.
    destruct H.
    - exfalso; eauto using impl_state_MI_restrict_SI_contra.
    - eauto using impl_state_restrict_SI_value_eq.
  Qed.

End Facts.

