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

  Local Notation spec := (spec extIdx1 extIdx2).

  (** Label mapping *)
  
  Definition svmIdxF (idx: IdxT): IdxT :=
    if idx ?<n (indicesOf impl0) then specIdx else idx.

  Definition svmMamap (ima: MsgAddr): MsgAddr :=
    {| ma_from := svmIdxF (ma_from ima);
       ma_to := svmIdxF (ma_to ima);
       ma_chn :=
         (if ma_to ima ==n child1Idx
          then 0
          else if ma_from ima ==n child1Idx
               then 0
               else numChns) + (ma_chn ima)
    |}.

  Definition svmMsgF := liftMmap svmMamap.
  Definition svmP := liftLmap svmMsgF.

  (** Global invariants *)

  Definition SvmInvs :=
    BlockedInv /\i ValidTidState.

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
      SvmR (indicesOf impl) (tst_oss ist) (tst_oss sst) /\
      SvmSpecORqs (tst_orqs sst) /\
      SimMP svmMsgF impl (tst_msgs ist) (tst_msgs sst).

  Section Facts.

    Lemma svmMamap_ExtInjective:
      ExtInjective svmMamap impl0.
    Proof.
      (* red; intros. *)
      (* destruct ma1 as [from1 to1 chn1], ma2 as [from2 to2 chn2]. *)
      (* unfold svmMamap in H1; simpl in H1; inv H1. *)
      (* unfold maExternal, svmIdxF in *. *)
      (* unfold_idx; unfold ma_from, ma_to in *. *)
      (* destruct (from1 ?<n _); destruct (to1 ?<n _); *)
      (*   destruct (from2 ?<n _); destruct (to2 ?<n _); *)
      (*     subst; simpl in *; *)
      (*       try congruence. *)
    Admitted.

    Lemma svmMamap_ValidMsgMap:
      ValidMaMap svmMamap impl0 spec.
    Proof.
      split.
      - unfold_idx.
        unfold impl0.
        split.
        + find_if_inside.
          * Common.dest_in; cbn in *.
            { unfold id in H; rewrite <-H; reflexivity. }
            { unfold id in H0; rewrite <-H0; reflexivity. }
            { unfold id in H; rewrite <-H; reflexivity. }
          * find_if_inside; auto.
            elim n; clear n.
            Common.dest_in.
            cbn in *.
            unfold svmIdxF in H.
            find_if_inside; auto.
        + find_if_inside.
          * Common.dest_in; cbn in *.
            { unfold id in H; rewrite <-H; auto. }
            { unfold id in H0; rewrite <-H0; auto. }
            { unfold id in H; rewrite <-H; auto. }
          * find_if_inside; auto.
            elim n; clear n.
            Common.dest_in.
            cbn in *.
            unfold svmIdxF in H.
            find_if_inside; auto.
      - apply svmMamap_ExtInjective.
    Qed.

    Lemma SvmSim_init:
      SvmSim impl0 (initsOf impl0) (initsOf spec).
    Proof.
      repeat esplit.
      right; repeat econstructor;
        cbn; intros; inv H; cbn; reflexivity.
    Qed.

    Lemma SvmSim_MsgsInSim:
      MsgsInSim svmMsgF (SvmSim impl0).
    Proof.
      hnf; intros.
      hnf in *; cbn in *; dest.
      split; [|split]; auto.
      apply SimMP_ext_msg_ins; auto.
    Qed.
      
    Lemma SvmSim_MsgsOutSim:
      MsgsOutSim impl0 (liftTmap svmMsgF) (SvmSim impl0).
    Proof.
      hnf; intros.
      hnf; hnf in H0; cbn in *; dest.
      split; [|split]; auto.
      apply SimMP_ext_msg_outs; auto.
    Qed.

    Lemma SvmInvs_init:
      SvmInvs (initsOf impl0).
    Proof.
      repeat constructor.
      hnf; intros.
      elim H.
    Qed.

    (*! Correctness of the initial system *)

    Theorem impl0_synth_ok:
      SynthOk spec (SvmSim impl0) SvmInvs svmP impl0.
    Proof.
      synthOk_init.
      - apply SvmSim_init.
      - apply SvmInvs_init.
      - split.
        + apply TrsSimulates_no_rules.
          * apply svmMamap_ValidMsgMap.
          * hnf; intros.
            hnf; hnf in H; cbn in *; dest.
            repeat split; simpl; auto.
            apply SimMP_ext_msg_ins; auto.
          * hnf; intros.
            hnf; hnf in H0; cbn in *; dest.
            repeat split; simpl; auto.
            apply SimMP_ext_msg_outs; auto.
          * hnf; intros.
            hnf in H; dest; auto.
          * reflexivity.
        + apply InvStep_no_rules; [|reflexivity].
          apply MsgsInv_invAnd.
          * apply BlockedInv_MsgsInv.
          * apply ValidTidState_MsgsInv.
      - apply serializable_no_rules; reflexivity.
    Qed.

    Theorem impl0_ok:
      (steps step_t) # (steps step_t) |-- impl0 <=[ svmP ] spec.
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

