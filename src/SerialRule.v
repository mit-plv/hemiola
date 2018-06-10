Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts Reduction.

Require Import Omega Permutation Wf.

Set Implicit Arguments.

Section ImmRqRs.
  Variable (topo: CTree).

  Definition ImmRule (rule: Rule) :=
    exists rqoidx rqmidx rsmidx,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_postcond rule post porq ins nost norq outs ->
          idsOf outs = [rsmidx]) /\
      In (Build_Channel rqoidx rqmidx (rule_oidx rule)) (ctr_chns topo) /\
      In (Build_Channel (rule_oidx rule) rsmidx rqoidx) (ctr_chns topo).

  Definition UpRqFwdRule (rule: Rule) :=
    exists coidx rqmidx rqfmidx poidx,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_postcond rule post porq ins nost norq outs ->
          idsOf outs = [rqfmidx]) /\
      (getParent (ctr_tr topo) (rule_oidx rule))
        >>=[False] (fun ptr => trCurOIdxOf ptr = poidx) /\
      (getThis (ctr_tr topo) (rule_oidx rule))
        >>=[False] (fun tr => In coidx (map trCurOIdxOf (trChildrenOf tr))) /\
      In (Build_Channel coidx rqmidx (rule_oidx rule)) (ctr_chns topo) /\
      In (Build_Channel (rule_oidx rule) rqfmidx poidx) (ctr_chns topo).

  Definition DownRqFwdRule (rule: Rule) :=
    exists rqoidx rqmidx rqfminds coinds,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_postcond rule post porq ins nost norq outs ->
          idsOf outs = rqfminds) /\
      (getThis (ctr_tr topo) (rule_oidx rule))
        >>=[False] (fun tr => SubList coinds (map trCurOIdxOf (trChildrenOf tr))) /\
      In (Build_Channel rqoidx rqmidx (rule_oidx rule)) (ctr_chns topo) /\
      Forall (fun om => In (Build_Channel (rule_oidx rule) (fst om) (snd om))
                           (ctr_chns topo))
             (combine coinds rqfminds).

  Definition DownRsBackRule (rule: Rule) :=
    exists poidx rsmidx rsbmidx coidx,
      rule_minds rule = [rsmidx] /\
      (forall post pors ins nost nors outs,
          rule_postcond rule post pors ins nost nors outs ->
          idsOf outs = [rsbmidx]) /\
      (getParent (ctr_tr topo) (rule_oidx rule))
        >>=[False] (fun ptr => trCurOIdxOf ptr = poidx) /\
      In (Build_Channel poidx rsmidx (rule_oidx rule)) (ctr_chns topo) /\
      In (Build_Channel (rule_oidx rule) rsbmidx coidx) (ctr_chns topo).

  Definition UpRsBackRule (rule: Rule) :=
    exists coinds rsminds rsbmidx rsboidx,
      rule_minds rule = rsminds /\
      (forall post pors ins nost nors outs,
          rule_postcond rule post pors ins nost nors outs ->
          idsOf outs = [rsbmidx]) /\
      (getThis (ctr_tr topo) (rule_oidx rule))
        >>=[False] (fun tr => SubList coinds (map trCurOIdxOf (trChildrenOf tr))) /\
      Forall (fun om => In (Build_Channel (snd om) (fst om) (rule_oidx rule))
                           (ctr_chns topo))
             (combine coinds rsminds) /\
      In (Build_Channel (rule_oidx rule) rsbmidx rsboidx) (ctr_chns topo).

  Definition ImmRqRsRule (rule: Rule) :=
    ImmRule rule \/
    UpRqFwdRule rule \/ DownRqFwdRule rule \/
    DownRsBackRule rule \/ UpRsBackRule rule.

  Definition ImmRqRsSys (sys: System) :=
    Forall ImmRqRsRule (sys_rules sys).
  
End ImmRqRs.

Section PartialBlocking.
  Variable (topo: CTree).
  
  Fixpoint getDownRq (oidx: IdxT) (orq: ORq Msg) :=
    match orq with
    | nil => None
    | ri :: orq' =>
      if isFromParent topo oidx (rqh_from ri) then
        Some ri
      else getDownRq oidx orq'
    end.

  Fixpoint getUpRq (oidx: IdxT) (orq: ORq Msg) :=
    match orq with
    | nil => None
    | ri :: orq' =>
      if isFromChild topo oidx (rqh_from ri) then
        Some ri
      else getUpRq oidx orq'
    end.

  (* TODO: need a more intuitive (easier) definition. *)
  Definition PartialBlockingPrec (oidx: IdxT): RPrecond :=
    fun (ost: OState) (orq: ORq Msg) (ins: list (Id Msg)) =>
      match getDownRq oidx orq with
      | Some dri =>
        Forall (fun msg => msg_id msg = msg_id (rqh_msg dri) /\
                           msg_rr msg = Rs) (valsOf ins) /\
        rqh_fwds dri = idsOf ins
      | None =>
        match getUpRq oidx orq with
        | Some uri => 
          SubList (idsOf ins) (chnsFromParent topo oidx) /\
          Forall (fun msg => msg_id msg = msg_id (rqh_msg uri) /\
                             msg_rr msg = Rs) (valsOf ins)
        | None => True
        end
      end.

  Definition PartialBlockingRule (rule: Rule) :=
    (rule_precond rule) ->rprec (PartialBlockingPrec (rule_oidx rule)).

  Definition PartialBlockingSys (sys: System) :=
    Forall PartialBlockingRule (sys_rules sys).

End PartialBlocking.

Fixpoint mconcat {A} (ms: list (M.t A)): M.t A :=
  match ms with
  | nil => M.empty _
  | m :: ms' =>
    M.union m (mconcat ms')
  end.

Inductive IRRType := Imm | RqFwd | RsBack.

Section RAtomic.
  Variables (sys: System) (topo: CTree).

  Context {MsgT} `{HasMsg MsgT}.

  (* Here we define [RAtomic], which defines a set of atomic sequences only by
   * immediate, request-forwarding, and responses-back rules.
   *)
  Inductive RAtomic:
    list (Id MsgT) (* ins *) -> list IdxT (* affected objects *) ->
    History MsgT (* outs *) -> MessagePool MsgT -> Prop :=

  | RAtomicImm:
      forall rq rqr rs,
        msg_rr (getMsg (valOf rq)) = Rq ->
        msg_rr (getMsg (valOf rs)) = Rs ->
        RAtomic [rq] [rule_oidx rqr] [RlblInt rqr [rq] [rs]]
                (enqMPI rs (emptyMP _))
  | RAtomicRqFwd:
      forall rq rqr rqfs,
        msg_rr (getMsg (valOf rq)) = Rq ->
        Forall (fun rqf => msg_rr (getMsg (valOf rqf)) = Rq) rqfs ->
        RAtomic [rq] [rule_oidx rqr] [RlblInt rqr [rq] rqfs]
                (enqMsgs rqfs (emptyMP _))
  | RAtomicRsBack:
      forall rss rsr rsb,
        Forall (fun rs => msg_rr (getMsg (valOf rs)) = Rs) rss ->
        msg_rr (getMsg (valOf rsb)) = Rs ->
        RAtomic rss [rule_oidx rsr] [RlblInt rsr rss [rsb]]
                (enqMPI rsb (emptyMP _))

  | RAtomicRqFwdApp:
      forall rq rqr rqfwds rqfwdsp rqfoinds rqfhsts rqfouts,
        msg_rr (getMsg (valOf rq)) = Rq ->
        RAtomic [rq] [rule_oidx rqr] [RlblInt rqr [rq] rqfwds] (enqMsgs rqfwds (emptyMP _)) ->
        
        SubList rqfwdsp rqfwds ->
        NoDup rqfwdsp ->
        Forall (fun moho =>
                  msg_rr (getMsg (valOf (fst moho))) = Rq /\
                  RAtomic [fst moho] (fst (snd moho))
                          (fst (snd (snd moho)))
                          (snd (snd (snd moho))))
               (combine rqfwdsp (combine rqfoinds (combine rqfhsts rqfouts))) ->
        NoDup (rule_oidx rqr :: List.concat rqfoinds) ->
        RAtomic [rq] (rule_oidx rqr :: List.concat rqfoinds)
                (List.concat rqfhsts ++ [RlblInt rqr [rq] rqfwds])
                
                
                (mconcat rqfouts) (** FIXME: add uninitiated request forwardings *)

  | RAtomicRsBackApp:
      forall rq oinds hst rsr rss rsb,
        Forall (fun rs => msg_rr (getMsg (valOf rs)) = Rs) rss ->
        msg_rr (getMsg (valOf rsb)) = Rs ->
        RAtomic [rq] oinds hst (enqMsgs rss (emptyMP _)) ->
        RAtomic [rq] oinds (RlblInt rsr rss [rsb] :: hst) (enqMPI rsb (emptyMP _)).

End RAtomic.

(*! Proving [Serializability] using quasi-sequential histories *)

Section QuasiSeq.
  Variables (sys: System)
            (quasiSeq: forall (sys: System) (hst: MHistory) (n: nat), Prop).

  Definition QuasiSeqOkInit :=
    forall hst st,
      steps step_m sys (initsOf sys) hst st ->
      exists n, quasiSeq sys hst n.

  Definition QuasiSeqOkStep :=
    forall hst st n,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      ((exists trss, Sequential sys msg_dec hst trss) \/
       (exists rhst m, Reduced sys hst rhst /\
                       quasiSeq sys rhst m /\ m < n)).

  Lemma quasiSeq_implies_serializableSys:
    QuasiSeqOkStep ->
    forall n hst st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      Serializable sys hst.
  Proof.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros.
    specialize (H _ _ _ H0 H1); destruct H; dest.
    - eapply sequential_serializable; eauto.
    - eapply reduced_serializable; eauto.
      eapply IHn; eauto.
      eapply H; eauto.
  Qed.

  Lemma quasiSeqOk_implies_serializableSys:
    QuasiSeqOkInit -> QuasiSeqOkStep -> SerializableSys sys.
  Proof.
    intros; red; intros.
    specialize (H _ _ H1); destruct H as [n ?].
    eapply quasiSeq_implies_serializableSys; eauto.
  Qed.

End QuasiSeq.

Definition Continuous (hst1 hst2: MHistory) :=
  exists inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    inits2 <> nil /\
    SubList inits2 eouts1.

Definition trsTypeOf (hst: MHistory) :=
  match hst with
  | nil => TSlt
  | lbl :: _ =>
    match lbl with
    | RlblEmpty _ => TSlt
    | RlblIns _ => TIns
    | RlblOuts _ => TOuts
    | RlblInt _ _ _ => TInt
    end
  end.

Definition DiscontinuousTrsType (tty1 tty2: TrsType) :=
  match tty1, tty2 with
  | TSlt, _ => True
  | _, TSlt => True
  | TInt, _ => True
  | _, TInt => True
  | _, _ => False
  end.

Definition DiscontinuousA (hst1 hst2: MHistory) :=
  forall inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
    DisjList (idsOf ins1) (idsOf ins2) /\
    DisjList eouts1 inits2 /\
    DisjList (idsOf outs1) (idsOf outs2).

Definition DiscontinuousIns (hst1 hst2: MHistory) :=
  forall eins1 inits2 ins2 outs2 eouts2,
    hst1 = [RlblIns eins1] ->
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
    DisjList eins1 ins2 /\
    DisjList (idsOf eins1) (idsOf outs2).

Definition DiscontinuousOuts (hst1 hst2: MHistory) :=
  forall inits1 ins1 outs1 eouts1 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    hst2 = [RlblOuts eouts2] ->
    DisjList outs1 eouts2.

Definition Discontinuous (hst1 hst2: MHistory) :=
  DiscontinuousTrsType (trsTypeOf hst1) (trsTypeOf hst2) /\
  DiscontinuousA hst1 hst2 /\
  DiscontinuousIns hst1 hst2 /\
  DiscontinuousOuts hst1 hst2.

Definition Separated (hsts: list MHistory) :=
  forall hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 ->
    ~ Continuous hst1 hst2.

Definition NonconflictingRules (rule1 rule2: Rule) :=
  (rule_oidx rule1 <> rule_oidx rule2) \/
  (* TODO: define when rules are for the same object. *)
  False.

Definition NonconflictingLabels {MsgT} (lbl1 lbl2: RLabel MsgT) :=
  match lbl1, lbl2 with
  | RlblInt rule1 _ _, RlblInt rule2 _ _ => NonconflictingRules rule1 rule2
  | _, _ => True
  end.

Definition Nonconflicting {MsgT} (hst1 hst2: History MsgT) :=
  forall lbl1 lbl2,
    In lbl1 hst1 ->
    In lbl2 hst2 ->
    NonconflictingLabels lbl1 lbl2.

Definition Interleaved (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    Continuous hst1 hst2.

Definition MinInterleaved (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    Continuous hst1 hst2 /\
    Separated (hsts2 ++ [hst1]) /\
    Separated (hst2 :: hsts2).

Lemma atomic_reduced:
  forall sys hst1 inits1 ins1 outs1 eouts1
         hst2 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
    DiscontinuousA hst1 hst2 ->
    Nonconflicting hst1 hst2 ->
    Reduced sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  intros; red; intros.
  split.
  - eapply steps_split in H3; [|reflexivity].
    destruct H3 as [sti [? ?]].
    admit.
  - red; do 2 rewrite behaviorOf_app.
    do 2 erewrite atomic_behavior_nil by eassumption.
    reflexivity.
  
Admitted.

Lemma non_conflicting_discontinuous_reduced:
  forall sys hst1 hst2,
    STransactional msg_dec hst1 ->
    STransactional msg_dec hst2 ->
    Discontinuous hst1 hst2 ->
    Nonconflicting hst1 hst2 ->
    Reduced sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  intros.
  inv H0.
  - simpl; apply silent_reduced_1.
  - simpl.
    inv H; try (red in H1; dest; simpl in H; exfalso; auto; fail).
    + apply silent_commutes_2.
    + apply msg_ins_reduced_1.
      eauto using atomic_internal_history.
  - inv H; try (red in H1; dest; simpl in H; exfalso; auto; fail).
    + apply silent_commutes_2.
    + red in H1; dest; clear H H1 H3.
      specialize (H4 _ _ _ _ _ H0 eq_refl).
      eapply msg_outs_reduced_2; eauto.
  - inv H.
    + simpl; apply silent_reduced_2.
    + red in H1; dest; clear H H0 H4.
      specialize (H1 _ _ _ _ _ eq_refl H3); dest.
      eauto using msg_ins_reduced_2.
    + apply msg_outs_reduced_1.
      eauto using atomic_internal_history.
    + red in H1; dest; clear H H4 H5.
      eauto using atomic_reduced.
Qed.

Lemma interleaved_min:
  forall hsts, Interleaved hsts -> MinInterleaved hsts.
Proof.
Admitted.

Lemma separated_cons:
  forall (hsts1 hsts2: list MHistory) hst,
    Separated (hsts2 ++ hst :: hsts1) ->
    Forall (fun phst => ~ Continuous phst hst) hsts1 /\
    Forall (fun nhst => ~ Continuous hst nhst) hsts2 /\
    Separated (hsts2 ++ hsts1).
Proof.
Admitted.

Lemma continuous_atomic_concat:
  forall (hst1 hst2: MHistory),
    Continuous hst1 hst2 ->
    exists inits ins outs eouts,
      Atomic msg_dec inits ins (hst2 ++ hst1) outs eouts.
Proof.
  unfold Continuous; intros; dest.
  pose proof (atomic_app H H1 H0 H2); dest.
  eauto.
Qed.

Lemma stransactional_sequential_or_interleaved:
  forall sys trss st,
    steps step_m sys (initsOf sys) (List.concat trss) st ->
    Forall (STransactional msg_dec) trss ->
    Sequential sys msg_dec (List.concat trss) trss \/
    Interleaved trss.
Proof.
  induction trss as [|trs trss]; simpl; intros;
    [left; constructor; auto|].

  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  inv H0.
  specialize (IHtrss _ H H5); destruct IHtrss.

  - (* TODO: need to prove that whenever a semi-transaction
     * [STransactional ins trs outs] is added to a history ([List.concat trss]),
     * [ins] is either a new semi-transaction or a continuation from one of 
     * previous semi-transactions.
     *
     * This is not true when [ins] takes a part from [trs1] and the other part
     * from [trs2], where [trs1 <> trs2] and [trs1 ∈ trss /\ trs2 ∈ trss].
     * Thus we need a static condition to ensure each rule in the system takes
     * incoming messages for a single transaction.
     *)
    admit.
  - right.
    clear -H0.
    destruct H0 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 [? ?]]]]]]; subst.
    exists hst1, hst2, hsts1, hsts2, (trs :: hsts3).
    split; auto.
Admitted.

Section WellInterleaved.
  Variable (sys: System).

  Definition WellInterleaved :=
    forall hst1 hst2,
      Continuous hst1 hst2 ->
      forall hsts,
        Forall (STransactional msg_dec) hsts ->
        Separated (hsts ++ [hst1]) ->
        Separated (hst2 :: hsts) ->
        exists rhst1 rhst2,
          Reduced sys (List.concat (hst2 :: hsts ++ [hst1]))
                  (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) /\
          Forall (STransactional msg_dec) (rhst2 ++ rhst1) /\
          List.length hsts = List.length (rhst2 ++ rhst1).

  Lemma well_interleaved_reduced:
    forall (Hwi: WellInterleaved) trss st1 st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (STransactional msg_dec) trss ->
      Interleaved trss ->
      exists (rhst : MHistory) (m : nat),
        Reduced sys (List.concat trss) rhst /\
        SSequential msg_dec rhst m /\
        m < Datatypes.length trss.
  Proof.
    intros.
    apply interleaved_min in H1.
    destruct H1 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 [? [? [? ?]]]]]]]]; subst.
    match goal with
    | [H: steps step_m _ _ ?hst _ |- _] =>
      replace hst with ((List.concat hsts3)
                          ++ (List.concat (hst2 :: hsts2 ++ [hst1]))
                          ++ (List.concat hsts1)) in *;
        [|simpl; repeat rewrite <-app_assoc;
          repeat rewrite concat_app; simpl;
          rewrite <-app_assoc, app_nil_r;
          repeat rewrite concat_app; simpl;
          reflexivity]
    end.
    eapply steps_split in H; [|reflexivity]; destruct H as [sti2 [? ?]].
    eapply steps_split in H; [|reflexivity]; destruct H as [sti1 [? ?]].
    apply Forall_app_inv in H0; dest.
    inv H6; apply Forall_app_inv in H10; dest; inv H7.
    pose proof (Hwi _ _ H2 _ H6 H3 H4).
    destruct H7 as [rhst1 [rhst2 [? [? ?]]]].

    exists ((List.concat hsts3)
              ++ (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
              ++ (List.concat hsts1)); eexists.
    split; [|split].
    - apply reduced_app_1.
      apply reduced_app_2.
      replace (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
        with (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)); [assumption|].
      repeat (rewrite concat_app; simpl).
      rewrite <-app_assoc; reflexivity.
    - econstructor.
      + repeat rewrite <-concat_app; reflexivity.
      + reflexivity.
      + apply Forall_app_inv in H8; dest.
        repeat (apply Forall_app; auto).
        constructor; auto.
        eapply continuous_atomic_concat in H2; eauto.
        destruct H2 as [inits [ins [outs [eouts ?]]]].
        eapply STrsAtomic; eauto.
    - repeat (simpl; try rewrite app_length).
      unfold MHistory; rewrite H10.
      apply plus_lt_compat_l.
      rewrite app_length.
      rewrite <-Nat.add_assoc; simpl.
      repeat rewrite Nat.add_succ_r.
      rewrite Nat.add_assoc.
      auto.
  Qed.

  Definition WellInterleavedInd :=
    forall hst1 hst2,
      Continuous hst1 hst2 ->
      forall hst,
        STransactional msg_dec hst ->
        forall hsts,
          Forall (STransactional msg_dec) hsts ->
          Forall (fun phst => ~ Continuous phst hst) (hsts ++ [hst1]) ->
          ~ Continuous hst hst2 ->
          Reduced sys (hst2 ++ hst ++ List.concat hsts ++ hst1)
                  (hst2 ++ List.concat hsts ++ hst1 ++ hst) \/
          Reduced sys (hst2 ++ hst ++ List.concat hsts ++ hst1)
                  (hst ++ hst2 ++ List.concat hsts ++ hst1).

  Lemma well_interleaved_ind_ok:
    forall (Hwii: WellInterleavedInd), WellInterleaved.
  Proof.
    red; induction hsts as [|hst hsts]; simpl; intros;
      [exists nil, nil; simpl; split; auto; apply reduced_refl|].

    inv H0.

    apply separated_cons with (hsts2:= nil) in H1; dest; simpl in *; clear H1.
    apply separated_cons with (hsts2:= [hst2]) in H2; dest.
    inv H2; clear H10.
    
    specialize (IHhsts H6 H3 H4).
    destruct IHhsts as [rhst1 [rhst2 ?]]; dest.

    eapply Hwii in H6; eauto.
    specialize (H6 H0 H9).
    destruct H6.
    - exists (rhst1 ++ [hst]), rhst2.
      split; [|split].
      + repeat (simpl; try rewrite concat_app; try rewrite app_nil_r).
        repeat (simpl in H2; try rewrite concat_app in H2; try rewrite app_nil_r in H2).
        eapply reduced_trans; [eassumption|].
        repeat rewrite app_assoc.
        apply reduced_app_2.
        repeat rewrite <-app_assoc.
        assumption.
      + apply Forall_app_inv in H7; dest.
        repeat apply Forall_app; eauto.
      + repeat rewrite app_length.
        rewrite app_length in H8.
        rewrite Nat.add_assoc, <-H8.
        simpl; omega.
    - exists rhst1, (hst :: rhst2).
      split; [|split].
      + repeat (simpl; try rewrite concat_app; try rewrite app_nil_r).
        repeat (simpl in H2; try rewrite concat_app in H2; try rewrite app_nil_r in H2).
        eapply reduced_trans; [eassumption|].
        apply reduced_app_1.
        assumption.
      + apply Forall_app_inv in H7; dest.
        repeat apply Forall_app; eauto.
      + simpl; rewrite app_length.
        rewrite app_length in H8.
        rewrite <-H8.
        auto.
  Qed.

End WellInterleaved.

Section ImmRqRsSerial.
  Variable (topo: CTree) (sys: System).
  Hypotheses (Hirr: ImmRqRsSys topo sys)
             (Hpb: PartialBlockingSys topo sys).

  (* Lemma immrqrs_atomic_ratomic: *)
  (*   forall st1 hst st2, *)
  (*     steps step_m sys st1 hst st2 -> *)
  (*     forall ins outs, *)
  (*       Atomic ins hst outs -> *)
  (*       exists oinds, *)
  (*         RAtomic ins oinds hst outs. *)
  (* Proof. *)

  (* Lemma immrqrs_not_continuous_discontinuous: *)
  (*   forall hst1 hst2 st1 st2 hst, *)
  (*     steps step_m sys st1 (hst2 ++ hst ++ hst1) st2 -> *)
  (*     Continuous hst1 hst2 -> *)
  (*     DiscontinuousA hst1 hst2. *)
  (* Proof. *)

  Lemma immrqrs_well_interleaved_ind:
    WellInterleavedInd sys.
  Proof.
  Admitted.
  
  Lemma immrqrs_well_interleaved:
    WellInterleaved sys.
  Proof.
    intros.
    apply well_interleaved_ind_ok.
    apply immrqrs_well_interleaved_ind.
  Qed.
  
  Local Definition quasiSeq :=
    fun (_: System) (hst: MHistory) n => SSequential msg_dec hst n.

  Lemma immrqrs_pb_quasiSeq_ok:
    QuasiSeqOkStep sys quasiSeq.
  Proof.
    red; intros.
    inv H0.
    pose proof (stransactional_sequential_or_interleaved H H3).
    destruct H0; eauto.
    right; eapply well_interleaved_reduced; eauto.
    apply immrqrs_well_interleaved.
  Qed.

  Theorem immrqrs_pb_serializable:
    SerializableSys sys.
  Proof.
    intros.
    apply quasiSeqOk_implies_serializableSys with (quasiSeq := quasiSeq).
    - red; intros.
      apply ssequential_default.
    - apply immrqrs_pb_quasiSeq_ok.
  Qed.

End ImmRqRsSerial.

