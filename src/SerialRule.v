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

Section RAtomic.
  Variables (sys: System) (topo: CTree).

  Context {MsgT} `{HasMsg MsgT}.

  (* Here we define [RAtomic], which also defines a set of atomic sequences.
   * They are more restrictive than ordinary [Atomic] sequences in that they are
   * generated by a certain set of rules -- immediate, request-forwarding, and
   * responses-back.
   *)
  Inductive RAtomic:
    list (Id MsgT) (* requestors *) -> list IdxT (* affected objects *) ->
    History MsgT -> MessagePool MsgT -> Prop :=
  (* | RAtomicStart: *)
  (*     forall ins rule outs, *)
  (*       RAtomic ins [rule_oidx rule] [RlblInt rule ins outs] *)
  (*               (enqMsgs outs (emptyMP _)) *)
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
  | RAtomicRqFwdA:
      forall rq rqr rqfwds rqfwdsp rqfoinds rqfhsts rqfouts,
        msg_rr (getMsg (valOf rq)) = Rq ->
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
                (mconcat rqfouts) (* FIXME: add uninitiated request forwardings *)
  | RAtomicRsBackA:
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
      ((exists trss, Sequential sys hst trss) \/
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

Definition Continuous {MsgT} (hst1 hst2: History MsgT) :=
  exists ins1 outs1 ins2 outs2,
    Atomic ins1 hst1 outs1 /\
    Atomic ins2 hst2 outs2 /\
    ins2 <> nil /\
    Forall (InMPI outs1) ins2.

Definition Discontinuous {MsgT} (hst1 hst2: History MsgT) :=
  forall ins1 outs1 ins2 outs2,
    STransactional ins1 hst1 outs1 ->
    STransactional ins2 hst2 outs2 ->
    DisjList ins1 ins2 /\ Forall (fun idm => ~ InMPI outs1 idm) ins2.

Definition NonconflictingRules (rule1 rule2: Rule) :=
  (rule_oidx rule1 <> rule_oidx rule2) \/
  (* TODO: define when rules are for the same object. *)
  True.

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

Definition Interleaved {MsgT} (hsts: list (History MsgT)) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    Continuous hst1 hst2.

Lemma continuous_atomic_concat:
  forall {MsgT} (hst1 hst2: History MsgT),
    Continuous hst1 hst2 ->
    exists mins mouts,
      Atomic mins (hst2 ++ hst1) mouts.
Proof.
  unfold Continuous; intros.
  destruct H as [ins1 [outs1 [ins2 [outs2 [? [? [? ?]]]]]]].
  eapply atomic_app in H2; eauto.
  dest; eauto.
Qed.

Lemma stransactional_sequential_or_interleaved:
  forall sys trss st,
    steps step_m sys (initsOf sys) (List.concat trss) st ->
    Forall (fun trs => exists ins outs, STransactional ins trs outs) trss ->
    Sequential sys (List.concat trss) trss \/
    Interleaved trss.
Proof.
  induction trss as [|trs trss]; simpl; intros;
    [left; constructor; auto|].

  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  inv H0; destruct H4 as [ins [outs ?]].
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
    clear -H2.
    destruct H2 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 [? ?]]]]]]; subst.
    exists hst1, hst2, hsts1, hsts2, (trs :: hsts3).
    split; auto.
  
Admitted.

(** FIXME: [Discontinuous] definition is too broad to prove this lemma:
 * the predicate should not allow the case where both [hst1] and [hst2]
 * have some observable labels ([RlblIns] or [RlblOuts]) so commuting
 * two histories induces different behaviors.
 *
 * [Discontinuous] is used for 
 * [between_continuous_discontinuous_nonconflicting], where the one of arguments
 * is [Atomic], which means that it's totally fine to restrict the definition
 * of it by disallowing commutations of observable labels.
 *)
Lemma non_conflicting_discontinuous_commute:
  forall sys hst1 ins1 outs1 hst2 ins2 outs2,
    STransactional ins1 hst1 outs1 ->
    STransactional ins2 hst2 outs2 ->
    Discontinuous hst1 hst2 ->
    Nonconflicting hst1 hst2 ->
    Reduced sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  induction hst2; simpl; intros;
    [rewrite app_nil_r; apply reduced_refl|].

  inv H0.
  - simpl; apply silent_reduced.
  - simpl. admit.
  - simpl. admit.
  - admit.

Admitted.

Section ImmRqRsSerial.
  Variable (topo: CTree) (sys: System).
  Hypotheses (Hirr: ImmRqRsSys topo sys)
             (Hpb: PartialBlockingSys topo sys).

  Lemma between_continuous_discontinuous_nonconflicting:
    forall hst1 hst2,
      Continuous hst1 hst2 ->
      forall hsts,
        Forall (fun hst => exists ins outs, STransactional ins hst outs) hsts ->
        forall st1 st2,
          steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
          Forall (fun hst => Discontinuous hst1 hst /\ Nonconflicting hst1 hst) hsts \/
          Forall (fun hst => Discontinuous hst hst2 /\ Nonconflicting hst hst2) hsts.
  Proof.
  Admitted.

  Lemma between_continuous_reduced:
    forall hst1 hst2,
      Continuous hst1 hst2 ->
      forall hsts,
        Forall (fun hst => exists ins outs, STransactional ins hst outs) hsts ->
        forall st1 st2,
          steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
          Reduced sys (List.concat (hst2 :: hsts ++ [hst1]))
                  (List.concat (hst2 :: hst1 :: hsts)) \/
          Reduced sys (List.concat (hst2 :: hsts ++ [hst1]))
                  (List.concat (hsts ++ [hst2; hst1])).
  Proof.
    intros.
    pose proof H.
    destruct H as [ins1 [outs1 [ins2 [outs2 [? [? [? ?]]]]]]].
    eapply between_continuous_discontinuous_nonconflicting in H2; eauto.
    destruct H2; [left|right].
    - simpl; apply reduced_app_1.
      rewrite concat_app; simpl; rewrite app_nil_r.

      clear -H H0 H2.
      generalize dependent hst1.
      induction hsts; simpl; intros;
        [rewrite app_nil_r; apply reduced_refl|].
      inv H0; inv H2; dest.
      specialize (IHhsts H5 _ H H6).
      rewrite <-app_assoc.
      eapply reduced_trans; [eapply reduced_app_1; eassumption|].
      do 2 rewrite app_assoc.
      apply reduced_app_2.
      eapply non_conflicting_discontinuous_commute; eauto.
      eapply STrsAtomic; eauto.

    - change (hst2 :: hsts ++ [hst1]) with ((hst2 :: hsts) ++ [hst1]).
      do 2 rewrite concat_app.
      simpl; rewrite app_nil_r.
      rewrite app_assoc.
      apply reduced_app_2.

      clear -H0 H2 H3.
      generalize dependent hst2.
      induction hsts; simpl; intros;
        [rewrite app_nil_r; apply reduced_refl|].
      inv H0; inv H2; dest.
      specialize (IHhsts H5 _ H3 H6).
      rewrite <-app_assoc.
      eapply reduced_trans; [|eapply reduced_app_1; eassumption].
      do 2 rewrite app_assoc.
      apply reduced_app_2.
      eapply non_conflicting_discontinuous_commute; eauto.
      eapply STrsAtomic; eauto.
  Qed.

  Local Definition quasiSeq :=
    fun (_: System) (hst: MHistory) n => SSequential hst n.

  Lemma immrqrs_pb_interleaved_reducible:
    forall trss st1 st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (fun trs => exists ins outs, STransactional ins trs outs) trss ->
      Interleaved trss ->
      exists (rhst : MHistory) (m : nat),
        Reduced sys (List.concat trss) rhst /\
        SSequential rhst m /\
        m < Datatypes.length trss.
  Proof.
    intros.
    destruct H1 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 [? ?]]]]]]; subst.
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
    inv H4; apply Forall_app_inv in H8; dest; inv H5.
    eapply between_continuous_reduced in H3; eauto.
    destruct H9 as [ins1 [outs1 ?]].
    destruct H3.

    - exists ((List.concat hsts3)
                ++ (List.concat ((hst2 ++ hst1) :: hsts2))
                ++ (List.concat hsts1)); eexists.
      split; [|split].
      + apply reduced_app_1.
        apply reduced_app_2.
        replace (List.concat ((hst2 ++ hst1) :: hsts2))
          with (List.concat (hst2 :: hst1 :: hsts2)); auto.
        simpl; apply app_assoc.
      + econstructor.
        * repeat rewrite <-concat_app; reflexivity.
        * reflexivity.
        * do 2 (apply Forall_app; auto).
          constructor; auto.
          apply continuous_atomic_concat in H2.
          destruct H2 as [mins [mouts ?]].
          do 2 eexists.
          eapply STrsAtomic; eauto.
      + repeat (simpl; try rewrite app_length).
        apply plus_lt_compat_l.
        do 2 rewrite Nat.add_comm with (n:= List.length hsts2).
        auto.

    - exists ((List.concat hsts3)
                ++ (List.concat (hsts2 ++ [hst2 ++ hst1]))
                ++ (List.concat hsts1)); eexists.
      split; [|split].
      + apply reduced_app_1.
        apply reduced_app_2.
        replace (List.concat (hsts2 ++ [hst2 ++ hst1]))
          with (List.concat (hsts2 ++ [hst2; hst1])); auto.
        do 2 rewrite concat_app.
        simpl; do 2 rewrite app_nil_r; reflexivity.
      + econstructor.
        * repeat rewrite <-concat_app; reflexivity.
        * reflexivity.
        * do 3 (apply Forall_app; auto).
          constructor; auto.
          apply continuous_atomic_concat in H2.
          destruct H2 as [mins [mouts ?]].
          do 2 eexists.
          eapply STrsAtomic; eauto.
      + repeat (simpl; try rewrite app_length).
        apply plus_lt_compat_l.
        apply le_lt_n_Sm.
        rewrite <-Nat.add_assoc; simpl.
        apply Nat.le_refl.
  Qed.
  
  Lemma immrqrs_pb_quasiSeq_ok:
    QuasiSeqOkStep sys quasiSeq.
  Proof.
    red; intros.
    inv H0.
    pose proof (stransactional_sequential_or_interleaved H H3).
    destruct H0; eauto.
    right; eapply immrqrs_pb_interleaved_reducible; eauto.
  Qed.

  Theorem immrqrs_pb_serializable:
    SerializableSys sys.
  Proof.
    intros.
    apply quasiSeqOk_implies_serializableSys with (quasiSeq := quasiSeq).
    - red; intros.
      apply SSequential_default.
    - apply immrqrs_pb_quasiSeq_ok.
  Qed.

End ImmRqRsSerial.

