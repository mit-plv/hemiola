Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.
Require Import Serial SerialFacts Reduction.

Require Import Omega Wf.

Set Implicit Arguments.

Open Scope list.

(*! Quasi-sequential histories *)

Section QuasiSeq.
  Context `{oifc: OStateIfc}.
  Variables (sys: System)
            (quasiSeq: forall (sys: System) (hst: MHistory) (n: nat), Prop).

  Definition QuasiSeqOkInit :=
    forall hst st,
      steps step_m sys (initsOf sys) hst st ->
      exists n, quasiSeq sys hst n.

  Definition QuasiSeqOkStep :=
    forall hst n st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      ((exists rhst rtrss,
           steps step_m sys (initsOf sys) rhst st /\
           Sequential sys msg_dec rhst rtrss) \/
       (exists rhst m,
           steps step_m sys (initsOf sys) rhst st /\
           quasiSeq sys rhst m /\ m < n)).

  Lemma quasiSeq_implies_serializableSys:
    QuasiSeqOkStep ->
    forall n hst st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      Serializable sys hst st.
  Proof.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros.
    specialize (H _ _ _ H0 H1); destruct H.
    - destruct H as [rhst [rtrss [? ?]]].
      exists rhst; split; eauto.
    - destruct H as [rhst [m ?]]; dest.
      specialize (IHn _ H3 _ _ H H2).
      eapply reducible_serializable with (hto:= rhst); eauto.
  Qed.

  Lemma quasiSeqOk_implies_serializableSys:
    QuasiSeqOkInit -> QuasiSeqOkStep -> SerializableSys sys.
  Proof.
    intros; red; intros.
    specialize (H _ _ H1); destruct H as [n ?].
    eapply quasiSeq_implies_serializableSys; eauto.
  Qed.

End QuasiSeq.

Definition ExtContinuous `{oifc: OStateIfc} (sys: System)
           (hst1 hst2: MHistory) :=
  exists inits1 eouts1 inits2 ins2 outs2 eouts2,
    ExtAtomic sys msg_dec inits1 hst1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    ~ SubList (idsOf inits2) (sys_merqs sys) /\
    SubList inits2 eouts1.

Definition ExtContinuousL `{oifc: OStateIfc} (sys: System)
           (hst: MHistory) (l: MLabel) :=
  exists inits eouts oidx ridx rins routs,
    ExtAtomic sys msg_dec inits hst eouts /\
    l = RlblInt oidx ridx rins routs /\
    ~ SubList (idsOf rins) (sys_merqs sys) /\
    SubList rins eouts.

Definition Discontinuous (hst1 hst2: MHistory) :=
  exists inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    DisjList eouts1 inits2.

Definition ExtInterleaved `{oifc: OStateIfc} (sys: System)
           (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    ExtContinuous sys hst1 hst2 /\
    Forall (fun hst => Discontinuous hst1 hst) hsts2.

Definition ExtInterleavedL `{oifc: OStateIfc} (sys: System)
           (hsts: list MHistory) :=
  exists hst1 l2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ [l2] :: hsts2 ++ hst1 :: hsts1 /\
    ExtContinuousL sys hst1 l2 /\
    Forall (fun hst => Discontinuous hst1 hst) hsts2.

Lemma extContinuous_concat:
  forall `{oifc: OStateIfc} (sys: System) hst l,
    ExtContinuousL sys hst l ->
    exists inits neouts,
      ExtAtomic sys msg_dec inits (l :: hst) neouts.
Proof.
  unfold ExtContinuousL; intros; dest; subst.
  inv H.
  do 2 eexists.
  econstructor; [eassumption|].
  econstructor; eauto.
  destruct x3; try discriminate.
  elim H1; apply SubList_nil.
Qed.

Lemma extContinuous_hst_stransactional_length:
  forall `{oifc: OStateIfc} (sys: System) hst l tn,
    ExtContinuousL sys hst l ->
    STransactional sys msg_dec hst tn ->
    tn = 0.
Proof.
  unfold ExtContinuousL; intros.
  destruct H as [eouts [oidx [ridx [rins [routs ?]]]]]; dest; subst.
  inv H.
  inv H0; auto; try (inv H4; fail).
  exfalso; inv H.
  pose proof (atomic_unique H4 H5); dest; subst; auto.
Qed.

Lemma extContinuous_label_stransactional_one:
  forall `{oifc: OStateIfc} (sys: System) hst l tn,
    ExtContinuousL sys hst l ->
    STransactional sys msg_dec [l] tn ->
    tn = 1.
Proof.
  unfold ExtContinuousL; intros.
  destruct H as [eouts [oidx [ridx [rins [routs ?]]]]]; dest; subst.
  inv H0; auto; try discriminate.
  exfalso; inv H1.
  inv H4; auto.
  inv H9.
Qed.

Lemma discontinuous_tail_right:
  forall hst1 hst2 lbl2,
    hst2 <> nil ->
    Discontinuous hst1 (lbl2 :: hst2) ->
    Discontinuous hst1 hst2.
Proof.
  unfold Discontinuous; intros.
  destruct H0 as [inits1 [ins1 [outs1 [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]]]].
  dest.
  inv H1; [elim H; reflexivity|].
  do 8 eexists; repeat split; eauto.
Qed.

Lemma extAtomic_Discontinuous:
  forall `{oifc: OStateIfc} (sys: System) st1 trss st2,
    steps step_m sys st1 (List.concat trss) st2 ->
    Forall (AtomicEx msg_dec) trss ->
    Forall (Transactional sys msg_dec) trss ->
    forall trs1 trs2,
      In trs1 trss -> In trs2 trss ->
      Discontinuous trs1 trs2.
Proof.
  intros.
  rewrite Forall_forall in H0, H1.
  pose proof (H0 _ H2).
  pose proof (H1 _ H2).
  pose proof (H0 _ H3).
  pose proof (H1 _ H3).
  eapply atomic_Transactional_ExtAtomic in H5; [|eassumption].
  destruct H5 as [einits1 [eouts1 ?]]; inv H5.
  eapply atomic_Transactional_ExtAtomic in H7; [|eassumption].
  destruct H7 as [einits2 [eouts2 ?]]; inv H5.

  assert (exists st11 st12, steps step_m sys st11 trs1 st12).
  { apply in_split in H2.
    destruct H2 as [ptrss [ntrss ?]]; subst.
    rewrite concat_app in H; simpl in H.
    eapply steps_split in H; [|reflexivity].
    destruct H as [sti1 [? ?]].
    eapply steps_split in H; [|reflexivity].
    destruct H as [sti2 [? ?]].
    eauto.
  }
  destruct H5 as [st11 [st12 ?]].
  eapply atomic_eouts_not_erqs in H5; [|eassumption].

  do 8 eexists.
  repeat ssplit; try eassumption.
  red; intros idm.
  destruct (in_dec (id_dec msg_dec) idm eouts1); [|auto].
  rewrite Forall_forall in H5.
  specialize (H5 _ i).
  right; intro Hx.
  apply in_map with (f:= idOf) in Hx.
  apply H7 in Hx; auto.
Qed.

Lemma atomic_beginning_label:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    exists hhst oidx ridx routs,
      hst = hhst ++ [RlblInt oidx ridx inits routs].
Proof.
  induction 1; simpl; intros; subst.
  - exists nil; do 3 eexists; simpl; reflexivity.
  - destruct IHAtomic as [hhst [ioidx [iridx [irouts ?]]]]; subst.
    exists (RlblInt oidx ridx rins routs :: hhst).
    exists ioidx, iridx, irouts.
    reflexivity.
Qed.

Lemma extInterleaved_atomic_extInterleavedL:
  forall `{oifc: OStateIfc} (sys: System) atms n,
    Forall (AtomicEx msg_dec) atms ->
    SSequential sys msg_dec atms n ->
    ExtInterleaved sys atms ->
    exists datms,
      List.concat atms = List.concat datms /\
      Forall (AtomicEx msg_dec) datms /\
      ExtInterleavedL sys datms /\
      exists m,
        SSequential sys msg_dec datms m /\
        m <= n.
Proof.
  unfold ExtInterleaved, ExtInterleavedL; intros.
  destruct H1 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 ?]]]]]; dest; subst.
  red in H2.
  destruct H2 as [inits1 [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]]; dest.
  pose proof (atomic_beginning_label H2).
  destruct H6 as [hhst [oidx [ridx [routs ?]]]]; subst.
  
  exists (hsts3 ++ (lift_each hhst)
                ++ [RlblInt oidx ridx inits2 routs]
                :: hsts2 ++ hst1 :: hsts1).
  repeat split.
  - repeat (rewrite concat_app; simpl).
    repeat rewrite <-app_assoc.
    rewrite <-lift_each_concat.
    reflexivity.
  - apply Forall_app_inv in H; dest.
    inv H6; apply Forall_app_inv in H10; dest.
    inv H7.
    apply atomicEx_split_each in H9.
    rewrite lift_each_app in H9.
    apply Forall_app_inv in H9; dest.
    inv H8; clear H14.
    apply Forall_app; [assumption|].
    apply Forall_app; [assumption|].
    constructor; [assumption|].
    apply Forall_app; [assumption|].
    constructor; assumption.
  - exists hst1, (RlblInt oidx ridx inits2 routs).
    eexists hsts1, hsts2, (hsts3 ++ lift_each hhst).
    repeat split; auto.
    + repeat (rewrite <-app_assoc; simpl).
      reflexivity.
    + red; exists inits1, eouts1, oidx, ridx, inits2, routs.
      repeat split; auto.
  - apply ssequential_app_inv in H0.
    destruct H0 as [n1 [n2 ?]]; dest; subst.
    inv H6; inv H9.
    apply ssequential_app_inv in H7.
    destruct H7 as [n2 [n3 ?]]; dest; subst.
    inv H7; inv H11.

    eapply internal_stransactional_split_each in H2; eauto.
    destruct H2 as [sn [? ?]].
    rewrite lift_each_app in H2; simpl in H2.
    apply ssequential_app_inv in H2.
    destruct H2 as [sn1 [sn2 ?]]; dest; subst.
    inv H11; inv H14.
    inv H12; [|discriminate].

    eexists; split.
    + apply ssequential_app; [eassumption|].
      apply ssequential_app; [eassumption|].
      econstructor; try reflexivity; [|eassumption].
      apply ssequential_app; [eassumption|].
      econstructor; try reflexivity; eassumption.
    + omega.
Qed.

(** [NonMergeable] says that any transactions in a given system [sys] are
 * executed without any merging, i.e., each [Atomic] history is either the start
 * of a new transaction or a continuation of a previous transaction.
 *)
Definition NonMergeable `{oifc: OStateIfc} (sys: System) :=
  forall st1,
    Reachable (steps step_m) sys st1 ->
    IntMsgsEmpty sys (bst_msgs st1) ->
    forall trss trs st2,
      steps step_m sys st1 (trs ++ List.concat trss) st2 ->
      Forall (AtomicEx msg_dec) trss ->
      Forall (Transactional sys msg_dec) trss ->
      forall eouts,
        IntAtomic sys msg_dec trs eouts ->
        ExtInterleaved sys (trs :: trss).

Section WellInterleaved.
  Context {oifc: OStateIfc}.
  Variable (sys: System).
  Hypothesis (Hnmg: NonMergeable sys).

  Definition WellInterleavedHst (hst1: MHistory) (l2: MLabel) :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2 hsts,
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (Discontinuous hst1) hsts ->
        Forall (AtomicEx msg_dec) hsts ->
        exists rhst1 rhst2,
          steps step_m sys st1
                (List.concat rhst2 ++ l2 :: hst1 ++ List.concat rhst1) st2 /\
          Distribution hsts rhst1 rhst2.
  
  Definition WellInterleaved :=
    forall hst1 l2,
      ExtContinuousL sys hst1 l2 ->
      WellInterleavedHst hst1 l2.

  Lemma well_interleaved_reducible:
    forall (Hwi: WellInterleaved) trss n st1 st2
           (Hr: Reachable (steps step_m) sys st1),
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (AtomicEx msg_dec) trss ->
      SSequential sys msg_dec trss n ->
      ExtInterleavedL sys trss ->
      exists (rtrss: list MHistory) (m: nat),
        steps step_m sys st1 (List.concat rtrss) st2 /\
        SSequential sys msg_dec rtrss m /\ m < n.
  Proof.
    intros.
    destruct H2 as [hst1 [l2 [hsts1 [hsts2 [hsts3 ?]]]]]; dest; subst.
    match goal with
    | [H: steps step_m _ _ ?hst _ |- _] =>
      replace hst with ((List.concat hsts3)
                          ++ (List.concat ([l2] :: hsts2 ++ [hst1]))
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
    simpl in H5; rewrite concat_app in H5.
    simpl in H5; rewrite app_nil_r in H5.
    pose proof (Hwi _ _ H3 _ (reachable_steps Hr H) _ _ H5 H4 H6).
    destruct H7 as [rhst1 [rhst2 ?]]; dest.

    apply ssequential_app_inv in H1.
    destruct H1 as [n3 [n2 ?]]; dest; subst.
    inv H10; inv H15.
    pose proof (extContinuous_label_stransactional_one H3 H14); subst; simpl.
    apply ssequential_app_inv in H13.
    destruct H13 as [n2 [n1 ?]]; dest; subst.
    inv H13; inv H17.
    pose proof (ssequential_distr_inv H8 H10).
    destruct H13 as [rn1 [rn2 ?]]; dest; subst.
    pose proof (extContinuous_hst_stransactional_length H3 H16); subst.
    
    eapply extContinuous_concat in H3.
    destruct H3 as [inits [neouts ?]].
    
    exists (hsts3 ++ (rhst2 ++ (l2 :: trs) :: rhst1) ++ trss); eexists.
    split; [|split].
    - repeat rewrite concat_app.
      eapply steps_append; eauto.
      eapply steps_append; eauto.
    - apply ssequential_app; [eassumption|].
      apply ssequential_app; [|eassumption].
      apply ssequential_app; [eassumption|].
      econstructor; try reflexivity; [eassumption|].
      eapply STrsExtAtomic; eassumption.
    - simpl; omega.
  Qed.

  Lemma atomic_transactions_sequential_or_extInterleaved:
    forall trss st1 st2,
      Reachable (steps step_m) sys st1 ->
      IntMsgsEmpty sys st1.(bst_msgs) ->
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (AtomicEx msg_dec) trss ->
      Sequential sys msg_dec (List.concat trss) trss \/
      ExtInterleaved sys trss.
  Proof.
    induction trss as [|trs trss]; simpl; intros;
      [left; constructor; auto|].

    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti [? ?]].
    inv H2.
    specialize (IHtrss _ _ H H0 H1 H7); destruct IHtrss.

    - inv H2; clear H5.
      destruct H6 as [inits [ins [outs [eouts ?]]]].
      destruct (subList_dec idx_dec (idsOf inits) (sys_merqs sys)) as [Hex|Hnex].
      + left; constructor; [|reflexivity].
        constructor; auto.
        eapply TrsAtomic; econstructor; eauto.
      + right.
        eapply Hnmg; eauto.
        * eapply steps_append; eassumption.
        * econstructor; eassumption.

    - right.
      clear -H2.
      destruct H2 as [hst1 [l2 [hsts1 [hsts2 [hsts3 [? [? ?]]]]]]]; subst.
      exists hst1, l2, hsts1, hsts2, (trs :: hsts3).
      split; auto.
  Qed.

  Lemma well_interleaved_serializable:
    WellInterleaved -> SerializableSys sys.
  Proof.
    intros.
    apply quasiSeqOk_implies_serializableSys
      with (quasiSeq := fun sys hst n =>
                          exists trss,
                            SSequential sys msg_dec trss n /\
                            hst = List.concat trss).
    - red; intros.
      apply ssequential_default.
    - red; intros.
      destruct H1 as [trss [? ?]]; subst.

      apply trss_reducible_to_ins_atomics_outs with (sys0:= sys) in H1.
      destruct H1 as [ins [atms [outs ?]]]; dest.

      pose proof (H4 _ (reachable_init step_m sys) _ H0).
      eapply steps_split in H6; [|reflexivity]; destruct H6 as [sti2 [? ?]].
      eapply steps_split in H6; [|reflexivity]; destruct H6 as [sti1 [? ?]].

      assert (IntMsgsEmpty sys sti1.(bst_msgs)).
      { eapply insHistory_IntMsgsEmpty; eauto.
        apply init_IntMsgsEmpty.
      }
      assert (Reachable (steps step_m) sys sti1) by (eexists; eassumption).
      pose proof (atomic_transactions_sequential_or_extInterleaved H10 H9 H8 H2).
      destruct H11.
      + left.
        exists (outs ++ List.concat atms ++ ins).
        eexists (lift_each outs ++ atms ++ lift_each ins).
        split.
        * apply H4; auto.
          apply reachable_init.
        * apply sequential_app; [apply sequential_outsHistory; assumption|].
          apply sequential_app; [|apply sequential_insHistory; assumption].
          assumption.
      + right.

        apply ssequential_app_inv in H5.
        destruct H5 as [no [nai ?]]; dest; subst.
        apply ssequential_app_inv in H12.
        destruct H12 as [na [ni ?]]; dest; subst.

        eapply extInterleaved_atomic_extInterleavedL in H11; eauto.
        destruct H11 as [datms [? [? [? [m ?]]]]]; dest.
        rewrite H11 in *; clear H11.
        
        eapply well_interleaved_reducible with (st1:= sti1) in H; eauto.
        destruct H as [ratms [rm ?]]; dest.
        exists (outs ++ List.concat ratms ++ ins).
        eexists.
        split; [|split].
        * do 2 (eapply steps_append; eauto).
        * eexists; split.
          { apply ssequential_app; [apply ssequential_outsHistory; eassumption|].
            apply ssequential_app; [|apply ssequential_insHistory; eassumption].
            eassumption.
          }
          { repeat rewrite concat_app.
            repeat rewrite <-lift_each_concat.
            reflexivity.
          }
        * omega.
  Qed.

End WellInterleaved.

Section Pushable.
  Context {oifc: OStateIfc}.
  Variables (sys: System) (P: MState -> Prop)
            (hst1: MHistory) (l2: MLabel).

  Hypotheses (Hpinit: PInitializing sys P hst1).

  Definition LRPushable (lpush rpush: MHistory -> Prop) (hsts: list MHistory) :=
    forall lhst rhst hsts1 hsts2 hsts3,
      hsts = hsts3 ++ lhst :: hsts2 ++ rhst :: hsts1 ->
      lpush lhst -> rpush rhst ->
      ReducibleP sys P (lhst ++ rhst) (rhst ++ lhst).

  Lemma LRPushable_split_left:
    forall lpush rpush hsts1 hsts2,
      LRPushable lpush rpush (hsts1 ++ hsts2) ->
      LRPushable lpush rpush hsts1.
  Proof.
    unfold LRPushable; intros; subst.
    eapply H; eauto.
    instantiate (1:= hsts0 ++ hsts2).
    instantiate (1:= hsts3).
    instantiate (1:= hsts4).
    repeat (rewrite <-app_assoc; simpl).
    reflexivity.
  Qed.

  Lemma LRPushable_split_right:
    forall lpush rpush hsts1 hsts2,
      LRPushable lpush rpush (hsts1 ++ hsts2) ->
      LRPushable lpush rpush hsts2.
  Proof.
    unfold LRPushable; intros; subst.
    eapply H; eauto.
    instantiate (1:= hsts0).
    instantiate (1:= hsts3).
    instantiate (1:= hsts1 ++ hsts4).
    repeat (rewrite <-app_assoc; simpl).
    reflexivity.
  Qed.

  Lemma LRPushable_commutative_left:
    forall lpush rpush hsts phst,
      LRPushable lpush rpush (hsts ++ [phst]) ->
      Forall lpush hsts ->
      Forall (PPreserving sys P) hsts ->
      rpush phst ->
      ReducibleP sys P (List.concat hsts ++ phst) (phst ++ List.concat hsts).
  Proof.
    induction hsts as [|hst hsts]; simpl; intros;
      [rewrite app_nil_r; apply reducibleP_refl|].

    inv H0; inv H1.
    eapply reducibleP_trans.
    - rewrite <-app_assoc.
      apply reducibleP_app_1.
      apply IHhsts; auto.
      apply LRPushable_split_right with (hsts1:= [hst]); auto.
    - do 2 rewrite app_assoc.
      apply reducibleP_app_2.
      + red in H; red; intros.
        eapply H; eauto.
        instantiate (1:= nil).
        instantiate (1:= hsts).
        instantiate (1:= nil).
        reflexivity.
      + apply PPreserving_Forall_concat; assumption.
  Qed.

  Lemma left_pushable_left:
    forall lpush hsts,
      Forall lpush hsts ->
      Forall (fun hst =>
                lpush hst ->
                Reducible sys (hst ++ hst1) (hst1 ++ hst)) hsts ->
      Reducible sys (List.concat hsts ++ hst1)
                (hst1 ++ List.concat hsts).
  Proof.
    induction hsts as [|hst hsts]; simpl; intros;
      [rewrite app_nil_r; apply reducible_refl|].
    inv H; inv H0.
    specialize (H2 H3).
    eapply reducible_trans.
    - rewrite <-app_assoc.
      apply reducible_app_1.
      apply IHhsts; assumption.
    - do 2 rewrite app_assoc.
      apply reducible_app_2; try assumption.
  Qed.

  Definition PushableHst :=
    exists (lpush rpush: MHistory -> Prop),
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (Discontinuous hst1) hsts ->
        Forall (PPreserving sys P) hsts /\
        Forall (fun hst => lpush hst \/ rpush hst) hsts /\
        Forall (fun hst => lpush hst ->
                           Reducible sys (hst ++ hst1) (hst1 ++ hst)) hsts /\
        Forall (fun hst => rpush hst ->
                           ReducibleP sys P (l2 :: hst) (hst ++ [l2])) hsts /\
        LRPushable lpush rpush hsts.
  
  Lemma PushableHst_WellInterleavedHst:
    forall (Hp: PushableHst),
      WellInterleavedHst sys hst1 l2.
  Proof.
    unfold PushableHst, WellInterleavedHst; intros.
    destruct Hp as [lpush [rpush ?]]; dest.
    pose proof (H3 _ H _ _ H2 H0 H1); dest.
    generalize dependent st1.
    generalize dependent st2.
    generalize H1 H2 H4.
    eapply list_ind_pick
      with (l:= hsts) (Q0:= lpush) (Q1:= rpush); eauto; simpl; intros.

    - exists nil, nil.
      simpl in *; rewrite app_nil_r in *.
      split; auto.
      constructor.

    - clear H1 H2 H4 H5 H6 H7 H8 hsts; rename l into hsts.
      exists hsts, nil.

      specialize (H3 _ H11 _ _ H9 H12 H0); dest.
      pose proof (left_pushable_left H H3).
      inv H12.
      apply H6 in H14; [|assumption].
      
      simpl; split; auto.
      + econstructor; eauto.
      + apply distribution_left.
      
    - clear H1 H2 H4 H5 H6 H7 H8 hsts.
      rename l0 into hsts2; rename l1 into hsts1.

      specialize (H3 _ H13 _ _ H11 H14 H10); dest.

      assert (ReducibleP sys P ((l2 :: List.concat hsts2) ++ a)
                        (a ++ l2 :: List.concat hsts2)).
      { apply Forall_app_inv in H12; dest.
        change (l2 :: List.concat hsts2) with ([l2] ++ List.concat hsts2).
        rewrite <-app_assoc.
        eapply reducibleP_trans.
        { apply reducibleP_app_1.
          eapply LRPushable_commutative_left with (lpush:= lpush); eauto.
          eapply LRPushable_split_left with (hsts2:= hsts1).
          rewrite <-app_assoc; assumption.
        }
        { do 2 rewrite app_assoc.
          apply reducibleP_app_2.
          { rewrite Forall_forall in H4.
            apply H4; [|assumption].
            apply in_or_app; right.
            left; reflexivity.
          }
          { apply PPreserving_Forall_concat; assumption. }
        }
      }

      apply Forall_app_inv in H10; dest; inv H8.
      apply Forall_app_inv in H11; dest; inv H10.
      apply Forall_app_inv in H12; dest; inv H11.
      specialize (H9 (Forall_app H7 H17) (Forall_app H8 H19) (Forall_app H10 H21)).

      replace (l2 :: List.concat (hsts2 ++ a :: hsts1) ++ hst1)
        with (((l2 :: List.concat hsts2) ++ a) ++ List.concat hsts1 ++ hst1)
        in H14
        by (repeat rewrite concat_app;
            simpl; repeat rewrite app_assoc; reflexivity).
      eapply steps_split in H14; [|reflexivity].
      destruct H14 as [sti [? ?]].

      assert (P sti).
      { eapply steps_split in H11; [|reflexivity].
        destruct H11 as [psti [? ?]].
        apply Hpinit in H11.
        eapply PPreserving_Forall_concat.
        { eapply H21. }
        { eassumption. }
        { assumption. }
      }
      apply H6 in H12; eauto; clear H14.
      
      pose proof (steps_append H11 H12); clear H11 H12 sti.
      rewrite <-app_assoc in H14.
      eapply steps_split in H14; [|reflexivity].
      destruct H14 as [sti [? ?]].
      match type of H11 with
      | steps _ _ _ ?rhst _ =>
        replace rhst with (l2 :: List.concat (hsts2 ++ hsts1) ++ hst1) in H11
        by (repeat rewrite concat_app;
            simpl; repeat rewrite app_assoc; reflexivity)
      end.
      specialize (H9 _ _ H13 H11).
      destruct H9 as [rhst1 [rhst2 ?]]; dest.
      pose proof (steps_append H9 H12).

      exists rhst1, (a :: rhst2).
      split.
      + simpl; rewrite <-app_assoc; assumption.
      + apply distribution_add_right_head; auto.
  Qed.
  
End Pushable.

Section LPushable.
  Context {oifc: OStateIfc}.
  Variables (sys: System).

  Definition LPushableHst (hst1: MHistory) (l2: MLabel) :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (Discontinuous hst1) hsts ->
        Forall (fun hst => Reducible sys (hst ++ hst1) (hst1 ++ hst)) hsts.

  Lemma LPushableHst_PushableHst:
    forall hst1 l2
           (Hlp: LPushableHst hst1 l2),
      PushableHst sys (fun _ => True) hst1 l2.
  Proof.
    unfold LPushableHst, PushableHst; intros.
    exists (fun _ => True), (fun _ => False).
    intros.
    specialize (Hlp _ H _ _ H0 H1 H2).
    repeat split.
    - apply Forall_forall; intros.
      red; intros; auto.
    - apply Forall_forall; intros; auto.
    - eapply Forall_impl; [|eapply Hlp].
      intros; auto.
    - apply Forall_forall; intros; exfalso; auto.
    - red; intros; exfalso; auto.
  Qed.

  Lemma LPushableHst_WellInterleavedHst:
    forall hst1 l2 (Hlp: LPushableHst hst1 l2),
      WellInterleavedHst sys hst1 l2.
  Proof.
    intros.
    apply PushableHst_WellInterleavedHst with (P:= fun _ => True).
    - red; intros; auto.
    - apply LPushableHst_PushableHst; assumption.
  Qed.

End LPushable.

Section RPushable.
  Context {oifc: OStateIfc}.
  Variables (sys: System) (P: MState -> Prop)
            (hst1: MHistory) (l2: MLabel).

  Hypotheses (Hpinit: PInitializing sys P hst1).

  Definition RPushableHst :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (fun hst => Discontinuous hst1 hst) hsts ->
        Forall (fun hst => PPreserving sys P hst /\
                           ReducibleP sys P (l2 :: hst) (hst ++ [l2])) hsts.

  Lemma RPushableHst_PushableHst:
    forall (Hrp: RPushableHst),
      PushableHst sys P hst1 l2.
  Proof.
    unfold RPushableHst, PushableHst; intros.
    exists (fun _ => False), (fun _ => True).
    intros.
    specialize (Hrp _ H _ _ H0 H1 H2).
    repeat split.
    - eapply Forall_impl; [|eapply Hrp].
      simpl; intros; dest; auto.
    - apply Forall_forall; intros; auto.
    - apply Forall_forall; intros; exfalso; auto.
    - eapply Forall_impl; [|eapply Hrp].
      simpl; intros; dest; auto.
    - red; intros; exfalso; auto.
  Qed.

  Lemma RPushableHst_WellInterleavedHst:
    forall (Hrp: RPushableHst),
      WellInterleavedHst sys hst1 l2.
  Proof.
    intros.
    apply PushableHst_WellInterleavedHst with (P0:= P).
    - assumption.
    - apply RPushableHst_PushableHst; assumption.
  Qed.

End RPushable.

Close Scope list.

