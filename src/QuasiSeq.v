Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.
Require Import Serial SerialFacts Reduction.

Require Import Omega Wf.

Set Implicit Arguments.

Open Scope list.

(*! Quasi-sequential histories *)

Section QuasiSeq.
  Context {oifc: OStateIfc}.
  Variables (sys: System oifc)
            (quasiSeq: forall (sys: System oifc) (hst: MHistory) (n: nat), Prop).

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

Definition ExtContinuous {oifc} (sys: System oifc)
           (hst1 hst2: MHistory) :=
  exists eouts1 inits2 ins2 outs2 eouts2,
    ExtAtomic sys msg_dec hst1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    ~ SubList (idsOf inits2) (sys_merqs sys) /\
    SubList inits2 eouts1.

Definition ExtContinuousL {oifc} (sys: System oifc)
           (hst: MHistory) (l: MLabel) :=
  exists eouts oidx ridx rins routs,
    ExtAtomic sys msg_dec hst eouts /\
    l = RlblInt oidx ridx rins routs /\
    ~ SubList (idsOf rins) (sys_merqs sys) /\
    SubList rins eouts.

Definition Discontinuous (hst1 hst2: MHistory) :=
  exists inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    DisjList inits2 eouts1.

Definition ExtInterleaved {oifc} (sys: System oifc)
           (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    ExtContinuous sys hst1 hst2 /\
    Forall (fun hst => Discontinuous hst1 hst) hsts2.

Definition ExtInterleavedL {oifc} (sys: System oifc)
           (hsts: list MHistory) :=
  exists hst1 l2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ [l2] :: hsts2 ++ hst1 :: hsts1 /\
    ExtContinuousL sys hst1 l2 /\
    Forall (fun hst => Discontinuous hst1 hst) hsts2.

Lemma extContinuous_concat:
  forall {oifc} (sys: System oifc) hst l,
    ExtContinuousL sys hst l ->
    exists neouts,
      ExtAtomic sys msg_dec (l :: hst) neouts.
Proof.
  unfold ExtContinuousL; intros; dest; subst.
  inv H.
  eexists.
  econstructor; [eassumption|].
  econstructor; eauto.
  destruct x2; try discriminate.
  elim H1; apply SubList_nil.
Qed.

Lemma extContinuous_hst_stransactional_length:
  forall {oifc} (sys: System oifc) hst l tn,
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
  forall {oifc} (sys: System oifc) hst l tn,
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
  forall {oifc} (sys: System oifc) atms n,
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
  destruct H2 as [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]; dest.

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
    + red; exists eouts1, oidx, ridx, inits2, routs.
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

Lemma atomic_transactions_sequential_or_extInterleaved:
  forall {oifc} (sys: System oifc) trss st1 st2,
    Reachable (steps step_m) sys st1 ->
    steps step_m sys st1 (List.concat trss) st2 ->
    Forall (AtomicEx msg_dec) trss ->
    Sequential sys msg_dec (List.concat trss) trss \/
    ExtInterleaved sys trss.
Proof.
  induction trss as [|trs trss]; simpl; intros;
    [left; constructor; auto|].

  eapply steps_split in H0; [|reflexivity].
  destruct H0 as [sti [? ?]].
  inv H1.
  specialize (IHtrss _ _ H H0 H6); destruct IHtrss.

  - admit.
  - right.
    clear -H1.
    destruct H1 as [hst1 [l2 [hsts1 [hsts2 [hsts3 [? [? ?]]]]]]]; subst.
    exists hst1, l2, hsts1, hsts2, (trs :: hsts3).
    split; auto.
Admitted.

Section WellInterleaved.
  Context {oifc: OStateIfc}.
  Variable (sys: System oifc).

  Definition WellInterleavedHst (hst1: MHistory) (l2: MLabel) :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2 hsts,
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (fun hst => Discontinuous hst1 hst) hsts ->
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
    destruct H3 as [neouts ?].
    
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

      assert (Reachable (steps step_m) sys sti1) by (red; eauto).
      pose proof (atomic_transactions_sequential_or_extInterleaved H9 H8 H2).
      destruct H10.
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
        apply ssequential_app_inv in H11.
        destruct H11 as [na [ni ?]]; dest; subst.

        eapply extInterleaved_atomic_extInterleavedL in H10; eauto.
        destruct H10 as [datms [? [? [? [m ?]]]]]; dest.
        rewrite H10 in *; clear H10.
        
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
  Variable (sys: System oifc).

  Definition LRPushable (lpush rpush: MHistory -> Prop) (hsts: list MHistory) :=
    forall lhst rhst hsts1 hsts2 hsts3,
      hsts = hsts3 ++ lhst :: hsts2 ++ rhst :: hsts1 ->
      lpush lhst -> rpush rhst ->
      Reducible sys (lhst ++ rhst) (rhst ++ lhst).

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
    forall lpush rpush hsts hst,
      LRPushable lpush rpush (hsts ++ [hst]) ->
      Forall lpush hsts ->
      rpush hst ->
      Reducible sys (List.concat hsts ++ hst) (hst ++ List.concat hsts).
  Proof.
    induction hsts; simpl; intros;
      [rewrite app_nil_r; apply reducible_refl|].

    inv H0.
    eapply reducible_trans.
    - rewrite <-app_assoc.
      apply reducible_app_1.
      apply IHhsts; auto.
      apply LRPushable_split_right with (hsts1:= [a]); auto.
    - do 2 rewrite app_assoc.
      apply reducible_app_2.
      eapply H; eauto.
      instantiate (1:= nil).
      instantiate (1:= hsts).
      instantiate (1:= nil).
      reflexivity.
  Qed.

  Lemma left_pushable_left:
    forall lpush hst1 hsts,
      Forall lpush hsts ->
      Forall (fun hst =>
                lpush hst ->
                Reducible sys (hst ++ hst1) (hst1 ++ hst)) hsts ->
      Reducible sys (List.concat hsts ++ hst1)
                (hst1 ++ List.concat hsts).
  Proof.
    induction hsts; simpl; intros;
      [rewrite app_nil_r; apply reducible_refl|].
    inv H; inv H0.
    specialize (H2 H3).
    eapply reducible_trans.
    - rewrite <-app_assoc.
      apply reducible_app_1.
      apply IHhsts; assumption.
    - do 2 rewrite app_assoc.
      apply reducible_app_2; assumption.
  Qed.

  Definition PushableHst (hst1: MHistory) (l2: MLabel) :=
    exists (lpush rpush: MHistory -> Prop),
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (fun hst => Discontinuous hst1 hst) hsts ->
        Forall (fun hst => lpush hst \/ rpush hst) hsts /\
        Forall (fun hst =>
                  lpush hst ->
                  Reducible sys (hst ++ hst1) (hst1 ++ hst)) hsts /\
        Forall (fun hst =>
                  rpush hst ->
                  Reducible sys (l2 :: hst) (hst ++ [l2])) hsts /\
        LRPushable lpush rpush hsts.
  
  Definition Pushable :=
    forall hst1 l2,
      ExtContinuousL sys hst1 l2 ->
      PushableHst hst1 l2.

  Lemma PushableHst_WellInterleavedHst:
    forall hst1 l2 (Hp: PushableHst hst1 l2),
      WellInterleavedHst sys hst1 l2.
  Proof.
    unfold PushableHst, WellInterleavedHst; intros.
    destruct Hp as [lpush [rpush ?]]; dest.
    pose proof (H3 _ H _ _ H2 H0 H1); dest.
    generalize dependent st1.
    generalize dependent st2.
    generalize H1 H2.
    eapply list_ind_pick
      with (l:= hsts) (Q0:= lpush) (Q1:= rpush); eauto; simpl; intros.

    - exists nil, nil.
      simpl in *; rewrite app_nil_r in *.
      split; auto.
      constructor.

    - clear H1 H2 H4 H5 H6 H7 hsts; rename l into hsts.
      exists hsts, nil.

      specialize (H3 _ H9 _ _ H8 H10 H0); dest.
      pose proof (left_pushable_left _ H H2).
      inv H10.
      apply H5 in H12; [|assumption].
      
      simpl; split; auto.
      + econstructor; eauto.
      + apply distribution_left.
      
    - clear H1 H2 H4 H5 H6 H7 hsts.
      rename l0 into hsts2; rename l1 into hsts1.

      specialize (H3 _ H11 _ _ H10 H12 H9); dest.

      assert (Reducible sys ((l2 :: List.concat hsts2) ++ a)
                        (a ++ l2 :: List.concat hsts2)).
      { change (l2 :: List.concat hsts2) with ([l2] ++ List.concat hsts2).
        rewrite <-app_assoc.
        eapply reducible_trans.
        { apply reducible_app_1.
          eapply LRPushable_commutative_left; eauto.
          eapply LRPushable_split_left with (hsts2:= hsts1).
          rewrite <-app_assoc; assumption.
        }
        { do 2 rewrite app_assoc.
          apply reducible_app_2.
          rewrite Forall_forall in H3.
          apply H3; [|assumption].
          apply in_or_app; right.
          left; reflexivity.
        }
      }

      apply Forall_app_inv in H9; dest; inv H7.
      apply Forall_app_inv in H10; dest; inv H9.
      specialize (H8 (Forall_app H6 H15) (Forall_app H7 H17)).

      replace (l2 :: List.concat (hsts2 ++ a :: hsts1) ++ hst1)
        with (((l2 :: List.concat hsts2) ++ a) ++ List.concat hsts1 ++ hst1)
        in H12
        by (repeat rewrite concat_app;
            simpl; repeat rewrite app_assoc; reflexivity).
      eapply steps_split in H12; [|reflexivity].
      destruct H12 as [sti [? ?]].

      apply H5 in H10; [|eauto].
      pose proof (steps_append H9 H10); clear H9 H10 sti.
      rewrite <-app_assoc in H12.
      eapply steps_split in H12; [|reflexivity].
      destruct H12 as [sti [? ?]].
      match type of H9 with
      | steps _ _ _ ?rhst _ =>
        replace rhst with (l2 :: List.concat (hsts2 ++ hsts1) ++ hst1) in H9
        by (repeat rewrite concat_app;
            simpl; repeat rewrite app_assoc; reflexivity)
      end.
      specialize (H8 _ _ H11 H9).
      destruct H8 as [rhst1 [rhst2 ?]]; dest.
      pose proof (steps_append H8 H10).

      exists rhst1, (a :: rhst2).
      split.
      + simpl; rewrite <-app_assoc; assumption.
      + apply distribution_add_right_head; auto.
  Qed.
  
  Lemma well_interleaved_push_ok:
    forall (Hp: Pushable), WellInterleaved sys.
  Proof.
    unfold Pushable, WellInterleaved; intros.
    red; intros.
    apply PushableHst_WellInterleavedHst; auto.
  Qed.

End Pushable.

Section LPushable.
  Context {oifc: OStateIfc}.
  Variable (sys: System oifc).

  Definition LPushableHst (hst1: MHistory) (l2: MLabel) :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (fun hst => Discontinuous hst1 hst) hsts ->
        Forall (fun hst => Reducible sys (hst ++ hst1) (hst1 ++ hst)) hsts.

  Lemma LPushableHst_PushableHst:
    forall hst1 l2 (Hlp: LPushableHst hst1 l2),
      PushableHst sys hst1 l2.
  Proof.
    unfold LPushableHst, PushableHst; intros.
    exists (fun _ => True), (fun _ => False).
    intros.
    repeat split.
    - apply Forall_forall; intros; auto.
    - eapply Forall_impl; [|eapply Hlp; eauto].
      intros; auto.
    - apply Forall_forall; intros; exfalso; auto.
    - red; intros; exfalso; auto.
  Qed.

  Lemma LPushableHst_WellInterleavedHst:
    forall hst1 l2 (Hlp: LPushableHst hst1 l2),
      WellInterleavedHst sys hst1 l2.
  Proof.
    intros.
    apply PushableHst_WellInterleavedHst.
    apply LPushableHst_PushableHst.
    assumption.
  Qed.

End LPushable.

Section RPushableP.
  Context {oifc: OStateIfc}.
  Variables (sys: System oifc) (P: MState oifc -> Prop)
            (hst1: MHistory) (l2: MLabel).

  Definition PInitializing :=
    forall st1 st2, steps step_m sys st1 hst1 st2 -> P st2.

  Definition PPreserving (hst: MHistory) :=
    forall st1,
      P st1 ->
      forall st2,
        steps step_m sys st1 hst st2 -> P st2.
  
  Hypotheses (Hpinit: PInitializing).

  Definition RPushableP :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (l2 :: List.concat hsts ++ hst1) st2 ->
        Forall (fun hst => Discontinuous hst1 hst) hsts ->
        Forall (fun hst => PPreserving hst /\
                           ReducibleP sys P (l2 :: hst) (hst ++ [l2])) hsts.

  Lemma RPushableP_WellInterleavedHst:
    forall (Hrp: RPushableP), WellInterleavedHst sys hst1 l2.
  Proof.
    unfold RPushableP, WellInterleavedHst; intros.
    exists nil, hsts; simpl.
    split; [|apply distribution_right].
    rewrite app_nil_r.

    specialize (Hrp _ H _ _ H2 H0 H1).
    generalize dependent st1.
    generalize dependent st2.
    induction hsts as [|hst hsts]; simpl; intros; [assumption|].

    inv Hrp; inv H1; inv H2; dest.
    specialize (IHhsts H6 H8 H9).

    replace (l2 :: (hst ++ List.concat hsts) ++ hst1)
      with ((l2 :: hst) ++ List.concat hsts ++ hst1) in H0
      by (simpl; rewrite app_assoc; reflexivity).
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti [? ?]].

    apply H2 in H3.
    - pose proof (steps_append H0 H3); clear H0 H3 sti.
      rewrite <-app_assoc in H5.
      eapply steps_split in H5; [|reflexivity].
      destruct H5 as [sti [? ?]].
      rewrite <-app_assoc.
      eapply steps_append.
      + eapply IHhsts; eassumption.
      + assumption.
    - eapply reachable_steps; eassumption.
    - eapply steps_split in H0; [|reflexivity].
      destruct H0 as [psti [? ?]].
      apply Hpinit in H0.
      assert (Forall PPreserving hsts).
      { rewrite Forall_forall in H6; apply Forall_forall; intros.
        apply H6; auto.
      }
      clear -H0 H5 H10.
      generalize dependent sti.
      induction hsts; simpl; intros;
        [inv_steps; assumption|].
      inv H10.
      eapply steps_split in H5; [|reflexivity].
      destruct H5 as [npsti [? ?]].
      eauto.
  Qed.

End RPushableP.

Close Scope list.

