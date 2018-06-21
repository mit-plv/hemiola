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
          rule_trs rule post porq ins = (nost, norq, outs) ->
          idsOf outs = [rsmidx]) /\
      In (Build_Channel rqoidx rqmidx (rule_oidx rule)) (ctr_chns topo) /\
      In (Build_Channel (rule_oidx rule) rsmidx rqoidx) (ctr_chns topo).

  Definition UpRqFwdRule (rule: Rule) :=
    exists coidx rqmidx rqfmidx poidx,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_trs rule post porq ins = (nost, norq, outs) ->
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
          rule_trs rule post porq ins = (nost, norq, outs) ->
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
          rule_trs rule post pors ins = (nost, nors, outs) ->
          idsOf outs = [rsbmidx]) /\
      (getParent (ctr_tr topo) (rule_oidx rule))
        >>=[False] (fun ptr => trCurOIdxOf ptr = poidx) /\
      In (Build_Channel poidx rsmidx (rule_oidx rule)) (ctr_chns topo) /\
      In (Build_Channel (rule_oidx rule) rsbmidx coidx) (ctr_chns topo).

  Definition UpRsBackRule (rule: Rule) :=
    exists coinds rsminds rsbmidx rsboidx,
      rule_minds rule = rsminds /\
      (forall post pors ins nost nors outs,
          rule_trs rule post pors ins = (nost, nors, outs) ->
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
  Definition PartialBlockingPrec (oidx: IdxT): OPrec :=
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
    (rule_precond rule) ->oprec (PartialBlockingPrec (rule_oidx rule)).

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

Lemma atomic_trsTypeOf:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    trsTypeOf hst = TInt.
Proof.
  intros; inv H; reflexivity.
Qed.

Definition Separated (hsts: list MHistory) :=
  forall hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 ->
    ~ Continuous hst1 hst2.

Definition Prec := MState -> Prop.
Definition Trs := MState -> MState.

Definition DenotationalL (sys: System) (prec: Prec) (trs: Trs) (hst: MHistory) :=
  forall st1,
    prec st1 ->
    steps step_m sys st1 hst (trs st1).

Definition DenotationalR (sys: System) (prec: Prec) (trs: Trs) (hst: MHistory) :=
  forall st1 st2,
    steps step_m sys st1 hst st2 ->
    prec st1 /\ st2 = trs st1.

Definition Denotational (sys: System) (prec: Prec) (trs: Trs) (hst: MHistory) :=
  DenotationalL sys prec trs hst /\
  DenotationalR sys prec trs hst.

Definition Nonconflicting (p1 p2: Prec) (f1 f2: Trs) :=
  (forall o, p2 (f1 o) -> p2 o) /\
  (forall o, p1 o -> p1 (f2 o)) /\
  (forall o, f2 (f1 o) = f1 (f2 o)).

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

Definition BCommutable (sys: System) (hst1 hst2: MHistory) :=
  behaviorOf sys hst2 ++ behaviorOf sys hst1 =
  behaviorOf sys hst1 ++ behaviorOf sys hst2.

Lemma silent_denotational:
  forall sys, Denotational sys (fun _ => True) id [RlblEmpty _].
Proof.
  intros.
  hnf; split; hnf; intros.
  - repeat econstructor.
  - inv H; inv H3; inv H5; auto.
Qed.

Lemma ins_denotational:
  forall sys eins,
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    Denotational sys (fun _ => True)
                 (fun st => {| bst_oss := bst_oss st;
                               bst_orqs := bst_orqs st;
                               bst_msgs := enqMsgs eins (bst_msgs st) |})
                 [RlblIns eins].
Proof.
  intros.
  hnf; split; hnf; intros.
  - econstructor.
    + econstructor.
    + econstructor; eauto.
      destruct st1; reflexivity.
  - inv H1; inv H5; inv H7; auto.
Qed.

Lemma outs_denotational:
  forall sys eouts,
    eouts <> nil ->
    ValidMsgsExtOut sys eouts ->
    Denotational sys (fun st => Forall (FirstMPI (bst_msgs st)) eouts)
                 (fun st => {| bst_oss := bst_oss st;
                               bst_orqs := bst_orqs st;
                               bst_msgs := deqMsgs (idsOf eouts) (bst_msgs st) |})
                 [RlblOuts eouts].
Proof.
  intros.
  hnf; split; hnf; intros.
  - econstructor.
    + econstructor.
    + econstructor; eauto.
      destruct st1; reflexivity.
  - inv H1; inv H5; inv H7; auto.
Qed.

Inductive DenoteIntHst: Prec -> Trs -> MHistory -> Prop :=
| DenoteNil: DenoteIntHst (fun _ => True) id nil
| DenoteCons:
    forall p f hst,
      DenoteIntHst p f hst ->
      forall rule ins outs,
        DenoteIntHst
          (fun st =>
             p st /\
             let oss := bst_oss (f st) in
             let orqs := bst_orqs (f st) in
             let msgs := bst_msgs (f st) in
             Forall (FirstMPI msgs) ins /\
             exists ost orq,
               oss@[rule_oidx rule] = Some ost /\
               orqs@[rule_oidx rule] = Some orq /\
               rule_precond rule ost orq ins /\
               snd (rule_trs rule ost orq ins) = outs
          )
          (fun st =>
             let oss := bst_oss (f st) in
             let orqs := bst_orqs (f st) in
             let msgs := bst_msgs (f st) in
             oss@[rule_oidx rule] >>=[st]
                (fun ost =>
                   orqs@[rule_oidx rule] >>=[st]
                       (fun orq =>
                          match rule_trs rule ost orq ins with
                          | (nost, norq, _) =>
                            {| bst_oss := oss +[rule_oidx rule <- nost];
                               bst_orqs := orqs +[rule_oidx rule <- norq];
                               bst_msgs := enqMsgs outs (deqMsgs (idsOf ins) msgs)
                            |}
                          end)))
          (RlblInt rule ins outs :: hst).

Lemma denoteIntHst_prec_trs_exist:
  forall hst,
    InternalHistory hst ->
    exists p f, DenoteIntHst p f hst.
Proof.
  induction hst; simpl; intros.
  - do 2 eexists; constructor.
  - inv H.
    specialize (IHhst H3).
    destruct IHhst as [pp [pf ?]].
    destruct a as [| |rule ins outs|]; try (elim H2; fail).
    do 2 eexists.
    econstructor; eauto.
Qed.

Definition WfLbl (sys: System) (lbl: MLabel) :=
  match lbl with
  | RlblEmpty _ => True
  | RlblIns eins => eins <> nil /\ ValidMsgsExtIn sys eins
  | RlblOuts eouts => eouts <> nil /\ ValidMsgsExtOut sys eouts
  | RlblInt rule ins outs =>
    In (rule_oidx rule) (sys_oinds sys) /\
    ValidMsgsIn sys ins /\
    idsOf ins = rule_minds rule /\
    map msg_id (valsOf ins) = rule_msg_ids rule /\
    In rule (sys_rules sys) /\
    ValidMsgsOut sys outs /\
    DisjList (idsOf ins) (idsOf outs)
  end.

Definition WfHistory (sys: System) (hst: MHistory) :=
  Forall (WfLbl sys) hst.

Lemma steps_wfHistory:
  forall sys st1 hst st2,
    steps step_m sys st1 hst st2 ->
    WfHistory sys hst.
Proof.
  induction 1; simpl; intros; [constructor|].
  constructor; auto.
  clear H; inv H0; red; auto 7.
Qed.

Lemma denoteIntHst_denotationalL:
  forall sys p f hst,
    WfHistory sys hst ->
    DenoteIntHst p f hst ->
    DenotationalL sys p f hst.
Proof.
  induction 2; simpl; intros; [constructor|].
  inv H; econstructor; [destruct H; eapply IHDenoteIntHst; eauto|].
  dest.
  remember (rule_trs rule x x0 ins) as nst.
  destruct nst as [[noss norqs] nmsgs].
  apply eq_sym in Heqnst.
  simpl in H7; subst.
  red in H3; dest.
  econstructor; try reflexivity; try eassumption; simpl.
  - destruct (f st1); reflexivity.
  - rewrite H2, H5; simpl.
    rewrite Heqnst; reflexivity.
Qed.

Lemma denoteIntHst_denotationalR:
  forall sys p f hst,
    DenoteIntHst p f hst ->
    DenotationalR sys p f hst.
Proof.
  induction 1; simpl; intros;
    [red; intros; inv H; auto|].

  red; intros; inv H0.
  specialize (IHDenoteIntHst _ _ H4); dest; subst.
  inv H6; rewrite H21; simpl.
  repeat split; auto.
  - do 2 eexists; repeat split; try eassumption.
    rewrite H16; reflexivity.
  - rewrite H8, H9; simpl.
    rewrite H16; reflexivity.
Qed.

Lemma denoteIntHst_denotational:
  forall sys p f hst,
    WfHistory sys hst ->
    DenoteIntHst p f hst ->
    Denotational sys p f hst.
Proof.
  intros; split.
  - apply denoteIntHst_denotationalL; auto.
  - apply denoteIntHst_denotationalR; auto.
Qed.

Lemma atomic_denotational:
  forall sys inits ins hst outs eouts,
    WfHistory sys hst ->
    Atomic msg_dec inits ins hst outs eouts ->
    exists p f,
      Denotational sys p f hst /\
      DenoteIntHst p f hst.
Proof.
  intros.
  apply atomic_internal_history in H0.
  apply denoteIntHst_prec_trs_exist in H0.
  destruct H0 as [p [f ?]].
  pose proof (denoteIntHst_denotational H H0).
  eauto.
Qed.

Lemma nonconflicting_reduced:
  forall sys hst1 hst2 p1 p2 f1 f2,
    BCommutable sys hst1 hst2 ->
    Denotational sys p1 f1 hst1 ->
    Denotational sys p2 f2 hst2 ->
    Nonconflicting p1 p2 f1 f2 ->
    Reduced sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  intros; red; intros.
  split.
  - eapply steps_split in H3; [|reflexivity].
    destruct H3 as [sti [? ?]].
    red in H0, H1; dest.
    specialize (H6 _ _ H3); specialize (H5 _ _ H4); dest; subst.
    red in H2; dest.
    specialize (H2 _ H5).
    specialize (H1 _ H2).
    specialize (H7 _ H6).
    specialize (H0 _ H7).
    rewrite H8.
    eapply steps_append; eauto.
  - red; do 2 rewrite behaviorOf_app; assumption.
Qed.

Definition DiscontinuousTrsType (tty1 tty2: TrsType) :=
  match tty1, tty2 with
  | TSlt, _ => True
  | _, TSlt => True
  | TInt, _ => True
  | _, TInt => True
  | _, _ => False
  end.

Lemma discontinuous_trs_type_bcommutable:
  forall sys hst1 hst2,
    STransactional msg_dec hst1 ->
    STransactional msg_dec hst2 ->
    DiscontinuousTrsType (trsTypeOf hst1) (trsTypeOf hst2) ->
    BCommutable sys hst1 hst2.
Proof.
  intros.
  inv H.
  - inv H0; try reflexivity.
    eapply atomic_behavior_nil with (sys:= sys) in H.
    hnf; rewrite H; reflexivity.
  - inv H0; try reflexivity; try (intuition; fail).
    eapply atomic_behavior_nil with (sys:= sys) in H.
    hnf; rewrite H; reflexivity.
  - inv H0; try reflexivity; try (intuition; fail).
    eapply atomic_behavior_nil with (sys:= sys) in H.
    hnf; rewrite H; reflexivity.
  - eapply atomic_behavior_nil with (sys:= sys) in H2.
    hnf; rewrite H2.
    rewrite app_nil_r; reflexivity.
Qed.

Corollary discontinuous_trs_type_reduced:
  forall sys hst1 hst2 p1 p2 f1 f2,
    STransactional msg_dec hst1 ->
    STransactional msg_dec hst2 ->
    DiscontinuousTrsType (trsTypeOf hst1) (trsTypeOf hst2) ->
    Denotational sys p1 f1 hst1 ->
    Denotational sys p2 f2 hst2 ->
    Nonconflicting p1 p2 f1 f2 ->
    Reduced sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  intros.
  eapply nonconflicting_reduced; eauto.
  eapply discontinuous_trs_type_bcommutable; eauto.
Qed.

Lemma discontinuous_trs_type_nonconflicting:
  forall sys hst1 hst2,
    WfHistory sys hst1 -> WfHistory sys hst2 ->
    STransactional msg_dec hst1 ->
    STransactional msg_dec hst2 ->
    DiscontinuousTrsType (trsTypeOf hst1) (trsTypeOf hst2) ->
    exists p1 p2 f1 f2,
      Denotational sys p1 f1 hst1 /\
      Denotational sys p2 f2 hst2 /\
      Nonconflicting p1 p2 f1 f2.
Proof.
  intros; inv H1.

  - inv H2.
    + do 4 eexists.
      split; [|split];
        [apply silent_denotational|apply silent_denotational|].
      hnf; auto.
    + do 4 eexists.
      inv H0; destruct H4; clear H5.
      split; [|split];
        [apply silent_denotational|apply ins_denotational; auto|].
      hnf; auto.
    + do 4 eexists.
      inv H0; destruct H4; clear H5.
      split; [|split];
        [apply silent_denotational|apply outs_denotational; auto|].
      hnf; auto.
    + eapply atomic_denotational in H1; eauto.
      destruct H1 as [p2 [f2 [? ?]]].
      do 4 eexists.
      split; [|split]; [apply silent_denotational|eassumption|].
      hnf; auto.

  - inv H2; try (elim H3; fail).
    + do 4 eexists.
      inv H; destruct H4; clear H5.
      split; [|split];
        [apply ins_denotational; auto|apply silent_denotational|].
      hnf; auto.
    + pose proof (atomic_denotational H0 H1).
      destruct H2 as [p2 [f2 [? ?]]].
      inv H; inv H7; clear H8.
      do 4 eexists.
      split; [|split]; [apply ins_denotational; auto|eassumption|].
      (** TODO: prove a lemma like:
       * Atomic msg_dec inits ins hst2 outs eouts ->
       * DenoteIntHst p f hst2 ->
       * DisjList eins ins ->
       * DisjList (idsOf eins) (idsOf outs) ->
       * Nonconflicting (fun _ : MState => True) p
       *   (fun st : MState =>
       *     {| bst_oss := bst_oss st;
       *        bst_orqs := bst_orqs st;
       *        bst_msgs := enqMsgs eins (bst_msgs st) |}) f.
       *)
      admit. (* similar to [msg_ins_reduced_2] *)

  - inv H2; try (elim H3; fail).
    + do 4 eexists.
      inv H; destruct H4; clear H5.
      split; [|split];
        [apply outs_denotational; auto|apply silent_denotational|].
      hnf; auto.
    + pose proof (atomic_denotational H0 H1).
      destruct H2 as [p2 [f2 [? ?]]].
      inv H; inv H7; clear H8.
      do 4 eexists.
      split; [|split]; [apply outs_denotational; auto|eassumption|].
      admit. (* similar to [msg_outs_reduced_1] *)

  - inv H2.
    + eapply atomic_denotational in H4; eauto.
      destruct H4 as [p1 [f1 [? ?]]].
      do 4 eexists.
      split; [|split]; [eassumption|apply silent_denotational|].
      hnf; auto.
    + pose proof (atomic_denotational H H4).
      destruct H1 as [p1 [f1 [? ?]]].
      inv H0; inv H7; clear H8.
      do 4 eexists.
      split; [|split]; [eassumption|apply ins_denotational; auto|].
      admit. (* similar to [msg_ins_reduced_1] *)
    + pose proof (atomic_denotational H H4).
      destruct H1 as [p1 [f1 [? ?]]].
      inv H0; inv H7; clear H8.
      do 4 eexists.
      split; [|split]; [eassumption|apply outs_denotational; auto|].
      rename eouts0 into mouts.
      (** TODO: prove a lemma similar to above, requiring:
       * DisjList (idsOf mouts) (idsOf ins) /\
       * DisjList mouts outs *)
      admit. (* similar to [msg_outs_reduced_2] *)

    + pose proof (atomic_denotational H H4).
      destruct H2 as [p1 [f1 [? ?]]].
      pose proof (atomic_denotational H0 H1).
      destruct H6 as [p2 [f2 [? ?]]].
      exists p1, p2, f1, f2.
      do 2 (split; auto).
      admit.
Admitted.

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

