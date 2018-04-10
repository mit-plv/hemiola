Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts Invariant.

Set Implicit Arguments.

Section Simulation.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI} `{HasInit StateI} `{HasLabel LabelI}
          `{IsSystem SysS} `{HasInit StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SysI StateI LabelI) (stepS: Step SysS StateS LabelS)
            (sim: StateI -> StateS -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl: SysI) (spec: SysS).

  Definition Simulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ilbl ist2,
        stepI impl ist1 ilbl ist2 ->
        match extLabel impl (getLabel ilbl) with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel spec (getLabel slbl) = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel spec (getLabel slbl) = Some (p elbl) /\
              ist2 ≈ sst2)
        end.

  Hypothesis (Hsim: Simulates).

  Lemma simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        steps stepI impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) =
          behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H5).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H7; [|exact H10].
    remember (extLabel impl (getLabel lbl)) as ilbl; clear Heqilbl.
    destruct ilbl as [elbl|].

    - destruct H7 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H9, H11; simpl.
        reflexivity.
    - destruct H7.
      * destruct H7 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H9, H11; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

  Hypothesis (Hsimi: sim initsOf initsOf).

  Theorem simulation_implies_refinement:
    (steps stepI) # (steps stepS) |-- impl ⊑[p] spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H5.
    eapply simulation_steps in H6; [|exact Hsimi].
    destruct H6 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End Simulation.

Section InvSim.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI} `{HasInit StateI} `{HasLabel LabelI}
          `{IsSystem SysS} `{HasInit StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SysI StateI LabelI) (stepS: Step SysS StateS LabelS)
            (ginv: StateI -> Prop)
            (sim: StateI -> StateS -> Prop)
            (p: Label -> Label)
            (linv: LabelI -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl: SysI) (spec: SysS).

  Definition InvSim :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ilbl ist2,
        linv ilbl ->
        stepI impl ist1 ilbl ist2 ->
        match extLabel impl (getLabel ilbl) with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel spec (getLabel slbl) = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel spec (getLabel slbl) = Some (p elbl) /\
              ist2 ≈ sst2)
        end.

  Hypothesis (Hsim: InvSim)
             (Hinv: InvStep impl stepI ginv).

  Lemma inv_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        Forall linv ihst ->
        steps stepI impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) =
          behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 4; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    inv H7.
    specialize (IHsteps H5 H6 H13).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H9;
      [|exact H11|eapply inv_steps; eauto|exact H12].
    
    remember (extLabel impl (getLabel lbl)) as ilbl; clear Heqilbl.
    destruct ilbl as [elbl|].

    - destruct H9 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H10, H14; simpl.
        reflexivity.
    - destruct H9.
      * destruct H9 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H10, H14; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

End InvSim.

Definition LiftInv {StateT1 StateT2} (f: StateT2 -> StateT1)
           (inv: StateT1 -> Prop): StateT2 -> Prop :=
  fun st2 => inv (f st2).
  
Definition LiftSimL {StateI1 StateI2} (f: StateI2 -> StateI1)
           {StateS} (sim: StateI1 -> StateS -> Prop): StateI2 -> StateS -> Prop :=
  fun sti2 sts => sim (f sti2) sts.

Definition LiftSimR {StateS1 StateS2} (f: StateS2 -> StateS1)
           {StateI} (sim: StateI -> StateS1 -> Prop): StateI -> StateS2 -> Prop :=
  fun sti sts2 => sim sti (f sts2).

Section SimMap.
  Variable (mmap: Msg -> Msg).

  Definition LabelMap (il: Label) :=
    match il with
    | LblIn imsg => LblIn (mmap imsg)
    | LblOuts outs => LblOuts (map mmap outs)
    end.

  Definition ValidMsgMap (impl spec: System) :=
    forall msg,
      fromInternal impl msg =
      fromInternal spec (mmap msg) /\
      toInternal impl msg =
      toInternal spec (mmap msg).

  Lemma validMsgMap_from_isExternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        fromExternal impl msg = b ->
        fromExternal spec (mmap msg) = b.
  Proof.
    unfold ValidMsgMap; intros.
    rewrite <-H0.
    specialize (H msg); dest.
    unfold fromInternal, fromExternal in *.
    do 2 rewrite internal_external_negb in H.
    destruct (isExternal _ _);
      destruct (isExternal _ _); auto.
  Qed.

  Lemma validMsgMap_to_isInternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        toInternal impl msg = b ->
        toInternal spec (mmap msg) = b.
  Proof.
    unfold ValidMsgMap; intros.
    rewrite <-H0.
    specialize (H msg); dest; auto.
  Qed.

  Lemma validMsgMap_same_indices:
    forall impl1 spec,
      ValidMsgMap impl1 spec ->
      forall impl2,
        indicesOf impl1 = indicesOf impl2 ->
        ValidMsgMap impl2 spec.
  Proof.
    unfold ValidMsgMap, fromInternal, toInternal, isExternal, isInternal; intros.
    rewrite <-H0; auto.
  Qed.
  
End SimMap.

(** [SimMP] defines a standard simulation between two [MessagePool]s of 
 * implementation and spec. It's basically rollback of all ongoing transactions.
 *)
Section SimMP.
  Variable msgP: Msg -> Msg.

  (* Assume [rb] is already ordered in terms of [tinfo_tid], which is uniquely 
   * assigned to each transaction.
   *)
  Fixpoint addActive (amsg: Msg) (atinfo: TInfo) (rb: MessagePool TMsg) :=
    match rb with
    | nil => {| tmsg_msg := amsg; tmsg_info := Some atinfo |} :: nil
    | tmsg :: rb' =>
      match tmsg_info tmsg with
      | Some tinfo =>
        if tinfo_tid atinfo <n tinfo_tid tinfo
        then {| tmsg_msg := amsg; tmsg_info := Some atinfo |} :: rb
        else if tinfo_tid atinfo ==n tinfo_tid tinfo
             then rb
             else tmsg :: addActive amsg atinfo rb'
      | None => {| tmsg_msg := amsg; tmsg_info := Some atinfo |} :: rb
      end
    end.
  
  Fixpoint addInactive (iam: TMsg) (rb: MessagePool TMsg) :=
    rb ++ iam :: nil.

  Fixpoint rollbacked (rb mp: MessagePool TMsg) :=
    match mp with
    | nil => rb
    | tmsg :: mp' =>
      match tmsg_info tmsg with
      | Some tinfo => rollbacked (addActive (tmsg_msg tmsg) tinfo rb) mp'
      | None => rollbacked (addInactive tmsg rb) mp'
      end
    end.

  (* [rollback], as the name says, rolls back all active messages
   * in a given [MessagePool].
   *)
  Definition rollback (mp: MessagePool TMsg) := rollbacked nil mp.

  (* [deinitialize] makes a message uninitialized. *)
  Definition deinitialize (tmsg: TMsg): TMsg :=
    toTMsgU (msgP (match tmsg_info tmsg with
                   | Some tinfo =>
                     (* NOTE: any rules built by the synthesizer do not
                      * generate a message where [tinfo_rqin tinfo] is
                      * [nil]. Actually, it is always a singleton, i.e.,
                      * a single request.
                      *)
                     hd (tmsg_msg tmsg) (tinfo_rqin tinfo)
                   | None => tmsg_msg tmsg
                   end)).

  (* NOTE: Each message in [mp] is assumed to be unique in terms of
   * [TInfo] it carries.
   *)
  Definition deinitializeMP (mp: MessagePool TMsg) :=
    map deinitialize mp.
  
  Definition SimMP (imsgs smsgs: MessagePool TMsg) :=
    smsgs = deinitializeMP (rollback imsgs).

  Lemma rollbacked_enqMP_toTMsgU:
    forall msgs emsg rb,
      enqMP (toTMsgU (msgP emsg)) (deinitializeMP (rollbacked rb msgs)) =
      deinitializeMP (rollbacked rb (enqMP (toTMsgU emsg) msgs)).
  Proof.
    induction msgs; simpl; intros.
    - unfold deinitializeMP, enqMP.
      rewrite map_app; simpl.
      reflexivity.
    - destruct (tmsg_info a); eauto.
  Qed.

  Lemma rollbacked_app:
    forall mp1 rb mp2,
      rollbacked rb (mp1 ++ mp2) =
      rollbacked (rollbacked rb mp1) mp2.
  Proof.
    induction mp1; simpl; intros; [reflexivity|].
    destruct (tmsg_info a); auto.
  Qed.

  Lemma SimMP_ext_msg_in:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall emsg,
        SimMP (enqMP (toTMsgU emsg) imsgs)
              (enqMP (toTMsgU (msgP emsg)) smsgs).
  Proof.
    unfold SimMP; intros; subst.
    unfold rollback.
    apply rollbacked_enqMP_toTMsgU.
  Qed.

  Lemma SimMP_ext_msg_immediate_out:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall emsg,
        FirstMP imsgs (toTMsgU emsg) ->
        SimMP (removeMP (toTMsgU emsg) imsgs)
              (removeMP (toTMsgU (msgP emsg)) smsgs).
  Proof.
  Admitted.

  Lemma SimMP_int_msg_immediate:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall rq rs tinfo,
        tmsg_info rq = Some tinfo ->
        tmsg_info rs = Some tinfo ->
        SimMP (distributeMsgs [rs] (removeMP rq imsgs)) smsgs.
  Proof.
  Admitted.

  Lemma SimMP_ext_msg_rq_forwarding:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall emsg fwds tinfo,
        tmsg_info emsg = None ->
        Forall (fun tmsg => tmsg_info tmsg = Some tinfo) fwds ->
        FirstMP imsgs emsg ->
        TidLtMP imsgs (tinfo_tid tinfo) ->
        SimMP (distributeMsgs fwds (removeMP emsg imsgs)) smsgs.
  Proof.
  Admitted.

  Lemma SimMP_responses_back_ext_out:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall origRq ts rss,
        Forall (fun tmsg =>
                  (tmsg_info tmsg) >>=[False] (fun tinfo => tinfo = buildTInfo ts [origRq]))
               rss ->
        ForallMP (fun tmsg =>
                    (tmsg_info tmsg) >>=[True] (fun tinfo => tinfo_tid tinfo <> ts))
                 (removeMsgs rss imsgs) ->
        SimMP (removeMsgs rss imsgs)
              (removeMP (toTMsgU (msgP origRq)) smsgs).
  Proof.
  Admitted.

  Corollary SimMP_response_back_ext_out:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall origRq ts rs,
        Forall (fun tmsg =>
                  (tmsg_info tmsg) >>=[False] (fun tinfo => tinfo = buildTInfo ts [origRq]))
               [rs] ->
        ForallMP (fun tmsg =>
                    (tmsg_info tmsg) >>=[True] (fun tinfo => tinfo_tid tinfo <> ts))
                 (removeMP rs imsgs) ->
        SimMP (removeMP rs imsgs)
              (removeMP (toTMsgU (msgP origRq)) smsgs).
  Proof.
    intros; eapply SimMP_responses_back_ext_out in H0; eauto.
  Qed.
  
End SimMP.

