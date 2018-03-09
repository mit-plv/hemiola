Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts.

Section Simulation.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS StateS} `{HasLabel LabelS}.
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
        match extLabel (StateT:= StateI) impl (getLabel ilbl) with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = Some (p elbl) /\
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
          map p (behaviorOf (StateT:= StateI) impl ihst) =
          behaviorOf (StateT:= StateS) spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H3).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H5; [|exact H8].
    remember (extLabel impl (getLabel lbl)) as ilbl; clear Heqilbl.
    destruct ilbl as [elbl|].

    - destruct H5 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H7, H9; simpl.
        reflexivity.
    - destruct H5.
      * destruct H5 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H7, H9; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

  Hypothesis (Hsimi: sim (initsOf impl) (initsOf spec)).

  Theorem simulation_implies_refinement:
    (steps stepI) # (steps stepS) |-- impl ⊑[p] spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H3.
    eapply simulation_steps in H4; [|exact Hsimi].
    destruct H4 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End Simulation.

Section LInvSim.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SysI StateI LabelI) (stepS: Step SysS StateS LabelS)
            (sim: StateI -> StateS -> Prop)
            (p: Label -> Label)
            (linv: LabelI -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl: SysI) (spec: SysS).

  Definition LInvSim :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ilbl ist2,
        linv ilbl ->
        stepI impl ist1 ilbl ist2 ->
        match extLabel (StateT:= StateI) impl (getLabel ilbl) with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = Some (p elbl) /\
              ist2 ≈ sst2)
        end.

  Hypothesis (Hsim: LInvSim).

  Lemma label_inv_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        Forall linv ihst ->
        steps stepI impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          map p (behaviorOf (StateT:= StateI) impl ihst) =
          behaviorOf (StateT:= StateS) spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 3; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    inv H4.
    specialize (IHsteps H3 H10).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H6; [|exact H8|exact H9].
    remember (extLabel impl (getLabel lbl)) as ilbl; clear Heqilbl.
    destruct ilbl as [elbl|].

    - destruct H6 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H7, H11; simpl.
        reflexivity.
    - destruct H6.
      * destruct H6 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H7, H11; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

End LInvSim.

Definition LiftSimL {StateI1 StateS} (sim: StateI1 -> StateS -> Prop)
           {StateI2} (f: StateI2 -> StateI1): StateI2 -> StateS -> Prop :=
  fun sti2 sts => sim (f sti2) sts.

Definition LiftSimR {StateI StateS1} (sim: StateI -> StateS1 -> Prop)
           {StateS2} (f: StateS2 -> StateS1): StateI -> StateS2 -> Prop :=
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
      isInternal impl (mid_from (msg_id msg)) =
      isInternal spec (mid_from (msg_id (mmap msg))) /\
      isInternal impl (mid_to (msg_id msg)) =
      isInternal spec (mid_to (msg_id (mmap msg))).

  Lemma validMsgMap_from_isExternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        isExternal impl (mid_from (msg_id msg)) = b ->
        isExternal spec (mid_from (msg_id (mmap msg))) = b.
  Proof.
    unfold ValidMsgMap; intros.
    rewrite <-H0.
    specialize (H msg); dest.
    do 2 rewrite internal_external_negb in H.
    destruct (isExternal _ _);
      destruct (isExternal _ _); auto.
  Qed.

  Lemma validMsgMap_to_isInternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        isInternal impl (mid_to (msg_id msg)) = b ->
        isInternal spec (mid_to (msg_id (mmap msg))) = b.
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
    unfold ValidMsgMap, isExternal, isInternal; intros.
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

  (* [deinitialize] makes all messages in a given [MessagePool] uninitialized,
   * meaning that the messages are requests in which the corresponding 
   * transactions are not started yet.
   *
   * Each message in [mp] is assumed to be unique 
   * in terms of [TInfo] it carries.
   *)
  Definition deinitialize (mp: MessagePool TMsg) :=
    map (fun tmsg =>
           toTMsgU (msgP (match tmsg_info tmsg with
                          | Some tinfo =>
                            (* NOTE: any rules built by the synthesizer do not
                             * generate a message where [tinfo_rqin tinfo] is
                             * [nil]. Actually, it is always a singleton, i.e.,
                             * a single request.
                             *)
                            hd (tmsg_msg tmsg) (tinfo_rqin tinfo)
                          | None => tmsg_msg tmsg
                          end))) mp.
  
  Definition SimMP (imsgs smsgs: MessagePool TMsg) :=
    smsgs = deinitialize (rollback imsgs).

  Lemma rollbacked_enqMP_toTMsgU:
    forall msgs emsg rb,
      enqMP (toTMsgU (msgP emsg)) (deinitialize (rollbacked rb msgs)) =
      deinitialize (rollbacked rb (enqMP (toTMsgU emsg) msgs)).
  Proof.
    induction msgs; simpl; intros.
    - unfold deinitialize, enqMP.
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

End SimMP.

