Require Import Bool List String Peano_dec FinFun.
Require Import Common FMap Syntax Semantics SemFacts Invariant StepT.

Set Implicit Arguments.

Section Simulation.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI} `{HasInit SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS} `{HasInit SysS StateS} `{HasLabel LabelS}.
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
        match getLabel ilbl with
        | None => (exists sst2 slbl,
                      stepS spec sst1 slbl sst2 /\
                      getLabel slbl = None /\
                      ist2 ≈ sst2) \/
                  ist2 ≈ sst1
        | Some elbl => (exists sst2 slbl,
                           stepS spec sst1 slbl sst2 /\
                           getLabel slbl = Some (p elbl) /\
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
    destruct (getLabel lbl) as [elbl|].

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

  Hypothesis (Hsimi: sim (initsOf impl) (initsOf spec)).

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
          `{IsSystem SysI} `{HasInit SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS} `{HasInit SysS StateS} `{HasLabel LabelS}.
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
        match getLabel ilbl with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              getLabel slbl = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              getLabel slbl = Some (p elbl) /\
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
    
    destruct (getLabel lbl) as [elbl|].

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

Definition liftLmap (mmap: Msg -> Msg) (il: Label) :=
  match il with
  | LblIns ins => LblIns (map mmap ins)
  | LblOuts outs => LblOuts (map mmap outs)
  end.

Section SimMap.
  Variable (mamap: MsgAddr -> MsgAddr).

  Definition liftMmap (msg: Msg) :=
    {| msg_id := {| mid_addr := mamap (mid_addr (msg_id msg));
                    mid_tid := mid_tid (msg_id msg) |};
       msg_value := msg_value msg |}.

  Local Notation mmap := liftMmap.

  Definition ExtInjective (impl: System) :=
    forall (ma1 ma2: MsgAddr),
      maExternal impl ma1 = true ->
      maExternal impl ma2 = true ->
      mamap ma1 = mamap ma2 -> ma1 = ma2.

  Definition ValidMsgMap (impl spec: System) :=
    (forall msg,
        fromInternal impl msg = fromInternal spec (mmap msg) /\
        toInternal impl msg = toInternal spec (mmap msg)) /\
    ExtInjective impl.

  Lemma ExtInjective_same_indices:
    forall impl1 impl2,
      indicesOf impl1 = indicesOf impl2 ->
      ExtInjective impl1 ->
      ExtInjective impl2.
  Proof.
    unfold ExtInjective, maExternal; intros.
    apply H0; auto.
    - unfold_idx; rewrite H; auto.
    - unfold_idx; rewrite H; auto.
  Qed.

  Lemma validMsgMap_from_isExternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        fromExternal impl msg = b ->
        fromExternal spec (mmap msg) = b.
  Proof.
    unfold ValidMsgMap; intros; dest.
    rewrite <-H0.
    specialize (H msg); dest.
    unfold_idx.
    destruct (ma_from _ ?<n _);
      destruct (ma_from _ ?<n _); auto.
  Qed.

  Lemma validMsgMap_to_isInternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        toInternal impl msg = b ->
        toInternal spec (mmap msg) = b.
  Proof.
    unfold ValidMsgMap; intros; dest.
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
    unfold ValidMsgMap; unfold_idx; intros; dest.
    split.
    - rewrite <-H0; auto.
    - eapply ExtInjective_same_indices; eauto.
  Qed.

  Lemma validMsgMap_ValidMsgsExtIn:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        ValidMsgsExtIn spec (map mmap eins).
  Proof.
    intros.
    destruct H0; split.
    - clear -H H0; induction eins; simpl; [constructor|].
      inv H0; constructor; auto.
      red in H; dest; split.
      + apply negb_false_iff.
        rewrite <-fromInternal_fromExternal_negb.
        apply negb_false_iff in H0.
        rewrite <-fromInternal_fromExternal_negb in H0.
        specialize (H a); dest.
        rewrite <-H; auto.
      + specialize (H a); dest.
        rewrite <-H3; auto.
    - destruct H; clear H.
      unfold WellDistrMsgs in *.
      induction eins; simpl; intros; auto.
      unfold id in *; inv H0; inv H1; dest.
      constructor; auto.
      intro Hx; elim H3; clear -H H2 H5 Hx.
      induction eins; [elim Hx|].
      inv H5; inv Hx; dest.
      + assert (maExternal impl (msgAddrOf a) = true).
        { apply orb_true_intro; left; assumption. }
        assert (maExternal impl (msgAddrOf a0) = true).
        { apply orb_true_intro; left; assumption. }
        destruct a as [[[from1 to1 chn1] tid1] val1].
        destruct a0 as [[[from2 to2 chn2] tid2] val2].
        cbn in *.
        specialize (H2 _ _ H6 H5 H0); inv H2.
        left; auto.
      + right; auto.
  Qed.

  Lemma validMsgMap_ValidMsgsExtOut:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall eouts,
        ValidMsgsExtOut impl eouts ->
        ValidMsgsExtOut spec (map mmap eouts).
  Proof.
    intros.
    destruct H0; split.
    - clear -H H0; induction eouts; simpl; [constructor|].
      inv H0; constructor; auto.
      red in H; dest; split.
      + specialize (H a); dest.
        rewrite <-H; auto.
      + apply negb_false_iff.
        rewrite <-toInternal_toExternal_negb.
        apply negb_false_iff in H1.
        rewrite <-toInternal_toExternal_negb in H1.
        specialize (H a); dest.
        rewrite <-H3; auto.
    - destruct H; clear H.
      unfold WellDistrMsgs in *.
      induction eouts; simpl; intros; auto.
      unfold id in *; inv H0; inv H1; dest.
      constructor; auto.
      intro Hx; elim H3; clear -H0 H2 H5 Hx.
      induction eouts; [elim Hx|].
      inv H5; inv Hx; dest.
      + assert (maExternal impl (msgAddrOf a) = true).
        { apply orb_true_intro; right; assumption. }
        assert (maExternal impl (msgAddrOf a0) = true).
        { apply orb_true_intro; right; assumption. }
        destruct a as [[[from1 to1 chn1] tid1] val1].
        destruct a0 as [[[from2 to2 chn2] tid2] val2].
        cbn in *.
        specialize (H2 _ _ H6 H5 H); inv H2.
        left; auto.
      + right; auto.
  Qed.

End SimMap.

(* Lemma validMsgMap_liftTmap_ValidMsgsExtOut: *)
(*   forall impl spec msgP, *)
(*     ValidMsgMap msgP impl spec -> *)
(*     forall (eouts: list TMsg), *)
(*       ValidMsgsExtOut impl eouts -> *)
(*       ValidMsgsExtOut spec (map (liftTmap msgP) eouts). *)
(* Proof. *)
(*   intros. *)
(*   destruct H0; split. *)
(*   - clear -H H0; induction eouts; simpl; [constructor|]. *)
(*     inv H0; constructor; auto. *)
(*     red in H; dest. *)
(*     unfold fromInternal, toInternal, toExternal in *. *)
(*     destruct a as [msg ti]; cbn in *; unfold id in *. *)
(*     split. *)
(*     + specialize (H msg); dest. *)
(*       rewrite <-H; auto. *)
(*     + apply negb_false_iff. *)
(*       rewrite <-internal_external_negb. *)
(*       apply negb_false_iff in H1. *)
(*       rewrite <-internal_external_negb in H1. *)
(*       specialize (H msg); dest. *)
(*       rewrite <-H3; auto. *)

Section RqRsMP.
  Context {MsgT SysT} `{HasMsg MsgT} `{IsSystem SysT}.

  Definition requestsOfMP (sys: SysT) (mp: MessagePool MsgT) :=
    filter (fun msg => fromExternal sys msg) mp.

  (* NOTE: this definition includes external responses. *)
  Definition nonrequestsOfMP (sys: SysT) (mp: MessagePool MsgT) :=
    filter (fun msg => fromInternal sys msg) mp.

  Definition responsesOfMP (sys: SysT) (mp: MessagePool MsgT) :=
    filter (fun msg => toExternal sys msg) mp.

  (* NOTE: this definition includes external requests. *)
  Definition nonresponsesOfMP (sys: SysT) (mp: MessagePool MsgT) :=
    filter (fun msg => toInternal sys msg) mp.

End RqRsMP.

Definition MsgsInSim (msgF: Msg -> Msg) (sim: TState -> TState -> Prop) :=
  forall ioss iorqs imsgs its soss sorqs smsgs sts eins,
    sim {| tst_oss := ioss; tst_orqs := iorqs; tst_msgs := imsgs; tst_tid := its |}
        {| tst_oss := soss; tst_orqs := sorqs; tst_msgs := smsgs; tst_tid := sts |} ->
    sim {| tst_oss := ioss; tst_orqs := iorqs;
           tst_msgs := distributeMsgs (toTMsgsU eins) imsgs; tst_tid := its |}
        {| tst_oss := soss; tst_orqs := sorqs;
           tst_msgs := distributeMsgs (toTMsgsU (map msgF eins)) smsgs; tst_tid := sts |}.

Definition MsgsOutSim {SysT} `{IsSystem SysT} (impl: SysT)
           (msgF: TMsg -> TMsg) (sim: TState -> TState -> Prop) :=
  forall ioss iorqs imsgs its soss sorqs smsgs sts eouts,
    ValidMsgsExtOut impl eouts ->
    sim {| tst_oss := ioss; tst_orqs := iorqs; tst_msgs := imsgs; tst_tid := its |}
        {| tst_oss := soss; tst_orqs := sorqs; tst_msgs := smsgs; tst_tid := sts |} ->
    sim {| tst_oss := ioss; tst_orqs := iorqs;
           tst_msgs := removeMsgs eouts imsgs; tst_tid := its |}
        {| tst_oss := soss; tst_orqs := sorqs;
           tst_msgs := removeMsgs (map msgF eouts) smsgs; tst_tid := sts |}.

(** [SimMP] defines a standard simulation between two [MessagePool]s of 
 * implementation and spec. It's basically 1) rollbacking all live transactions
 * to their original external requests and 2) to keep all external responses.
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
  
  Definition addInactive (iam: TMsg) (rb: MessagePool TMsg) :=
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

  Context {SysT} `{IsSystem SysT}.
  Variable impl: SysT.

  Definition SimMP (imsgs smsgs: MessagePool TMsg) :=
    smsgs = (deinitializeMP (rollback (nonresponsesOfMP impl imsgs)))
              ++ (map (liftTmap msgP) (responsesOfMP impl imsgs)).

  Lemma rollbacked_enqMP_toTMsgU:
    forall msgs emsg rb,
      enqMP (toTMsgU (msgP emsg)) (deinitializeMP (rollbacked rb msgs)) =
      deinitializeMP (rollbacked rb (enqMP (toTMsgU emsg) msgs)).
  Proof.
    induction msgs; simpl; intros.
    - unfold deinitializeMP, enqMP, addInactive.
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

  Theorem ext_outs_SimMP_FirstMP:
    forall ist sst,
      SimMP ist sst ->
      forall imsg,
        toExternal impl imsg = true ->
        FirstMP ist imsg ->
        forall smsg,
          smsg = liftTmap msgP imsg ->
          FirstMP sst smsg.
  Proof.
  Admitted.

  Corollary ext_outs_SimMP_FirstMP_map:
    forall ist sst,
      SimMP ist sst ->
      forall imsgs,
        Forall (fun imsg => toExternal impl imsg = true) imsgs ->
        Forall (FirstMP ist) imsgs ->
        forall smsgs,
          smsgs = map (liftTmap msgP) imsgs ->
          Forall (FirstMP sst) smsgs.
  Proof.
    induction imsgs; simpl; intros; subst; [constructor|].
    inv H1; inv H2; constructor; auto.
    eapply ext_outs_SimMP_FirstMP; eauto.
  Qed.

  Lemma SimMP_ext_msg_ins:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall eins,
        SimMP (distributeMsgs (toTMsgsU eins) imsgs)
              (distributeMsgs (toTMsgsU (map msgP eins)) smsgs).
  Proof.
  Admitted.

  Lemma SimMP_ext_msg_outs:
    forall imsgs smsgs,
      SimMP imsgs smsgs ->
      forall eouts,
        ValidMsgsExtOut impl eouts ->
        SimMP (removeMsgs eouts imsgs)
              (removeMsgs (map (liftTmap msgP) eouts) smsgs).
  Proof.
  Admitted.

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

  (* Lemma SimMP_responses_back_ext_out: *)
  (*   forall imsgs smsgs, *)
  (*     SimMP imsgs smsgs -> *)
  (*     forall origRq ts rss, *)
  (*       Forall (fun tmsg => *)
  (*                 (tmsg_info tmsg) >>=[False] (fun tinfo => tinfo = buildTInfo ts [origRq])) *)
  (*              rss -> *)
  (*       ForallMP (fun tmsg => *)
  (*                   (tmsg_info tmsg) >>=[True] (fun tinfo => tinfo_tid tinfo <> ts)) *)
  (*                (removeMsgs rss imsgs) -> *)
  (*       SimMP (removeMsgs rss imsgs) *)
  (*             (removeMP (toTMsgU (msgP origRq)) smsgs). *)
  (* Proof. *)

  (* Corollary SimMP_response_back_ext_out: *)
  (*   forall imsgs smsgs, *)
  (*     SimMP imsgs smsgs -> *)
  (*     forall origRq ts rs, *)
  (*       Forall (fun tmsg => *)
  (*                 (tmsg_info tmsg) >>=[False] (fun tinfo => tinfo = buildTInfo ts [origRq])) *)
  (*              [rs] -> *)
  (*       ForallMP (fun tmsg => *)
  (*                   (tmsg_info tmsg) >>=[True] (fun tinfo => tinfo_tid tinfo <> ts)) *)
  (*                (removeMP rs imsgs) -> *)
  (*       SimMP (removeMP rs imsgs) *)
  (*             (removeMP (toTMsgU (msgP origRq)) smsgs). *)
  (* Proof. *)
  (*   intros; eapply SimMP_responses_back_ext_out in H0; eauto. *)
  (*   simpl in H0; assumption. *)
  (* Qed. *)
  
End SimMP.

Definition ImpliesSimMP {SysT} `{IsSystem SysT} (impl: SysT)
           (msgP: Msg -> Msg) (sim: TState -> TState -> Prop) :=
  forall ist sst,
    sim ist sst ->
    SimMP msgP impl (tst_msgs ist) (tst_msgs sst).

Section NoRules.

  Lemma steps_simulation_NoExtOuts_no_rules:
    forall (sim: TState -> TState -> Prop) mamap impl spec,
      ValidMsgMap mamap impl spec ->
      MsgsInSim (liftMmap mamap) sim ->
      MsgsOutSim impl (liftTmap (liftMmap mamap)) sim ->
      sys_rules impl = nil ->
      forall ist1 sst1,
        sim ist1 sst1 ->
        NoExtOuts impl ist1 ->
        forall ihst ist2,
          steps step_t impl ist1 ihst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps step_t spec sst1 shst sst2 /\
            map (liftLmap (liftMmap mamap)) (behaviorOf impl ihst) =
            behaviorOf spec shst /\
            sim ist2 sst2.
  Proof.
    induction 7; simpl; intros;
      [do 2 eexists; repeat split; [constructor|reflexivity|assumption]|].

    specialize (IHsteps H3 H4); dest.
    inv H6.
    - do 2 eexists; repeat split; eauto.
    - destruct x as [noss norqs nmsgs ntid].
      do 2 eexists; repeat split.
      + eapply StepsCons.
        * eassumption.
        * eapply StIns; try reflexivity.
          { instantiate (1:= map (liftMmap mamap) eins).
            destruct eins; [exfalso; auto|discriminate].
          }
          { eapply validMsgMap_ValidMsgsExtIn; eauto. }
      + simpl; rewrite <-H8; repeat f_equal.
        clear; induction eins; simpl; auto.
        rewrite IHeins; reflexivity.
      + apply H0; auto.
    - exfalso.
      eapply steps_t_no_rules_NoExtOuts in H5; eauto.
      hnf in H5; simpl in H5.
      destruct eouts as [|eout eouts]; auto.
      inv H11.
      apply FirstMP_InMP in H14.
      eapply Forall_forall in H5; eauto.
      destruct H12; inv H6; dest.
      congruence.
    - exfalso.
      rewrite H2 in H17; elim H17.
  Qed.

  Corollary refines_no_rules:
    forall (sim: TState -> TState -> Prop) mamap impl spec,
      sim (initsOf impl) (initsOf spec) ->
      ValidMsgMap mamap impl spec ->
      MsgsInSim (liftMmap mamap) sim ->
      MsgsOutSim impl (liftTmap (liftMmap mamap)) sim ->
      sys_rules impl = nil ->
      (steps step_t) # (steps step_t) |-- impl <=[ liftLmap (liftMmap mamap) ] spec.
  Proof.
    unfold Refines; intros.
    inv H4.
    eapply steps_simulation_NoExtOuts_no_rules in H5; eauto.
    - dest; econstructor; eauto.
    - hnf; cbn; constructor.
  Qed.

  Lemma steps_simulation_BlockedInv_SimMP_no_rules:
    forall (sim: TState -> TState -> Prop) mamap impl spec,
      ValidMsgMap mamap impl spec ->
      MsgsInSim (liftMmap mamap) sim ->
      MsgsOutSim impl (liftTmap (liftMmap mamap)) sim ->
      ImpliesSimMP impl (liftMmap mamap) sim ->
      sys_rules impl = nil ->
      forall ist1 sst1,
        sim ist1 sst1 ->
        forall ihst ist2,
          steps step_t impl ist1 ihst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps step_t spec sst1 shst sst2 /\
            map (liftLmap (liftMmap mamap)) (behaviorOf impl ihst) =
            behaviorOf spec shst /\
            sim ist2 sst2.
  Proof.
    induction 7; simpl; intros;
      [do 2 eexists; repeat split; [constructor|reflexivity|assumption]|].

    specialize (IHsteps H4); dest.
    inv H6.
    - do 2 eexists; repeat split; eauto.
    - destruct x as [noss norqs nmsgs ntid].
      do 2 eexists; repeat split.
      + eapply StepsCons.
        * eassumption.
        * eapply StIns; try reflexivity.
          { instantiate (1:= map (liftMmap mamap) eins).
            destruct eins; [exfalso; auto|discriminate].
          }
          { eapply validMsgMap_ValidMsgsExtIn; eauto. }
      + simpl; rewrite <-H8; repeat f_equal.
        clear; induction eins; simpl; auto.
        rewrite IHeins; reflexivity.
      + apply H0; auto.
    - destruct x as [noss norqs nmsgs ntid].
      do 2 eexists; repeat split.
      + eapply StepsCons.
        * eassumption.
        * eapply StOuts; try reflexivity.
          { instantiate (1:= map (liftTmap (liftMmap mamap)) eouts).
            destruct eouts; [exfalso; auto|discriminate].
          }
          { specialize (H2 _ _ H9); simpl in H2.
            eapply ext_outs_SimMP_FirstMP_map; try eassumption; try reflexivity.
            destruct H12; clear -H6; induction eouts; simpl; auto.
            inv H6; constructor; auto.
            dest; auto.
          }
          { admit. }
      + simpl; rewrite <-H8; repeat f_equal.
        clear; induction eouts; simpl; auto.
        rewrite IHeouts; reflexivity.
      + apply H1; auto.
    - exfalso.
      rewrite H3 in H17; elim H17.
  Admitted.

End NoRules.

