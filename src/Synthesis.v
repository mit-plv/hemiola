Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics SemFacts.
Require Import StepDet Serial SerialFacts TrsInv TrsSim.

Set Implicit Arguments.

Section SimP.

  (** User inputs *)
  Variables
    (impl0 spec: System)
    (R: TState -> TState -> Prop)
    (ginv: TState -> Prop)
    (p: Label -> Label).

  (* NOTE: the order here matters. [Rule]s are synthesized during the simulation
   * proof. Invariants are proven after all [Rule]s are synthesized.
   *)
  Definition SynthOk (s: System) :=
    R (getStateInit s) (getStateInit spec) /\
    ginv (getStateInit s) /\
    (TrsSimulates R ginv p s spec /\ TrsInv s ginv) /\
    SerializableSys s.

  Hypothesis (Hinit_ok: SynthOk impl0).

  Section SynthesisStep.

    Definition SynT := System -> System -> Prop.
    Variable syn: SynT.

    (** The synthesizer [syn] should "preserve" three conditions:
     * 1) initial state
     * 2) serializability
     * 3) simulation on sequential semantics
     * 4) global invariants
     *)
    Hypotheses (HsynInit:
                  forall s s', syn s s' ->
                               getStateInit (StateT:= TState) s' =
                               getStateInit (StateT:= TState) s)
               (HsynSerial:
                  forall s, SerializableSys s ->
                            forall s', syn s s' -> SerializableSys s')
               (HsynSim:
                  forall s, TrsSimulates R ginv p s spec ->
                            forall s', syn s s' -> TrsSimulates R ginv p s' spec)
               (HsynInv:
                  forall s, TrsInv s ginv ->
                            forall s', syn s s' -> TrsInv s' ginv).

    Lemma synthOk_refinement:
      forall s, SynthOk s -> steps_det # steps_det |-- s ⊑[p] spec.
    Proof.
      unfold SynthOk; intros; dest.
      eapply refines_trans.
      - apply serializable_seqSteps_refines in H2.
        eassumption.
      - eapply sequential_simulation_implies_refinement; eauto.
    Qed.

    Lemma synthOk_preserved:
      forall s s', SynthOk s -> syn s s' -> SynthOk s'.
    Proof.
      unfold SynthOk; intros; dest.
      repeat split; eauto.
      - erewrite HsynInit; eauto.
      - erewrite HsynInit; eauto.
    Qed.

  End SynthesisStep.

End SimP.

Section SimMP.
  Variable msgP: Msg -> Msg.

  (* Assume [rb] is already ordered in terms of [tinfo_tid]. *)
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

  (* [rollback] basically rolls back all active messages (executing 
   * transactions) in a given [MessagePool].
   *)
  Fixpoint rollbacked (rb mp: MessagePool TMsg) :=
    match mp with
    | nil => rb
    | tmsg :: mp' =>
      match tmsg_info tmsg with
      | Some tinfo => rollbacked (addActive (tmsg_msg tmsg) tinfo rb) mp'
      | None => rollbacked (addInactive tmsg rb) mp'
      end
    end.

  Definition rollback (mp: MessagePool TMsg) := rollbacked nil mp.

  Definition deinitialize (mp: MessagePool TMsg) :=
    map (fun tmsg =>
           toTMsgU (msgP (match tmsg_info tmsg with
                          | Some tinfo => tinfo_rqin tinfo
                          | None => tmsg_msg tmsg
                          end))) mp.
  
  Definition SimMP (imsgs smsgs: MessagePool TMsg) :=
    smsgs = deinitialize (rollback imsgs).

End SimMP.

Section TrsLock.

  Definition alwaysLock (trsh: TrsHelper) := trsh = [].

End TrsLock.

Section SynRqRsImm.
  Variables (trsIdx: IdxT)
            (this: IdxT)
            (trsLocker: TrsHelper -> Prop).

  Definition liftTrsLocker (os: OState): Prop := trsLocker (ost_tst os).

  Definition rqChn: IdxT := 0.
  Definition rsChn: IdxT := 1.

  Definition msgValOut (val: Value) (tochn: IdxT * IdxT) :=
    {| msg_id := buildMsgId trsIdx this (fst tochn) (snd tochn);
       msg_value := val
    |}.

  Section Immediate.

    Definition synImm (prec: RPrecond) (rqFrom: IdxT) (postc: PostcondSt)
               (valOut: Value -> StateT -> Value) :=
      {| rule_mid := buildMsgId trsIdx rqFrom this rqChn;
         rule_precond := prec;
         rule_postcond :=
           rpostOf postc
                   (fun pre val =>
                      msgValOut (valOut val (ost_st pre)) (rqFrom, rsChn) :: nil)
      |}.

  End Immediate.

  Section RequestFwd.
    Variables (rqFrom: IdxT) (fwds: list IdxT).

    Definition synRqOuts (tochns: list (IdxT * IdxT)) (val: Value) :=
      map (msgValOut val) tochns.

    Definition synRqPostcond (pre: OState) (val: Value) (post: OState) :=
      post = {| ost_st := ost_st pre;
                ost_tst := (ost_tst pre)
                           +[ trsIdx <-
                              {| tst_rqval := val; (* store the request value *)
                                 tst_rss := map (fun idx => (idx, None)) fwds |}]
             |}.

    Definition synRq (prec: RPrecond) :=
      {| rule_mid := buildMsgId trsIdx rqFrom this rqChn;
         rule_precond := fun pre val => prec pre val /\ liftTrsLocker pre;
         rule_postcond :=
           rpostOf synRqPostcond
                   (fun _ val => synRqOuts (map (fun to => (to, rqChn)) fwds) val)
      |}.

  End RequestFwd.

  (** FIXME: preconditions in [synRsSingle] and [synRs] are currently just [T],
   * which is incorrect. For the serializability proof, we need correct ones.
   *)
  Section ResponseBack.
    Variables (rsFrom rsBack: IdxT).

    Fixpoint markResponded (rss: list (IdxT * option Value)) (rsVal: Value) :=
      match rss with
      | nil => nil
      | (idx, ov) :: rss' =>
        if idx ==n rsFrom
        then (idx, Some rsVal) :: rss'
        else (idx, ov) :: (markResponded rss' rsVal)
      end.

    Definition markRespondedTrs (trsh: TrsHelperUnit) (rsVal: Value) :=
      {| tst_rqval := tst_rqval trsh;
         tst_rss := markResponded (tst_rss trsh) rsVal |}.

    Definition Responded (pre: OState) (rsVal: Value) (post: OState) :=
      (ost_tst pre)@[trsIdx] >>=[False]
      (fun preth =>
         (ost_tst post)@[trsIdx] >>=[False]
         (fun postth => postth = markRespondedTrs preth rsVal)).

    Definition allResponded (fwds: list (IdxT * option Value)) :=
      forallb (fun ib => match snd ib with
                         | Some _ => true
                         | _ => false
                         end) fwds.

    (* NOTE: prestate already contains the request value and all the responded
     * values in [TrsHelperUnit], thus we don't need [Value] to define
     * [postcond].
     *)
    Definition WhenAllResponded (postcond: OState -> OState -> Prop)
               (pre: OState) (post: OState) :=
      (ost_tst pre)@[trsIdx] >>=[False]
      (fun trsh =>
         if allResponded (tst_rss trsh)
         then postcond pre post /\
              ost_tst post = M.remove trsIdx (ost_tst pre)
         else True).

    Fixpoint getFwdValue (vals: list (IdxT * option Value)) :=
      match vals with
      | nil => VUnit
      | (_, Some v) :: vals' =>
        match v with
        | VUnit => getFwdValue vals'
        | _ => v
        end
      | (_, None) :: vals' => getFwdValue vals'
      end.

    Definition rsFwdValue (post: OState) :=
      (ost_tst post)@[trsIdx] >>=[VUnit]
      (fun trsh => getFwdValue (tst_rss trsh)).
         
    Definition synRsPostcond (postcond: OState -> OState -> Prop)
               (pre: OState) (val: Value) (post: OState) :=
      exists allResp,
        Responded pre val allResp /\
        WhenAllResponded postcond allResp post.

    Definition synRsOuts (rsOut: StateT -> TrsHelperUnit -> Value) :=
      fun st val =>
        (ost_tst st)@[trsIdx] >>=[nil]
        (fun trsh =>
           let rss := markResponded (tst_rss trsh) val in
           if allResponded rss
           then {| msg_id := buildMsgId trsIdx this rsBack rsChn;
                   msg_value := rsOut (ost_st st) (markRespondedTrs trsh val)
                |} :: nil
           else nil).

    (* NOTE: [postcond] is a desired postcondition when assuming 
     * the transaction is atomic.
     *)
    Definition synRs (postcond: OState -> OState -> Prop)
               (rsOut: StateT -> TrsHelperUnit -> Value) :=
      {| rule_mid := buildMsgId trsIdx rsFrom this rsChn;
         rule_precond := ⊤;
         rule_postcond := rpostOf (synRsPostcond postcond) (synRsOuts rsOut) |}.

  End ResponseBack.

  Section AddRules.

    Definition buildRawObjs (oobs: list Object): list Object :=
      map (fun obj => {| obj_idx := obj_idx obj;
                         obj_state_init := obj_state_init obj;
                         obj_rules := nil |}) oobs.

    Definition buildRawSys (osys: System) :=
      buildRawObjs osys.

    Definition addRulesO (rules: list Rule) (obj: Object) :=
      {| obj_idx := obj_idx obj;
         obj_state_init := obj_state_init obj;
         obj_rules :=
           (filter (fun rule =>
                      if mid_to (rule_mid rule) ==n obj_idx obj
                      then true else false) rules)
             ++ obj_rules obj |}.

    Fixpoint addRules (rules: list Rule) (objs: list Object) :=
      match objs with
      | nil => nil
      | obj :: obs' =>
        (addRulesO rules obj) :: (addRules rules obs')
      end.

    Definition addRulesSys (rules: list Rule) (sys: System) :=
      addRules rules sys.
    
  End AddRules.

  Definition idxInter (li1 li2: list IdxT): list IdxT :=
    filter (fun idx => if idx ?<n li2 then true else false) li1.
  Definition idxSubtract (li1 li2: list IdxT): list IdxT :=
    filter (fun idx => if idx ?<n li2 then false else true) li1.
  
End SynRqRsImm.

Section Manipulation.

  Section MakeExternal.
    Variables (targetIdx diffIdx: IdxT)
              (Hdiff: targetIdx <> diffIdx).
    
    Definition makeIdxExternal (idx: IdxT): IdxT :=
      if idx ==n targetIdx
      then diffIdx 
      else idx.
    
    Definition makeMsgIdExternal (mid: MsgId): MsgId :=
      buildMsgId (mid_tid mid) (mid_from mid) (makeIdxExternal (mid_to mid)) (mid_chn mid).
    
    Definition makeRuleExternal (rule: Rule): Rule :=
      {| rule_mid := makeMsgIdExternal (rule_mid rule);
         rule_precond := rule_precond rule;
         rule_postcond := rule_postcond rule
      |}.

    Lemma makeRuleExternal_rule_in:
      forall rule rules1 rules2,
        mid_to (rule_mid rule) = targetIdx ->
        In rule (rules1 ++ map makeRuleExternal rules2) ->
        In rule rules1.
    Proof.
      intros.
      apply in_app_or in H0; destruct H0; auto.
      exfalso; clear -H H0 Hdiff.
      induction rules2; [auto|].
      destruct H0; auto.
      subst rule.
      cbn in H; unfold makeIdxExternal in H.
      find_if_inside; auto.
    Qed.

    Lemma addRulesO_makeRuleExternal:
      forall rs1 rs2 obj,
        obj_idx obj = targetIdx ->
        addRulesO (rs1 ++ map makeRuleExternal rs2) obj =
        addRulesO rs1 obj.
    Proof.
    Admitted.

  End MakeExternal.

  Section MakePreCondDisj.
    Variable (prec: Precond).

    Definition makePreCondDisj (rule: Rule): Rule :=
      {| rule_mid := rule_mid rule;
         rule_precond := fun pre val => ~ (prec pre val) /\ rule_precond rule pre val;
         rule_postcond := rule_postcond rule
      |}.

    Lemma makePreCondDisj_rule_in:
      forall rule pre val,
        rule_precond rule pre val ->
        prec pre val ->
        forall rules1 rules2,
          In rule (rules1 ++ map makePreCondDisj rules2) ->
          In rule rules1.
    Proof.
      intros.
      apply in_app_or in H1; destruct H1; auto.
      exfalso; clear -H H0 H1.
      induction rules2; [auto|].
      destruct H1; auto.
      subst; cbn in H; destruct H; auto.
    Qed.

    Lemma addRulesO_makePreCondDisj:
      forall rs1 rs2 obj rule pre val,
        rule_precond rule pre val ->
        prec pre val ->
        In rule (obj_rules (addRulesO (rs1 ++ map makePreCondDisj rs2) obj)) ->
        In rule (obj_rules (addRulesO rs1 obj)).
    Proof.
    Admitted.

  End MakePreCondDisj.

End Manipulation.

