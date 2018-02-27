Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics SemFacts.
Require Import StepDet Serial SerialFacts TrsInv TrsSim.

Set Implicit Arguments.

Section SimP.

  (** User inputs *)
  Variables
    (impl0 spec: System OrdOState)
    (R: TState -> TState -> Prop)
    (ginv: TState -> Prop)
    (p: Label -> Label).

  (* NOTE: the order here matters. [Rule]s are synthesized during the simulation
   * proof. Invariants are proven after all [Rule]s are synthesized.
   *)
  Definition SynthOk (s: System OrdOState) :=
    R (getStateInit s) (getStateInit spec) /\
    ginv (getStateInit s) /\
    (TrsSimulates R ginv p s spec /\ TrsInv s ginv) /\
    SerializableSys s.

  Hypothesis (Hinit_ok: SynthOk impl0).

  Section SynthesisStep.

    Definition SynT := System OrdOState -> System OrdOState -> Prop.
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

End SimMP.

(* Section TrsLock. *)

(*   Definition alwaysLock (trsh: TrsHelper) := trsh = []. *)

(* End TrsLock. *)

Section SynRqRsImm.
  Variables (trsIdx: IdxT)
            (this: IdxT).
            (* (trsLocker: TrsHelper -> Prop). *)

  (* Definition liftTrsLocker (os: OState OrdOState): Prop := trsLocker (ost_tst os). *)

  Definition rqChn: IdxT := 0.
  Definition rsChn: IdxT := 1.

  Definition SingleRqPostcondSt (mout: OrdOState -> Value -> OrdOState -> Prop)
    : PostcondSt OrdOState :=
    fun pre ins post =>
      match ins with
      | {| msg_value := val |} :: nil => mout pre val post
      | _ => False
      end.

  Definition SingleRqMsgOuts (mout: OrdOState -> Value -> list Msg): MsgOuts OrdOState :=
    fun pre ins =>
      match ins with
      | {| msg_value := val |} :: nil => mout pre val
      | _ => nil
      end.

  Definition msgValOut (val: Value) (tochn: IdxT * IdxT) :=
    {| msg_id := buildMsgId trsIdx this (fst tochn) (snd tochn);
       msg_value := val
    |}.

(*   Section Immediate. *)

(*     Definition synImm (prec: RPrecond) (rqFrom: IdxT) (postc: PostcondSt) *)
(*                (valOut: Value -> StateT -> Value) := *)
(*       {| rule_mids := buildMsgId trsIdx rqFrom this rqChn :: nil; *)
(*          rule_precond := prec; *)
(*          rule_postcond := *)
(*            rpostOf postc *)
(*                    (SingleRqMsgOuts *)
(*                       (fun pre val => *)
(*                          msgValOut (valOut val (ost_st pre)) (rqFrom, rsChn) :: nil)) *)
(*       |}. *)

(*   End Immediate. *)

(*   Section RequestFwd. *)
(*     Variables (rqFrom: IdxT) (fwds: list IdxT). *)

(*     Definition synRqOuts (tochns: list (IdxT * IdxT)) (val: Value) := *)
(*       map (msgValOut val) tochns. *)

(*     Definition synRqPostcond (pre: OState) (val: Value) (post: OState) := *)
(*       post = {| ost_st := ost_st pre; *)
(*                 ost_tst := (ost_tst pre) *)
(*                            +[ trsIdx <- *)
(*                               {| (* store the request value *) *)
(*                                  tst_rqval := val |}] *)
(*              |}. *)

(*     Definition synRq (prec: RPrecond) := *)
(*       {| rule_mids := buildMsgId trsIdx rqFrom this rqChn :: nil; *)
(*          rule_precond := fun pre val => prec pre val /\ liftTrsLocker pre; *)
(*          rule_postcond := *)
(*            rpostOf (SingleRqPostcondSt synRqPostcond) *)
(*                    (SingleRqMsgOuts *)
(*                       (fun _ val => synRqOuts (map (fun to => (to, rqChn)) fwds) val)) *)
(*       |}. *)

(*   End RequestFwd. *)

(*   (** FIXME: preconditions in [synRsSingle] and [synRs] are currently just [⊤], *)
(*    * which is incorrect. For the serializability proof, we need correct ones. *)
(*    *) *)
(*   Section ResponseBack. *)
(*     Variables (rsFroms: list IdxT) *)
(*               (rsBack: IdxT). *)

(*     Definition RsOut := StateT -> list Msg -> Value (* request value *) -> Value. *)
    
(*     Definition synRsOuts (rsout: RsOut): MsgOuts := *)
(*       fun pre ins => *)
(*         (ost_tst pre)@[trsIdx] >>=[nil] *)
(*         (fun trsh => {| msg_id := buildMsgId trsIdx this rsBack rsChn; *)
(*                         msg_value := rsout (ost_st pre) ins (tst_rqval trsh) |} :: nil). *)

(*     Definition synRs (postc: PostcondSt) (rsout: RsOut) := *)
(*       {| rule_mids := map (fun rsFrom => buildMsgId trsIdx rsFrom this rsChn) rsFroms; *)
(*          rule_precond := ⊤; *)
(*          rule_postcond := rpostOf postc (synRsOuts rsout) |}. *)

(*   End ResponseBack. *)
  
End SynRqRsImm.

Section AddRules.

  Definition buildRawObjs (oobs: list (Object OrdOState)): list (Object OrdOState) :=
    map (fun obj => {| obj_idx := obj_idx obj;
                       obj_state_init := obj_state_init obj;
                       obj_rules := nil |}) oobs.

  Definition buildRawSys (osys: System OrdOState) :=
    buildRawObjs osys.

  Definition addRulesO (rules: list (Rule OrdOState)) (obj: Object OrdOState) :=
    {| obj_idx := obj_idx obj;
       obj_state_init := obj_state_init obj;
       obj_rules :=
         (filter (fun rule =>
                    forallb (fun mid =>
                               if mid_to mid ==n obj_idx obj
                               then true else false) (rule_mids rule)) rules)
           ++ obj_rules obj |}.

  Fixpoint addRules (rules: list (Rule OrdOState)) (objs: list (Object OrdOState)) :=
    match objs with
    | nil => nil
    | obj :: obs' =>
      (addRulesO rules obj) :: (addRules rules obs')
    end.

  Definition addRulesSys (rules: list (Rule OrdOState)) (sys: System OrdOState) :=
    addRules rules sys.
  
End AddRules.

Definition idxInter (li1 li2: list IdxT): list IdxT :=
  filter (fun idx => if idx ?<n li2 then true else false) li1.
Definition idxSubtract (li1 li2: list IdxT): list IdxT :=
  filter (fun idx => if idx ?<n li2 then false else true) li1.

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
    
    Definition makeRuleExternal (rule: Rule OrdOState): Rule OrdOState :=
      {| rule_mids := map makeMsgIdExternal (rule_mids rule);
         rule_precond := rule_precond rule;
         rule_postcond := rule_postcond rule
      |}.

    Lemma makeRuleExternal_rule_in:
      forall rule rules1 rules2,
        rule_mids rule <> nil ->
        Forall (fun mid => mid_to mid = targetIdx) (rule_mids rule) ->
        In rule (rules1 ++ map makeRuleExternal rules2) ->
        In rule rules1.
    Proof.
      intros.
      apply in_app_or in H1; destruct H1; auto.
      exfalso; clear -H H0 H1 Hdiff.
      induction rules2; [auto|].
      destruct H1; auto.
      subst rule.
      cbn in H0; unfold makeIdxExternal in H0.
      destruct a as [rmids rprec rpost]; simpl in *.
      destruct rmids; [elim H; reflexivity|].
      inv H0.
      unfold makeMsgIdExternal, makeIdxExternal in *.
      cbn in *.
      find_if_inside; auto.
    Qed.

    Lemma addRulesO_makeRuleExternal:
      forall (rs1 rs2: list (Rule OrdOState)) obj,
        obj_idx obj = targetIdx ->
        addRulesO (rs1 ++ map makeRuleExternal rs2) obj =
        addRulesO rs1 obj.
    Proof.
    Admitted.

  End MakeExternal.

  Section MakePreCondDisj.
    Variable (prec: Precond OrdOState).

    Definition makePreCondDisj (rule: Rule OrdOState): Rule OrdOState :=
      {| rule_mids := rule_mids rule;
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

