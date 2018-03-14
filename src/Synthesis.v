Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics SemFacts.
Require Import StepDet Serial SerialFacts Invariant TrsSim.

Set Implicit Arguments.

Section SynthOk.

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
    R (initsOf s) (initsOf spec) /\
    ginv (initsOf s) /\
    (TrsSimulates R ginv p s spec /\ InvStep s step_det ginv) /\
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
                               initsOf (StateT:= TState) s' =
                               initsOf (StateT:= TState) s)
               (HsynSerial:
                  forall s, SerializableSys s ->
                            forall s', syn s s' -> SerializableSys s')
               (HsynSim:
                  forall s, TrsSimulates R ginv p s spec ->
                            forall s', syn s s' -> TrsSimulates R ginv p s' spec)
               (HsynInv:
                  forall s, InvStep s step_det ginv ->
                            forall s', syn s s' -> InvStep s' step_det ginv).

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

End SynthOk.

Section SynRqRsImm.
  Variables (trsIdx: IdxT)
            (this: IdxT).
            (* (trsLocker: TrsHelper -> Prop). *)

  Definition rqChn: IdxT := 0.
  Definition rsChn: IdxT := 1.
  Definition numChns := S rsChn.

  Definition SingleRqPostcondSt (mout: OState -> Value -> OState -> Prop): PostcondSt :=
    fun pre ins post =>
      match ins with
      | {| msg_value := val |} :: nil => mout pre val post
      | _ => False
      end.

  Definition SingleRqMsgOuts (mout: OState -> Value -> list Msg): MsgOuts :=
    fun pre ins =>
      match ins with
      | {| msg_value := val |} :: nil => mout pre val
      | _ => nil
      end.

  Definition msgValOut (val: Value) (tochn: IdxT * IdxT) :=
    {| msg_id := buildMsgId trsIdx this (fst tochn) (snd tochn);
       msg_value := val
    |}.

End SynRqRsImm.

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
    
    Definition makeRuleExternal (rule: Rule): Rule :=
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

  End MakeExternal.

  Section MakePreCondDisj.
    Variable (prec: Precond).

    Definition makePreCondDisj (rule: Rule): Rule :=
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

  End MakePreCondDisj.

End Manipulation.

