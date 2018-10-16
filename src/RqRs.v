Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts.
Require Import QuasiSeq Reduction.
Require Import Topology TopologyFacts.

Require Import Omega.

Set Implicit Arguments.

Section TreeTopo.
  Variable (gtr: GTree).
  Local Notation topo := (topoOfT gtr).

  Definition TreeTopoRule (rule: Rule) :=
    forall post porq ins nost norq outs,
      rule_trs rule post porq ins = (nost, norq, outs) ->
      (forall min,
          In min ins ->
          exists mfrom, In (createEdge mfrom (idOf min) (rule_oidx rule)) (dg_es topo)) /\
      (forall mout,
          In mout outs ->
          exists mto, In (createEdge (rule_oidx rule) (idOf mout) mto) (dg_es topo)).

  Definition TreeTopoSys (sys: System) :=
    Forall TreeTopoRule (sys_rules sys).

End TreeTopo.

Section PartialBlocking.
  Variable (gtr: GTree).

  Fixpoint getDownRq (oidx: IdxT) (orq: ORq Msg) :=
    match orq with
    | nil => None
    | ri :: orq' =>
      if isParent gtr oidx (rqh_from ri)
      then Some ri
      else getDownRq oidx orq'
    end.

  Fixpoint getUpRq (oidx: IdxT) (orq: ORq Msg) :=
    match orq with
    | nil => None
    | ri :: orq' =>
      if isParent gtr (rqh_from ri) oidx
      then Some ri
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

Section RqRs.
  Variable (RqRsT: Type).

  Definition RqRsDec := Rule -> RqRsT.
  Definition RqRsSemiDisj := RqRsT -> RqRsT -> Prop.

  Definition RNonExecutable (rule1 rule2: Rule) :=
    forall post porq ins1 nost norq outs ins2,
      rule_precond rule1 post porq ins1 ->
      rule_trs rule1 post porq ins1 = (nost, norq, outs) ->
      ~ rule_precond rule2 nost norq ins2.

  (** TODO: need to check whether the disjointness between [ins1] and [ins2] 
   * (or [outs1] and [outs2]) is required. *)
  Definition RCommutable (rule1 rule2: Rule) :=
    forall post1 porq1 ins1 nost1 norq1 outs1 ins2,
      rule_precond rule1 post1 porq1 ins1 ->
      rule_trs rule1 post1 porq1 ins1 = (nost1, norq1, outs1) ->
      rule_precond rule2 nost1 norq1 ins2 ->
      (* 1) Precondition of [rule2] holds if the one of [rule1] holds. *)
      rule_precond rule2 post1 porq1 ins2 /\
      forall nost2 norq2 outs2,
        rule_trs rule2 post1 porq1 ins2 = (nost2, norq2, outs2) ->
        (* 2) Precondition of [rule1] holds after a transition by [rule2]. *)
        rule_precond rule1 nost2 norq2 ins1 /\
        (* 3) Transitions by [rule1; rule2] and [rule2; rule1] are same. *)
        fst (rule_trs rule2 nost1 norq1 ins2) =
        fst (rule_trs rule1 nost2 norq2 ins1).

  Variables (rrdec: RqRsDec) (rrsd: RqRsSemiDisj).

  Definition RqRsSemiDisjComm (sys: System) :=
    forall rule1 rule2,
      In rule1 (sys_rules sys) -> In rule2 (sys_rules sys) ->
      rule_oidx rule1 = rule_oidx rule2 ->
      rrsd (rrdec rule1) (rrdec rule2) ->
      RCommutable rule1 rule2.

  Definition getRqRsLabel {MsgT} (lbl: RLabel MsgT): option (IdxT * RqRsT) :=
    match lbl with
    | RlblInt rule _ _ => Some (rule_oidx rule, rrdec rule)
    | _ => None
    end.
  
  Fixpoint getRqRsHistory (hst: MHistory): list (IdxT * RqRsT) :=
    match hst with
    | nil => nil
    | lbl :: hst' => (getRqRsLabel lbl) ::> (getRqRsHistory hst')
    end.

  Definition RqRsSemiDisjHistories (hst1 hst2: MHistory) :=
    forall irr1 irr2,
      In irr1 (getRqRsHistory hst1) ->
      In irr2 (getRqRsHistory hst2) ->
      fst irr1 = fst irr2 ->
      rrsd (snd irr1) (snd irr2).

  Definition RqRsContSemiDisj (sys: System) :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      RqRsSemiDisjHistories hst1 hst2.

  Definition RqRsLRComm (sys: System) :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      forall lhst rhst,
        RqRsSemiDisjHistories hst1 lhst ->
        RqRsSemiDisjHistories rhst hst2 ->
        Reducible sys (lhst ++ rhst) (rhst ++ lhst).

  Definition RqRsLOrR (sys: System) :=
    forall st1 st2 hst1 hst2 hsts,
      steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
      Forall (STransactional msg_dec) hsts ->
      Separated (hsts ++ [hst1]) ->
      Separated (hst2 :: hsts) ->
      Forall (fun hst => RqRsSemiDisjHistories hst1 hst \/
                         RqRsSemiDisjHistories hst hst2) hsts.
  
  Definition RqRsSys (sys: System) :=
    RqRsSemiDisjComm sys /\
    RqRsContSemiDisj sys /\
    RqRsLRComm sys /\
    RqRsLOrR sys.

End RqRs.

Section RqRsSerial.
  Variables (gtr: GTree)
            (RqRsT: Type) (rrdec: RqRsDec RqRsT)
            (rrsd: RqRsSemiDisj RqRsT)
            (sys: System).

  Hypotheses (Htr: TreeTopoSys gtr sys)
             (Hpb: PartialBlockingSys gtr sys)
             (Hrr: RqRsSys rrdec rrsd sys).

  Lemma rqrs_well_interleaved_push:
    WellInterleavedPush sys.
  Proof.
    red; intros.
    exists (RqRsSemiDisjHistories rrdec rrsd hst1).
    exists (fun hst => RqRsSemiDisjHistories rrdec rrsd hst hst2).

    assert (ValidContinuous sys hst1 hst2).
    { split; auto.
      simpl in H; rewrite concat_app in H.
      simpl in H; rewrite app_nil_r in H.
      eauto.
    }

    split; [|split; [|split]];
      try (eapply Hrr; eauto; fail).
  Qed.

  Theorem immrqrs_pb_serializable:
    SerializableSys sys.
  Proof.
    apply well_interleaved_serializable.
    apply well_interleaved_push_ok.
    apply rqrs_well_interleaved_push.
  Qed.

End RqRsSerial.

