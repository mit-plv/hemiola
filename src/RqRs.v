Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts.
Require Import QuasiSeq Reduction Denotation.
Require Import Topology TopologyFacts.

Require Import Omega.

Set Implicit Arguments.

Inductive RqRsTrs :=
| ImmTrs | RqUpTrs | RqDownTrs | RsTrs.

Section RqRsRule.
  Variable (gtr: GTree).

  Local Notation topo := (topoOfT gtr).

  (* TODO: may need to specify the type of handling messages, whether they are
   * requests or responses. *)
  
  Definition ImmRule (rule: Rule) :=
    exists rqoidx rqmidx rsmidx,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_trs rule post porq ins = (nost, norq, outs) ->
          idsOf outs = [rsmidx]) /\
      In (createEdge rqoidx rqmidx (rule_oidx rule)) (dg_es topo) /\
      In (createEdge (rule_oidx rule) rsmidx rqoidx) (dg_es topo).

  Definition RqUpRule (rule: Rule) :=
    exists coidx rqmidx rqfmidx poidx,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_trs rule post porq ins = (nost, norq, outs) ->
          idsOf outs = [rqfmidx]) /\
      getParent gtr (rule_oidx rule) = Some poidx /\
      getParent gtr coidx = Some (rule_oidx rule) /\
      In (createEdge coidx rqmidx (rule_oidx rule)) (dg_es topo) /\
      In (createEdge (rule_oidx rule) rqfmidx poidx) (dg_es topo).

  Definition RqDownRule (rule: Rule) :=
    exists rqoidx rqmidx rqfminds coinds,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_trs rule post porq ins = (nost, norq, outs) ->
          idsOf outs = rqfminds) /\
      Forall (fun cind => getParent gtr cind = Some (rule_oidx rule)) coinds /\
      In (createEdge rqoidx rqmidx (rule_oidx rule)) (dg_es topo) /\
      Forall (fun om => In (createEdge (rule_oidx rule) (fst om) (snd om))
                           (dg_es topo))
             (combine coinds rqfminds).

  Definition RsRule (rule: Rule) :=
    exists coinds rsminds rsbmidx,
      rule_minds rule = rsminds /\
      (forall post pors ins nost nors outs,
          rule_trs rule post pors ins = (nost, nors, outs) ->
          idsOf outs = [rsbmidx]) /\
      Forall (fun om => In (createEdge (snd om) (fst om) (rule_oidx rule))
                           (dg_es topo))
             (combine coinds rsminds).

  Definition RqRsRule (rule: Rule) :=
    ImmRule rule \/
    RqUpRule rule \/ RqDownRule rule \/
    RsRule rule.

  (** TODO: do we need this? *)
  (* Definition RqRsSafe (sys: System) := *)
  (*   forall rqr rsr, *)
  (*     In rqr (sys_rules sys) -> In rsr (sys_rules sys) -> *)
  (*     RqUpRule rqr -> *)
  (*     (ImmRule rsr \/ UpRsBackRule rsr) -> *)
  (*     forall post porq ins, *)
  (*       rule_precond rqr post porq ins -> *)
  (*       forall nost norq outs, *)
  (*         rule_trs rsr post porq ins = (nost, norq, outs) -> *)
  (*         rule_precond rqr nost norq ins. *)

  Definition RqRsSys (sys: System) :=
    Forall RqRsRule (sys_rules sys).
  (* RqRsSafe sys. *)
  
End RqRsRule.

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

(* Fixpoint mconcat {A} (ms: list (M.t A)): M.t A := *)
(*   match ms with *)
(*   | nil => M.empty _ *)
(*   | m :: ms' => *)
(*     M.union m (mconcat ms') *)
(*   end. *)

Section RqRsSerial.
  Variable (gtr: GTree) (sys: System).
  Hypotheses (Hrr: RqRsSys gtr sys)
             (Hpb: PartialBlockingSys gtr sys).

  Lemma rqrs_well_interleaved_push:
    WellInterleavedPush sys.
  Proof.
    red; intros.
  Admitted.
  
  Theorem immrqrs_pb_serializable:
    SerializableSys sys.
  Proof.
    apply well_interleaved_serializable.
    apply well_interleaved_push_ok.
    apply rqrs_well_interleaved_push.
  Qed.

End RqRsSerial.

