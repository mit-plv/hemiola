Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts.
Require Import QuasiSeq Reduction Denotation.

Require Import Omega.

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

  Definition ImmRqRsSafe (sys: System) :=
    forall rqr rsr,
      In rqr (sys_rules sys) -> In rsr (sys_rules sys) ->
      UpRqFwdRule rqr ->
      (ImmRule rsr \/ UpRsBackRule rsr) ->
      forall post porq ins,
        rule_precond rqr post porq ins ->
        forall nost norq outs,
          rule_trs rsr post porq ins = (nost, norq, outs) ->
          rule_precond rqr nost norq ins.

  Definition ImmRqRsSys (sys: System) :=
    Forall ImmRqRsRule (sys_rules sys) /\
    ImmRqRsSafe sys.
  
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

Section RAtomic.
  Variables (sys: System) (topo: CTree).

  (* Here we define [RAtomic], which defines a set of atomic sequences only by
   * immediate, request-forwarding, and responses-back rules.
   *)
  Inductive RAtomic:
    list (Id Msg) (* initially-dequeued messages *) ->
    list (Id Msg) (* all-dequeued  *) ->
    History Msg (* history *) ->
    list (Id Msg) (* all-enqueued *) ->
    list (Id Msg) (* eventual outputs *) ->
    Prop :=

  (** singletons *)
  | RAtomicImm:
      forall rq rqr rs,
        msg_rr (valOf rq) = Rq ->
        msg_rr (valOf rs) = Rs ->
        RAtomic [rq] [rq] [RlblInt rqr [rq] [rs]] [rs] [rs]
  | RAtomicRqFwd:
      forall rq rqr rqfs,
        msg_rr (valOf rq) = Rq ->
        Forall (fun rqf => msg_rr (valOf rqf) = Rq) rqfs ->
        RAtomic [rq] [rq] [RlblInt rqr [rq] rqfs] rqfs rqfs
  | RAtomicRsBack:
      forall rss rsr rsb,
        Forall (fun rs => msg_rr (valOf rs) = Rs) rss ->
        msg_rr (valOf rsb) = Rs ->
        RAtomic rss rss [RlblInt rsr rss [rsb]] [rsb] [rsb].

  (** request-forwarding *)
  (* | RAtomicRqFwdApp: *)
  (*     forall rq rqr rqfs rqfsp rqfins rqfhsts rqfouts rqfeouts, *)
  (*       msg_rr (valOf rq) = Rq -> *)
  (*       RAtomic [rq] [rq] [RlblInt rqr [rq] rqfs] rqfs rqfs -> *)

  (*       (* forwarded requests can be partially handled. *) *)
  (*       SubList rqfsp rqfs -> NoDup rqfsp -> *)
  
  (*       Forall (fun iihoo => *)
  (*                 msg_rr (valOf (fst moho)) = Rq /\ *)
  (*                 RAtomic [fst iihoo] (fst (snd iihoo)) *)
  (*                         (fst (snd (snd iihoo))) *)
  (*                         (fst (snd (snd (snd iihoo)))) *)
  (*                         (snd (snd (snd (snd iihoo))))) *)
  (*              (combine rqfsp (combine (rqfins (combine rqfhsts (combine rqfouts rqfeouts))))) -> *)
  
  (*       RAtomic [rq] ?? *)
  (*               (List.concat rqfhsts ++ [RlblInt rqr [rq] rqfs]) *)
  (*               ?? ??. *)
  (** responses-back *)
  (* | RAtomicRsBackApp: *)
  (*     forall rq oinds hst rsr rss rsb, *)
  (*       Forall (fun rs => msg_rr (getMsg (valOf rs)) = Rs) rss -> *)
  (*       msg_rr (getMsg (valOf rsb)) = Rs -> *)
  (*       RAtomic [rq] oinds hst (enqMsgs rss (emptyMP _)) -> *)
  (*       RAtomic [rq] oinds (RlblInt rsr rss [rsb] :: hst) (enqMPI rsb (emptyMP _)). *)

End RAtomic.

Section ImmRqRsSerial.
  Variable (topo: CTree) (sys: System).
  Hypotheses (Hirr: ImmRqRsSys topo sys)
             (Hpb: PartialBlockingSys topo sys).

  (* Lemma immrqrs_atomic_ratomic: *)
  (*   forall st1 hst st2, *)
  (*     steps step_m sys st1 hst st2 -> *)
  (*     forall inits1 ins1 outs1 eouts1, *)
  (*       Atomic inits1 ins1 hst outs1 eouts1 -> *)
  (*       RAtomic inits1 ins1 hst outs1 eouts1. *)
  
  Lemma immrqrs_well_interleaved_push:
    WellInterleavedPush sys.
  Proof.
    red; intros.

    red in H.
    destruct H as [inits1 [ins1 [outs1 [eouts1 ?]]]].
    destruct H as [inits2 [ins2 [outs2 [eouts2 [? [? [? ?]]]]]]].
    (* apply immrqrs_atomic_ratomic in H. *)
    (* apply immrqrs_atomic_ratomic in H4. *)
  Admitted.
  
  Theorem immrqrs_pb_serializable:
    SerializableSys sys.
  Proof.
    apply well_interleaved_serializable.
    apply well_interleaved_push_ok.
    apply immrqrs_well_interleaved_push.
  Qed.

End ImmRqRsSerial.

