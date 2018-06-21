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

Section ImmRqRsSerial.
  Variable (topo: CTree) (sys: System).
  Hypotheses (Hirr: ImmRqRsSys topo sys)
             (Hpb: PartialBlockingSys topo sys).

  Lemma immrqrs_well_interleaved_ind:
    WellInterleavedInd sys.
  Proof.
  Admitted.
  
  Theorem immrqrs_pb_serializable:
    SerializableSys sys.
  Proof.
    apply well_interleaved_serializable.
    apply well_interleaved_ind_ok.
    apply immrqrs_well_interleaved_ind.
  Qed.

End ImmRqRsSerial.

