Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT.
Require Import Topology Serial SerialFacts Reduction.

Require Import Omega Permutation Wf.

Set Implicit Arguments.

Section ImmRqRs.
  Variable (topo: CTree).

  Definition ImmRule (rule: Rule) :=
    exists rqoidx rqmidx rsmidx,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_postcond rule post porq ins nost norq outs ->
          idsOf outs = [rsmidx]) /\
      In (Build_Channel rqoidx rqmidx (rule_oidx rule)) (ctr_chns topo) /\
      In (Build_Channel (rule_oidx rule) rsmidx rqoidx) (ctr_chns topo).

  Definition UpRqFwdRule (rule: Rule) :=
    exists coidx rqmidx rqfmidx poidx,
      rule_minds rule = [rqmidx] /\
      (forall post porq ins nost norq outs,
          rule_postcond rule post porq ins nost norq outs ->
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
          rule_postcond rule post porq ins nost norq outs ->
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
          rule_postcond rule post pors ins nost nors outs ->
          idsOf outs = [rsbmidx]) /\
      (getParent (ctr_tr topo) (rule_oidx rule))
        >>=[False] (fun ptr => trCurOIdxOf ptr = poidx) /\
      In (Build_Channel poidx rsmidx (rule_oidx rule)) (ctr_chns topo) /\
      In (Build_Channel (rule_oidx rule) rsbmidx coidx) (ctr_chns topo).

  Definition UpRsBackRule (rule: Rule) :=
    exists coinds rsminds rsbmidx rsboidx,
      rule_minds rule = rsminds /\
      (forall post pors ins nost nors outs,
          rule_postcond rule post pors ins nost nors outs ->
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
  Definition PartialBlockingPrec (oidx: IdxT): RPrecond :=
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
    (rule_precond rule) ->rprec (PartialBlockingPrec (rule_oidx rule)).

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

  Context {MsgT} `{HasMsg MsgT}.

  (* Here we define [RAtomic], which also defines a set of atomic sequences.
   * They are more restrictive than ordinary [Atomic] sequences in that they are
   * generated by a certain set of rules -- immediate, request-forwarding, and
   * responses-back.
   *)
  Inductive RAtomic:
    list (Id MsgT) (* requestors *) -> list IdxT (* affected objects *) ->
    History MsgT -> MessagePool MsgT -> Prop :=
  (* | RAtomicStart: *)
  (*     forall ins rule outs, *)
  (*       RAtomic ins [rule_oidx rule] [RlblInt rule ins outs] *)
  (*               (enqMsgs outs (emptyMP _)) *)
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
  | RAtomicRqFwdA:
      forall rq rqr rqfwds rqfwdsp rqfoinds rqfhsts rqfouts,
        msg_rr (getMsg (valOf rq)) = Rq ->
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
                (mconcat rqfouts) (* FIXME: add uninitiated request forwardings *)
  | RAtomicRsBackA:
      forall rq oinds hst rsr rss rsb,
        Forall (fun rs => msg_rr (getMsg (valOf rs)) = Rs) rss ->
        msg_rr (getMsg (valOf rsb)) = Rs ->
        RAtomic [rq] oinds hst (enqMsgs rss (emptyMP _)) ->
        RAtomic [rq] oinds (RlblInt rsr rss [rsb] :: hst) (enqMPI rsb (emptyMP _)).

End RAtomic.

(*! Reducibility of request-forwardings and responses-back *)

(* For a given list of "list of transactions," we want to preserve an order
 * for each "list of transactions."
 *)
Inductive OPermutation {A}: list (list (list A)) -> list A -> Prop :=
| OPermNil: OPermutation nil nil
| OPermCons:
    forall strss1 trs trss strss2 hst,
      OPermutation (strss1 ++ trss :: strss2) hst ->
      OPermutation (strss1 ++ (trs :: trss) :: strss2) (trs ++ hst).
                
Definition liftSingletonTrs (hst: MHistory) :=
  map (fun lbl => [lbl]) hst.

(** * TODO: change all [Atomic] in below lemmas to a stronger one [RAtomic]? *)

Lemma downward_request_forwardings_reduced:
  forall sys rqfr rq rqfs rqfsp trss,

    (* A subtransaction for each downward request can happen 
     * in an arbitrary order. *)
    Permutation rqfs rqfsp ->

    (* [trss] are the subtransactions of downward requests,
     * where each of them is already [Atomic]. *)
    Forall (fun rqtrs => exists outs, Atomic [fst rqtrs] (snd rqtrs) outs)
           (combine rqfsp trss) ->

    (* Other irrelevant transaction segments and the subtransactions
     * are interleaved in an arbitrary manner. *)
    forall trsoths others,
      OPermutation [trss; liftSingletonTrs others] trsoths ->

      (* This reduction claims that all the irrelevant segments can be
       * left-pushed before the original request-forwarding label. *)
      Reduced sys (trsoths ++ [RlblInt rqfr [rq] rqfs])
              (List.concat trss ++ [RlblInt rqfr [rq] rqfs] ++ others).
Proof.
  (* induction on [OPermutation]? *)
Admitted.

Lemma upward_request_forwarding_reduced:
  forall sys rqfr rq rqf trs outs,

    (* The transaction for the upward request is already [Atomic]. *)
    Atomic [rqf] trs outs ->

    (* This reduction claims that intermediate irrelevant subhistory [others]
     * can be left-pushed before the original request-forwarding label. *)
    forall others,
      Reduced sys (trs ++ others ++ [RlblInt rqfr [rq] [rqf]])
              (trs ++ [RlblInt rqfr [rq] [rqf]] ++ others).
Proof.
  (* induction on [others]? *)
Admitted.

Lemma upward_responses_back_reduced:
  forall sys rsbr rss rssp trss rsb,

    (* A subtransaction for each upward response can happen 
     * in an arbitrary order. *)
    Permutation rss rssp ->

    (* [trss] are the subtransactions of upward responses,
     * where each of them is already [Atomic]. *)
    Forall (fun rstrs =>
              exists rq, Atomic rq (snd rstrs) (enqMPI (fst rstrs) (emptyMP _)))
           (combine rssp trss) ->

    (* Other irrelevant transaction segments and the subtransactions
     * are interleaved in an arbitrary manner. *)
    forall trsoths others,
      OPermutation [trss; liftSingletonTrs others] trsoths ->

      (* This reduction claims that all the irrelevant segments can be
       * right-pushed after the response-back label. *)
      Reduced sys (RlblInt rsbr rss [rsb] :: trsoths)
              (others ++ RlblInt rsbr rss [rsb] :: List.concat trss).
Proof.
Admitted.

Lemma downward_response_back_reduced:
  forall sys rq rsbr rs trs rsb,

    (* The transaction for the downward response is already [Atomic]. *)
    Atomic rq trs (enqMPI rs (emptyMP _)) ->

    (* This reduction claims that intermediate irrelevant subhistory [others] *)
    (* can be right-pushed after the response-back label. *)
    forall others,
      Reduced sys (RlblInt rsbr [rs] [rsb] :: others ++ trs)
              (others ++ RlblInt rsbr [rs] [rsb] :: trs).
Proof.
  (* induction on [others]? *)
Admitted.

(*! Proving [Serializability] using quasi-sequential histories *)

Section QuasiSeq.
  Variables (sys: System)
            (quasiSeq: forall (sys: System) (hst: MHistory) (n: nat), Prop).

  Definition QuasiSeqOkInit :=
    forall hst st,
      steps step_m sys (initsOf sys) hst st ->
      exists n, quasiSeq sys hst n.
    
  Definition QuasiSeqOkStep :=
    forall hst st1 st2 n,
      steps step_m sys st1 hst st2 ->
      quasiSeq sys hst n ->
      (Sequential sys hst \/
       exists rhst m, Reduced sys hst rhst /\
                      quasiSeq sys rhst m /\ m < n).

  Lemma quasiSeq_implies_serializableSys:
    QuasiSeqOkStep ->
    forall n hst st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      Serializable sys hst.
  Proof.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros.
    specialize (H _ _ _ _ H0 H1); destruct H.
    - eapply sequential_serializable; eauto.
    - destruct H as [rhst [m [? [? ?]]]].
      eapply reduced_serializable; eauto.
      eapply IHn; eauto.
      eapply H; eauto.
  Qed.

  Lemma quasiSeqOk_implies_serializableSys:
    QuasiSeqOkInit -> QuasiSeqOkStep -> SerializableSys sys.
  Proof.
    intros; red; intros.
    specialize (H _ _ H1); destruct H as [n ?].
    eapply quasiSeq_implies_serializableSys; eauto.
  Qed.

End QuasiSeq.

(* A list of (semi-)transactions is [Interleaved] iff
 * 1) there is a transaction which is [Atomic] but not [ExtAtomic] and
 * 2) this transaction and the previous transaction stem from different
 *    transactions, i.e., they cannot be merged into a single transaction.
 *)
Definition Interleaved (sys: System) {MsgT} (trss: list (History MsgT)) :=
  exists ins trs outs dtrs trss1 trss2,
    Atomic ins trs outs /\ ~ SubList (idsOf ins) (merqsOf sys) /\
    trss = trss1 ++ trs :: dtrs :: trss2 /\
    ~ STransactional (trs ++ dtrs).

(* Any legal transaction sequences are either [Sequential] or [Interleaved]. *)
Lemma stransactional_sequential_or_interleaved:
  forall sys trss st1 st2,
    steps step_m sys st1 (List.concat trss) st2 ->
    Forall STransactional trss ->
    Sequential sys (List.concat trss) \/
    Interleaved sys trss.
Proof.
Admitted.

Section ImmRqRsSerial.
  Variable (topo: CTree) (sys: System).
  Hypotheses (Hirr: ImmRqRsSys topo sys)
             (Hpb: PartialBlockingSys topo sys).

  Local Definition quasiSeq :=
    fun (_: System) (hst: MHistory) n => SSequential hst n.

  (* A possibly useful lemma:
   * forall ins hst outs, Atomic ins hst outs ->
   * it's either immediate or rq-fwd(+rs-back).
   *)

  Lemma immrqrs_partial_blocking_interleaved_reducible:
    forall trss st1 st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall STransactional trss ->
      Interleaved sys trss ->
      exists (rhst : MHistory) (m : nat),
        Reduced sys (List.concat trss) rhst /\
        SSequential rhst m /\
        m < Datatypes.length trss.
  Proof.
    intros.
    destruct H1 as [ins [trs [outs [dtrs [trss1 [trss2 [? [? [? ?]]]]]]]]].
    subst.
  Admitted.
  
  Lemma immrqrs_partial_blocking_quasiSeq_ok:
    QuasiSeqOkStep sys quasiSeq.
  Proof.
    red; intros.
    inv H0.
    pose proof (stransactional_sequential_or_interleaved H H3).
    destruct H0; [auto|].
    right.
    eapply immrqrs_partial_blocking_interleaved_reducible; eauto.
  Qed.

  Theorem immrqrs_partial_blocking_serializable:
    SerializableSys sys.
  Proof.
    intros.
    apply quasiSeqOk_implies_serializableSys with (quasiSeq := quasiSeq).
    - red; intros.
      apply SSequential_default.
    - apply immrqrs_partial_blocking_quasiSeq_ok.
  Qed.

End ImmRqRsSerial.

