Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT.
Require Import Topology Serial Reduction.

Require Import Permutation.

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

Section RAtomic.
  Variables (sys: System) (topo: CTree).

  Context {MsgT} `{HasMsg MsgT}.

  (** An [option] flag for the existence of response;
   * if the history contains the response [rs], then [Some rs].
   *)
  (* Inductive RAtomic: *)
  (*   IdxT (* requestor *) -> list IdxT (* affected objects *) -> *)
  (*   Id MsgT (* request *) -> History MsgT -> option (Id MsgT) (* response *) -> Prop := *)
  (* | RAtomicImm: *)
  (*     forall rqi immi immr rq rs, *)
  (*       rule_oidx immr = immi -> *)
  (*       In {| chn_midx := idOf rq; chn_from := rqi; chn_to := immi |} (ctr_chns topo) -> *)
  (*       In {| chn_midx := idOf rs; chn_from := immi; chn_to := rqi |} (ctr_chns topo) -> *)
  (*       RAtomic rqi [immi] rq [RlblInt (Some immr) [rq] [rs]] (Some rs) *)
  (* | RAtomicRq *)

End RAtomic.

(*! Reducibility of request-forwardings and responses-back *)

Definition liftSingletonTrs (hst: MHistory) :=
  map (fun lbl => [lbl]) hst.

(* For a given list of "list of transactions," we want to preserve an order
 * for each "list of transactions."
 *)
Inductive OPermutation {A}: list (list (list A)) -> list A -> Prop :=
| OPermNil: OPermutation nil nil
| OPermCons:
    forall strss1 trs trss strss2 hst,
      OPermutation (strss1 ++ trss :: strss2) hst ->
      OPermutation (strss1 ++ (trs :: trss) :: strss2) (trs ++ hst).

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


(*! Serializability, using the above reduction lemmas *)
(* TODO: we may have to provide more necessary conditions 
 * about the given topology and channels.
 *)
Section PerSystem.
  Variable (topo: CTree) (sys: System).
  Hypotheses (Hirr: ImmRqRsSys topo sys)
             (Hpb: PartialBlockingSys topo sys).

  Lemma immrqrs_partial_blocking_reduced_to_sequential:
    forall hst st,
      steps step_m sys (initsOf sys) hst st ->
      exists shst,
        Reduced sys hst shst /\ Sequential sys shst.
  Proof.
    
  Admitted.

  Theorem immrqrs_partial_blocking_serializable:
    SerializableSys sys.
  Proof.
    unfold SerializableSys; intros.
    pose proof (immrqrs_partial_blocking_reduced_to_sequential _ _ H).
    dest.
    eapply reduced_to_seq_serializable; eauto.
  Qed.

End PerSystem.

