Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutable QuasiSeq Topology.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Conditions.
  Context {oifc: OStateIfc}.

  (** Preconditions and postconditions dealing with messages. *)

  Definition MsgsFrom (froms: list IdxT): OPrec oifc :=
    fun _ _ mins => idsOf mins = froms.

  Definition MsgIdsFrom (msgIds: list IdxT): OPrec oifc :=
    fun _ _ mins => map msg_id (valsOf mins) = msgIds.

  Definition MsgsFromORq (rqty: IdxT): OPrec oifc :=
    fun _ orq mins =>
      (getRq orq rqty)
        >>=[False] (fun rqi => idsOf mins = rqi_minds_rss rqi).

  Definition MsgsTo (tos: list IdxT) (rule: Rule oifc): Prop :=
    forall ost orq mins,
      idsOf (snd (rule.(rule_trs) ost orq mins)) = tos.

  Definition RqAccepting: OPrec oifc :=
    fun _ _ mins =>
      Forall (fun idm => msg_type (valOf idm) = MRq) mins.

  Definition RsAccepting: OPrec oifc :=
    fun _ _ mins =>
      Forall (fun idm => msg_type (valOf idm) = MRs) mins.

  Definition RqReleasing (rule: Rule oifc) :=
    forall ost orq mins,
      Forall (fun idm => msg_type (valOf idm) = MRq)
             (snd (rule.(rule_trs) ost orq mins)).

  Definition RsReleasing (rule: Rule oifc) :=
    forall ost orq mins,
      Forall (fun idm => msg_type (valOf idm) = MRs)
             (snd (rule.(rule_trs) ost orq mins)).

  (** Preconditions to check the lock state *)
  Definition upRq := 0.
  Definition downRq := 1.

  Definition LockFreeORq (orq: ORq Msg) :=
    orq@[upRq] = None /\ orq@[downRq] = None.

  Definition UpLockFreeORq (orq: ORq Msg) :=
    orq@[upRq] = None.

  Definition DownLockFreeORq (orq: ORq Msg) :=
    orq@[downRq] = None.

  Definition UpLockedORq (orq: ORq Msg) :=
    orq@[upRq] <> None.

  Definition DownLockedORq (orq: ORq Msg) :=
    orq@[downRq] <> None.

  Definition UpLockFree: OPrec oifc :=
    fun ost orq mins => UpLockFreeORq orq.

  Definition DownLockFree: OPrec oifc :=
    fun ost orq mins => DownLockFreeORq orq.

  Definition UpLocking (rule: Rule oifc): Prop :=
    forall ost orq mins,
      exists rqi,
        snd (fst (rule.(rule_trs) ost orq mins)) = orq+[upRq <- rqi].

  Definition DownLocking (rule: Rule oifc): Prop :=
    forall ost orq mins,
      exists rqi,
        snd (fst (rule.(rule_trs) ost orq mins)) = orq+[downRq <- rqi].

  Definition UpReleasing (rule: Rule oifc): Prop :=
    forall ost orq mins,
      UpLockedORq orq /\
      UpLockFreeORq (snd (fst (rule.(rule_trs) ost orq mins))).

  Definition DownReleasing (rule: Rule oifc): Prop :=
    forall ost orq mins,
      DownLockedORq orq /\
      DownLockFreeORq (snd (fst (rule.(rule_trs) ost orq mins))).

  Definition SubLock (orq1 orq2: ORq Msg) :=
    M.Sub orq1 orq2.
  
  Definition PrecLockMonotone (rule: Rule oifc) :=
    forall ost orq mins,
      rule.(rule_precond) ost orq mins ->
      forall rorq,
        SubLock rorq orq ->
        rule.(rule_precond) ost rorq mins.

  Definition StateUnchanged (rule: Rule oifc): Prop :=
    forall ost orq mins,
      ost = fst (fst (rule.(rule_trs) ost orq mins)).

  (** Some facts *)

  Lemma UpLockFree_UpLocking_SubLock:
    forall rule post porq mins nost norq mouts,
      UpLockFree post porq mins ->
      UpLocking rule ->
      rule.(rule_precond) post porq mins ->
      rule.(rule_trs) post porq mins = (nost, norq, mouts) ->
      SubLock porq norq.
  Proof.
    unfold UpLockFree, UpLockFreeORq, UpLocking, SubLock; intros.
    specialize (H0 post porq mins).
    rewrite H2 in H0.
    simpl in H0; destruct H0 as [rqi ?]; subst.
    red; intros; mred.
  Qed.

  Lemma DownLockFree_DownLocking_SubLock:
    forall rule post porq mins nost norq mouts,
      DownLockFree post porq mins ->
      DownLocking rule ->
      rule.(rule_precond) post porq mins ->
      rule.(rule_trs) post porq mins = (nost, norq, mouts) ->
      SubLock porq norq.
  Proof.
    unfold DownLockFree, DownLockFreeORq, DownLocking, SubLock; intros.
    specialize (H0 post porq mins).
    rewrite H2 in H0.
    simpl in H0; destruct H0 as [rqi ?]; subst.
    red; intros; mred.
  Qed.
  
End Conditions.

Section RqRsTopo.
  Variables (gtr: DTree) (oifc: OStateIfc).

  Inductive RqRsTopo: DTree -> Prop :=
  | RqRsNode:
      forall ridx cs,
        Forall (fun udc =>
                  List.length (fst (fst udc)) = 2 /\ (* Two upward channels *)
                  List.length (snd (fst udc)) = 1 /\ (* A single downward channel *)
                  RqRsTopo (snd udc)) cs ->
        RqRsTopo (Node ridx cs).

  Definition edgeInds (es: list (edge DChn)): list IdxT :=
    map (fun e => snd e.(edge_chn)) es.

  Definition rqUpEdges: list IdxT :=
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRq) (upEdges gtr)).

  Definition rsUpEdges: list IdxT :=
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRs) (upEdges gtr)).

  Definition upEdges: list IdxT :=
    edgeInds (upEdges gtr).
  
  Definition downEdges: list IdxT :=
    edgeInds (downEdges gtr).

  Definition treeEdges: list IdxT :=
    edgeInds (dg_es (topoOfT gtr)).
  
  Definition rqEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRq)
                               (upEdgesFrom gtr oidx))).

  Definition rsEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRs)
                               (upEdgesFrom gtr oidx))).

  Definition rqEdgesUpTo (oidx: IdxT): list IdxT :=
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRq)
                     (upEdgesTo gtr oidx)).

  Definition rsEdgesUpTo (oidx: IdxT): list IdxT :=
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRs)
                     (upEdgesTo gtr oidx)).

  Definition edgesDownFrom (oidx: IdxT): list IdxT :=
    edgeInds (downEdgesFrom gtr oidx).

  Definition edgeDownTo (oidx: IdxT): option IdxT :=
    hd_error (edgeInds (downEdgesTo gtr oidx)).

  (* Upward-requested *)
  Definition FootprintedUp (orq: ORq Msg) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists rqi,
      orq@[upRq] = Some rqi /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (* Downward-requested *)
  Definition FootprintedDown (orq: ORq Msg) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists rqi,
      orq@[downRq] = Some rqi /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (** This precondition is required when handling a _downward response_. *)
  Definition FootprintedUpPrec (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    rule.(rule_precond)
    ->oprec (fun _ orq _ => FootprintedUp orq rssFrom rsbTo).

  (** This precondition is required when handling _upward responses_. *)
  Definition FootprintedDownPrec (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    rule.(rule_precond)
    ->oprec (fun _ orq _ => FootprintedDown orq rssFrom rsbTo).

  (* A rule is making an upward request. *)
  Definition FootprintingUp (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    forall ost orq mins,
      FootprintedUp (snd (fst (rule.(rule_trs) ost orq mins))) rssFrom rsbTo.

  (* A rule is making downward requests. *)
  Definition FootprintingDown (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    forall ost orq mins,
      FootprintedDown (snd (fst (rule.(rule_trs) ost orq mins))) rssFrom rsbTo.

  Definition FootprintUpOk (oidx: IdxT) (rqTo rsFrom rsbTo: IdxT) :=
    exists cidx,
      rqEdgeUpFrom oidx = Some rqTo /\
      edgeDownTo oidx = Some rsFrom /\
      edgeDownTo cidx = Some rsbTo.
  
  Definition FootprintDownOk
             (rqFrom: IdxT) (rqTos: list IdxT)
             (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists upCIdx downCInds,
      ~ In upCIdx downCInds /\
      rqEdgeUpFrom upCIdx = Some rqFrom /\
      edgeDownTo upCIdx = Some rsbTo /\
      Forall (fun crq => edgeDownTo (fst crq) = Some (snd crq))
             (combine downCInds rqTos) /\
      Forall (fun crs => rsEdgeUpFrom (fst crs) = Some (snd crs))
             (combine downCInds rssFrom).
  
  Section GoodLocking.

    Section PerObject.
      Variable (oidx: IdxT).
      
      (** * Rule predicates about which messages to accept *)

      (* A rule handling a request from one of its children *)
      Definition RqFromDownRule (rule: Rule oifc) :=
        exists rqFrom,
          In rqFrom (rqEdgesUpTo oidx) /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting /\oprec UpLockFree)).

      (* A rule handling a request from the parent *)
      Definition RqFromUpRule (rule: Rule oifc) :=
        exists rqFrom,
          edgeDownTo oidx = Some rqFrom /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)).

      (* A rule handling responses from some of its children *)
      Definition RsFromDownRule (rule: Rule oifc) :=
        exists rssFrom,
          SubList rssFrom (rsEdgesUpTo oidx) /\ NoDup rssFrom /\
          (rule.(rule_precond) ->oprec (MsgsFrom rssFrom /\oprec RsAccepting)) /\
          DownReleasing rule.

      (* A rule handling a response from the parent *)
      Definition RsFromUpRule (rule: Rule oifc) :=
        exists rsFrom,
          edgeDownTo oidx = Some rsFrom /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rsFrom] /\oprec RsAccepting)) /\
          UpReleasing rule.

      (** * Rule predicates about which messages to release *)

      (* A rule making requests to some of its children *)
      Definition RqToDownRule (rule: Rule oifc) :=
        exists rqsTo,
          SubList rqsTo (edgesDownFrom oidx) /\ NoDup rqsTo /\
          MsgsTo rqsTo rule /\ RqReleasing rule /\
          (rule.(rule_precond) ->oprec DownLockFree) /\
          DownLocking rule /\
          StateUnchanged rule.

      (* A rule making a request to the parent *)
      Definition RqToUpRule (rule: Rule oifc) :=
        exists rqTo,
          rqEdgeUpFrom oidx = Some rqTo /\
          MsgsTo [rqTo] rule /\ RqReleasing rule /\
          UpLocking rule /\
          StateUnchanged rule.

      (* A rule making a response to one of its children *)
      Definition RsToDownRule (rule: Rule oifc) :=
        exists rsTo,
          In rsTo (edgesDownFrom oidx) /\
          MsgsTo [rsTo] rule /\ RsReleasing rule /\
          (** Below [DownLockFree] is a crucial locking condition to avoid
           * incorrect behaviors by interleaving! *)
          (rule.(rule_precond) ->oprec DownLockFree).
      
      (* A rule making a response to the parent:
       * Note that unlike [RsToDownRule] we don't have any locking condition for
       * any upward responses. If we put [UpLockFree] here then it's correct
       * but makes deadlock. *)
      Definition RsToUpRule (rule: Rule oifc) :=
        exists rsTo,
          rsEdgeUpFrom oidx = Some rsTo /\
          MsgsTo [rsTo] rule /\
          RsReleasing rule.

      Definition GoodLockingAccept (rule: Rule oifc) :=
        RqFromDownRule rule \/
        RqFromUpRule rule \/
        RsFromDownRule rule \/
        RsFromUpRule rule.

      Definition GoodLockingRelease (rule: Rule oifc) :=
        RqToDownRule rule \/
        RqToUpRule rule \/
        RqToDownRule rule \/
        RsToUpRule rule.

      Definition GoodLockingRule (rule: Rule oifc) :=
        GoodLockingAccept rule /\
        GoodLockingRelease rule /\
        PrecLockMonotone rule.

    End PerObject.

    Definition GoodLockingObj (obj: Object oifc) :=
      Forall (GoodLockingRule obj.(obj_idx)) obj.(obj_rules).
    
    Definition GoodLockingSys (sys: System oifc) :=
      Forall GoodLockingObj sys.(sys_objs).
    
  End GoodLocking.

  Section GoodIteration.
    
    Section PerObject.
      Variable (oidx: IdxT).
      
      (* A rule making an immediate response to one of its children *)
      Definition ImmDownRule (rule: Rule oifc) :=
        exists cidx rqFrom rsTo,
          rqEdgeUpFrom cidx = Some rqFrom /\
          edgeDownTo cidx = Some rsTo /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)) /\
          MsgsTo [rsTo] rule /\ RsReleasing rule.

      (* A rule making an immediate response to the parent *)
      Definition ImmUpRule (rule: Rule oifc) :=
        exists rqFrom rsTo,
          edgeDownTo oidx = Some rqFrom /\
          rsEdgeUpFrom oidx = Some rsTo /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)) /\
          MsgsTo [rsTo] rule /\ RsReleasing rule.

      (* A rule forwarding a request. Request-forwarding rules should satisfy
       * following two properties:
       * 1) No RqDown-RqUp in order to control iteration order.
       * 2) Correct footprinting (to [ORq])
       *)
      Definition RqUpUp (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        In rqFrom (rqEdgesUpTo oidx) /\
        exists rqTo rsFrom rsbTo,
          rqTos = [rqTo] /\
          FootprintUpOk oidx rqTo rsFrom rsbTo /\
          FootprintingUp rule [rsFrom] rsbTo.

      Definition RqUpDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        In rqFrom (rqEdgesUpTo oidx) /\
        SubList rqTos (edgesDownFrom oidx) /\
        exists rssFrom rsbTo,
          FootprintDownOk rqFrom rqTos rssFrom rsbTo /\
          FootprintingDown rule rssFrom rsbTo.

      Definition RqDownDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        In rqFrom (edgesDownFrom oidx) /\
        SubList rqTos (edgesDownFrom oidx) /\
        exists downCIdx downCInds rssFrom rsbTo,
          edgeDownTo downCIdx = Some rqFrom /\
          rsEdgeUpFrom downCIdx = Some rsbTo /\
          Forall (fun crq => edgeDownTo (fst crq) = Some (snd crq))
                 (combine downCInds rqTos) /\
          Forall (fun crs => rsEdgeUpFrom (fst crs) = Some (snd crs))
                 (combine downCInds rssFrom) /\
          FootprintingDown rule rssFrom rsbTo.

      Definition RqFwdRule (rule: Rule oifc) :=
        exists rqFrom rqTos,
          (RqUpUp rqFrom rqTos rule \/
           RqUpDown rqFrom rqTos rule \/
           RqDownDown rqFrom rqTos rule) /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)) /\
          MsgsTo rqTos rule /\ RqReleasing rule.
      
      Definition RsBackRule (rule: Rule oifc) :=
        exists rssFrom rsbTo,
          (FootprintedUpPrec rule rssFrom rsbTo \/
           FootprintedDownPrec rule rssFrom rsbTo) /\
          (rule.(rule_precond) ->oprec (MsgsFrom rssFrom /\oprec RsAccepting)) /\
          MsgsTo [rsbTo] rule /\ RsReleasing rule.

      Definition FootprintUpToDown (rule: Rule oifc) (rsFrom: IdxT) (rqTos: list IdxT) :=
        exists rqFrom rsbTo nrssFrom,
          FootprintedUpPrec rule [rsFrom] rsbTo /\
          FootprintDownOk rqFrom rqTos nrssFrom rsbTo /\
          FootprintingDown rule nrssFrom rsbTo.
      
      Definition RsDownRqDownRule (rule: Rule oifc) :=
        exists rsFrom rqTos,
          FootprintUpToDown rule rsFrom rqTos /\
          edgeDownTo oidx = Some rsFrom /\
          SubList rqTos (edgesDownFrom oidx) /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rsFrom] /\oprec RsAccepting)) /\
          MsgsTo rqTos rule /\ RqReleasing rule.
      
      Definition GoodIterationRule (rule: Rule oifc) :=
        ImmDownRule rule \/ ImmUpRule rule \/
        RqFwdRule rule \/ RsBackRule rule \/
        RsDownRqDownRule rule.

    End PerObject.

    Definition GoodIterationObj (obj: Object oifc) :=
      Forall (GoodIterationRule obj.(obj_idx)) obj.(obj_rules).
    
    Definition GoodIterationSys (sys: System oifc) :=
      Forall GoodIterationObj sys.(sys_objs).
    
  End GoodIteration.

  Section RqUpRsUpComm.

    Definition RqUpRsUpOkObj (obj: Object oifc) :=
      forall rqUpRule rsUpRule,
        In rqUpRule obj.(obj_rules) -> RqToUpRule obj.(obj_idx) rqUpRule ->
        In rsUpRule obj.(obj_rules) -> RsToUpRule obj.(obj_idx) rsUpRule ->
        NonConflictingR rqUpRule rsUpRule.

    Definition RqUpRsUpOkSys (sys: System oifc) :=
      Forall RqUpRsUpOkObj sys.(sys_objs).
    
  End RqUpRsUpComm.

  Definition RqRsSys (sys: System oifc) :=
    GoodLockingSys sys /\
    GoodIterationSys sys /\
    RqUpRsUpOkSys sys.
  
End RqRsTopo.

Close Scope list.
Close Scope fmap.

