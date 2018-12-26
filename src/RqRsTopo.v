Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.

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

  Definition StateSilent (rule: Rule oifc): Prop :=
    forall ost orq mins,
      ost = fst (fst (rule.(rule_trs) ost orq mins)).

  Definition FootprintUpSilent (rule: Rule oifc): Prop :=
    forall ost orq mins,
      let norq := snd (fst (rule.(rule_trs) ost orq mins)) in
      orq@[upRq] = norq@[upRq].

  Definition FootprintDownSilent (rule: Rule oifc): Prop :=
    forall ost orq mins,
      let norq := snd (fst (rule.(rule_trs) ost orq mins)) in
      orq@[downRq] = norq@[downRq].

  Definition FootprintSilent (rule: Rule oifc): Prop :=
    FootprintUpSilent rule /\ FootprintDownSilent rule.
  
End Conditions.

Section RqRsTopo.
  Variables (dtr: DTree) (oifc: OStateIfc).

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
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRq) (upEdges dtr)).

  Definition rsUpEdges: list IdxT :=
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRs) (upEdges dtr)).

  Definition upEdges: list IdxT :=
    edgeInds (upEdges dtr).
  
  Definition downEdges: list IdxT :=
    edgeInds (downEdges dtr).

  Definition treeEdges: list IdxT :=
    edgeInds (dg_es (topoOfT dtr)).
  
  Definition rqEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRq)
                               (upEdgesFrom dtr oidx))).

  Definition rsEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRs)
                               (upEdgesFrom dtr oidx))).

  Definition rqEdgesUpTo (oidx: IdxT): list IdxT :=
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRq)
                     (upEdgesTo dtr oidx)).

  Definition rsEdgesUpTo (oidx: IdxT): list IdxT :=
    edgeInds (filter (fun e => snd (fst e.(edge_chn)) ==n MRs)
                     (upEdgesTo dtr oidx)).

  Definition edgesDownFrom (oidx: IdxT): list IdxT :=
    edgeInds (downEdgesFrom dtr oidx).

  Definition edgeDownTo (oidx: IdxT): option IdxT :=
    hd_error (edgeInds (downEdgesTo dtr oidx)).

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

  (** A rule handling a _downward response_. *)
  Definition FootprintReleasingUp (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    (rule.(rule_precond) ->oprec (fun _ orq _ => FootprintedUp orq rssFrom rsbTo)) /\
    (forall ost orq mins,
        let norq := snd (fst (rule.(rule_trs) ost orq mins)) in
        norq@[upRq] = None).

  (** A rule handling _upward responses_. *)
  Definition FootprintReleasingDown (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    (rule.(rule_precond) ->oprec (fun _ orq _ => FootprintedDown orq rssFrom rsbTo)) /\
    (forall ost orq mins,
        let norq := snd (fst (rule.(rule_trs) ost orq mins)) in
        norq@[downRq] = None).

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

  Definition FootprintUpDownOk
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

  Definition FootprintDownDownOk (rqTos: list IdxT) (rssFrom: list IdxT) :=
    exists downCInds,
      Forall (fun crq => edgeDownTo (fst crq) = Some (snd crq))
             (combine downCInds rqTos) /\
      Forall (fun crs => rsEdgeUpFrom (fst crs) = Some (snd crs))
             (combine downCInds rssFrom).
  
  Section GoodRqRs.
    
    Section PerObject.
      Variable (oidx: IdxT).
      
      (* A rule making an immediate response to one of its children *)
      Definition ImmDownRule (rule: Rule oifc) :=
        exists cidx rqFrom rsTo,
          rqEdgeUpFrom cidx = Some rqFrom /\
          edgeDownTo cidx = Some rsTo /\
          parentOf dtr cidx = Some oidx /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rqFrom]
                    /\oprec RqAccepting
                    /\oprec DownLockFree
                    /\oprec UpLockFree)) /\
          MsgsTo [rsTo] rule /\ RsReleasing rule /\
          FootprintSilent rule.

      (* A rule making an immediate response to the parent *)
      Definition ImmUpRule (rule: Rule oifc) :=
        exists rqFrom rsTo,
          edgeDownTo oidx = Some rqFrom /\
          rsEdgeUpFrom oidx = Some rsTo /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rqFrom]
                    /\oprec RqAccepting
                    /\oprec DownLockFree)) /\
          MsgsTo [rsTo] rule /\ RsReleasing rule /\
          FootprintSilent rule.

      (* A rule forwarding a request. Request-forwarding rules should satisfy
       * following two properties:
       * 1) No RqDown-RqUp in order to control iteration order.
       * 2) Correct footprinting (to [ORq])
       *)
      Definition RqUpUp (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        (rule.(rule_precond) ->oprec UpLockFree) /\
        UpLocking rule /\
        exists cidx rqTo rsFrom rsbTo,
          rqEdgeUpFrom cidx = Some rqFrom /\
          parentOf dtr cidx = Some oidx /\
          rqTos = [rqTo] /\
          FootprintUpOk oidx rqTo rsFrom rsbTo /\
          FootprintingUp rule [rsFrom] rsbTo /\
          FootprintDownSilent rule.

      Definition RqUpDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        (rule.(rule_precond) ->oprec DownLockFree) /\
        DownLocking rule /\
        SubList rqTos (edgesDownFrom oidx) /\
        exists cidx rssFrom rsbTo,
          rqEdgeUpFrom cidx = Some rqFrom /\
          parentOf dtr cidx = Some oidx /\
          FootprintUpDownOk rqFrom rqTos rssFrom rsbTo /\
          FootprintingDown rule rssFrom rsbTo /\
          FootprintUpSilent rule.

      Definition RqDownDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        (rule.(rule_precond) ->oprec DownLockFree) /\
        DownLocking rule /\
        edgeDownTo oidx = Some rqFrom /\
        exists rssFrom rsbTo,
          rsEdgeUpFrom oidx = Some rsbTo /\
          FootprintDownDownOk rqTos rssFrom /\
          FootprintingDown rule rssFrom rsbTo /\
          FootprintUpSilent rule.

      Definition RqFwdRule (rule: Rule oifc) :=
        exists rqFrom rqTos,
          (RqUpUp rqFrom rqTos rule \/
           RqUpDown rqFrom rqTos rule \/
           RqDownDown rqFrom rqTos rule) /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)) /\
          MsgsTo rqTos rule /\ RqReleasing rule /\ StateSilent rule.
      
      Definition RsBackRule (rule: Rule oifc) :=
        exists rssFrom rsbTo,
          ((FootprintReleasingUp rule rssFrom rsbTo /\ FootprintDownSilent rule) \/
           (FootprintReleasingDown rule rssFrom rsbTo /\ FootprintUpSilent rule)) /\
          (rule.(rule_precond) ->oprec (MsgsFrom rssFrom /\oprec RsAccepting)) /\
          MsgsTo [rsbTo] rule /\ RsReleasing rule.

      Definition FootprintUpToDown (rule: Rule oifc) (rsFrom: IdxT) (rqTos: list IdxT) :=
        exists rqFrom rsbTo nrssFrom,
          FootprintReleasingUp rule [rsFrom] rsbTo /\
          FootprintUpDownOk rqFrom rqTos nrssFrom rsbTo /\
          FootprintingDown rule nrssFrom rsbTo.
      
      Definition RsDownRqDownRule (rule: Rule oifc) :=
        exists rsFrom rqTos,
          FootprintUpToDown rule rsFrom rqTos /\
          edgeDownTo oidx = Some rsFrom /\
          SubList rqTos (edgesDownFrom oidx) /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rsFrom]
                    /\oprec RsAccepting
                    /\oprec DownLockFree)) /\
          MsgsTo rqTos rule /\ RqReleasing rule /\
          DownLocking rule /\ StateSilent rule.
      
      Definition GoodRqRsRule (rule: Rule oifc) :=
        ImmDownRule rule \/ ImmUpRule rule \/
        RqFwdRule rule \/ RsBackRule rule \/
        RsDownRqDownRule rule.

    End PerObject.

    Definition GoodRqRsObj (obj: Object oifc) :=
      Forall (GoodRqRsRule obj.(obj_idx)) obj.(obj_rules).
    
    Definition GoodRqRsSys (sys: System oifc) :=
      Forall GoodRqRsObj sys.(sys_objs).
    
  End GoodRqRs.

  Section RqUpRsUpComm.

    Definition RqToUpRule (oidx: IdxT) (rule: Rule oifc) :=
      RqFwdRule oidx rule /\
      exists rqFrom rqTos,
        RqUpUp oidx rqFrom rqTos rule.

    Definition RsToUpRule (oidx: IdxT) (rule: Rule oifc) :=
      ImmUpRule oidx rule \/
      (RsBackRule rule /\
       exists rssFrom rsbTo,
         FootprintReleasingDown rule rssFrom rsbTo).
    
    Definition RqUpRsUpOkObj (obj: Object oifc) :=
      forall rqUpRule rsUpRule,
        In rqUpRule obj.(obj_rules) -> RqToUpRule obj.(obj_idx) rqUpRule ->
        In rsUpRule obj.(obj_rules) -> RsToUpRule obj.(obj_idx) rsUpRule ->
        NonConflictingR rqUpRule rsUpRule.

    Definition RqUpRsUpOkSys (sys: System oifc) :=
      Forall RqUpRsUpOkObj sys.(sys_objs).
    
  End RqUpRsUpComm.

  Definition RqRsSys (sys: System oifc) :=
    GoodRqRsSys sys /\
    RqUpRsUpOkSys sys.
  
End RqRsTopo.

Close Scope list.
Close Scope fmap.

