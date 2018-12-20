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

  Definition MsgsFromORq (addr: AddrT) (rqty: IdxT): OPrec oifc :=
    fun _ orq mins =>
      (getRq orq addr rqty)
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

  Definition LockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True]
       (fun aorq => aorq@[upRq] = None /\ aorq@[downRq] = None).

  Definition UpLockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq@[upRq] = None).

  Definition DownLockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq@[downRq] = None).

  Definition UpLocked (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[False] (fun aorq => aorq@[upRq] <> None).

  Definition DownLocked (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[False] (fun aorq => aorq@[downRq] <> None).

  (** TODO: discuss whether it's fine to have a locking mechanism 
   * only for a single address. *)
  Definition UpLockFree0: OPrec oifc :=
    fun ost orq mins => UpLockFree orq O.

  Definition DownLockFree0: OPrec oifc :=
    fun ost orq mins => DownLockFree orq O.

  Definition UpLocking0 (rule: Rule oifc): Prop :=
    forall ost orq mins,
      UpLocked (snd (fst (rule.(rule_trs) ost orq mins))) O.

  Definition DownLocking0 (rule: Rule oifc): Prop :=
    forall ost orq mins,
      DownLocked (snd (fst (rule.(rule_trs) ost orq mins))) O.

  Definition UpReleasing0 (rule: Rule oifc): Prop :=
    forall ost orq mins,
      UpLocked orq O /\
      UpLockFree (snd (fst (rule.(rule_trs) ost orq mins))) O.

  Definition DownReleasing0 (rule: Rule oifc): Prop :=
    forall ost orq mins,
      DownLocked orq O /\
      DownLockFree (snd (fst (rule.(rule_trs) ost orq mins))) O.

  Definition StateUnchanged (rule: Rule oifc): Prop :=
    forall ost orq mins,
      ost = fst (fst (rule.(rule_trs) ost orq mins)).

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

  Section GoodLocking.
    
    Section PerObject.
      Variable (oidx: IdxT).
      
      (** * Rule predicates about which messages to accept *)

      (* A rule handling a request from one of its children *)
      Definition RqFromDownRule (rule: Rule oifc) :=
        exists rqFrom,
          In rqFrom (rqEdgesUpTo oidx) /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)).

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
          DownReleasing0 rule.

      (* A rule handling a response from the parent *)
      Definition RsFromUpRule (rule: Rule oifc) :=
        exists rsFrom,
          edgeDownTo oidx = Some rsFrom /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rsFrom] /\oprec RsAccepting)) /\
          UpReleasing0 rule.

      (** * Rule predicates about which messages to release *)

      (* A rule making requests to some of its children *)
      Definition RqToDownRule (rule: Rule oifc) :=
        exists rqsTo,
          SubList rqsTo (edgesDownFrom oidx) /\ NoDup rqsTo /\
          MsgsTo rqsTo rule /\ RqReleasing rule /\
          (rule.(rule_precond) ->oprec DownLockFree0) /\
          DownLocking0 rule /\
          StateUnchanged rule.

      (* A rule making a request to the parent *)
      Definition RqToUpRule (rule: Rule oifc) :=
        exists rqTo,
          rqEdgeUpFrom oidx = Some rqTo /\
          MsgsTo [rqTo] rule /\ RqReleasing rule /\
          (rule.(rule_precond) ->oprec UpLockFree0) /\
          UpLocking0 rule /\
          StateUnchanged rule.

      (* A rule making a response to one of its children *)
      Definition RsToDownRule (rule: Rule oifc) :=
        exists rsTo,
          In rsTo (edgesDownFrom oidx) /\
          MsgsTo [rsTo] rule /\ RsReleasing rule /\
          (** Below is a crucial locking condition to avoid 
           * incorrect behaviors by interleaving! *)
          (rule.(rule_precond) ->oprec DownLockFree0).
      
      (* A rule making a response to the parent:
       * Note that unlike [RsToDownRule] we don't have any locking condition for
       * any upward responses. If we put [UpLockFree0] here then it's correct
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
        GoodLockingRelease rule.

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
      (** TODO: correct footprinting *)
      Definition RqUpUp (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        In rqFrom (rqEdgesUpTo oidx) /\
        exists rqTo,
          rqTos = [rqTo] /\ rqEdgeUpFrom oidx = Some rqTo.

      (** TODO: correct footprinting *)
      Definition RqUpDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        In rqFrom (rqEdgesUpTo oidx) /\
        SubList rqTos (edgesDownFrom oidx).

      (** TODO: correct footprinting *)
      Definition RqDownDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        In rqFrom (edgesDownFrom oidx) /\
        SubList rqTos (edgesDownFrom oidx).

      Definition RqFwdRule (rule: Rule oifc) :=
        exists rqFrom rqTos,
          (RqUpUp rqFrom rqTos rule \/
           RqUpDown rqFrom rqTos rule \/
           RqDownDown rqFrom rqTos rule) /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)) /\
          MsgsTo rqTos rule /\ RqReleasing rule.

      Definition FootprintMatchUp (rssFrom: list IdxT) (rsbTo: IdxT) (rule: Rule oifc) :=
        rule.(rule_precond)
        ->oprec (fun _ orq _ =>
                   orq@[O] >>=[False]
                      (fun aorq =>
                         exists rqi,
                           aorq@[downRq] = Some rqi /\
                           rqi.(rqi_minds_rss) = rssFrom /\
                           rqi.(rqi_midx_rsb) = rsbTo)).

      Definition FootprintMatchDown (rssFrom: list IdxT) (rsbTo: IdxT) (rule: Rule oifc) :=
        rule.(rule_precond)
        ->oprec (fun _ orq _ =>
                   orq@[O] >>=[False]
                      (fun aorq =>
                         exists rqi,
                           aorq@[upRq] = Some rqi /\
                           rqi.(rqi_minds_rss) = rssFrom /\
                           rqi.(rqi_midx_rsb) = rsbTo)).
      
      Definition RsBackRule (rule: Rule oifc) :=
        exists rssFrom rsbTo,
          (FootprintMatchUp rssFrom rsbTo rule \/
           FootprintMatchDown rssFrom rsbTo rule) /\
          (rule.(rule_precond) ->oprec (MsgsFrom rssFrom /\oprec RsAccepting)) /\
          MsgsTo [rsbTo] rule /\ RsReleasing rule.

      (** TODO: correct footprint modification *)
      Definition FootprintModifying (rsFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        True.

      Definition RsDownRqDownRule (rule: Rule oifc) :=
        exists rsFrom rqTos,
          FootprintModifying rsFrom rqTos rule /\
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

