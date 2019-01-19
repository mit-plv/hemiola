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

  Definition UpLockFreeSuff (rule: Rule oifc) :=
    forall ost orq1 orq2 rins,
      rule.(rule_precond) ost orq1 rins -> orq2@[upRq] = None ->
      rule.(rule_precond) ost orq2 rins.

  Definition DownLockFreeSuff (rule: Rule oifc) :=
    forall ost orq1 orq2 rins,
      rule.(rule_precond) ost orq1 rins -> orq2@[downRq] = None ->
      rule.(rule_precond) ost orq2 rins.

  (** Upward-requested *)
  Definition FootprintedUp (orq: ORq Msg) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists rqi,
      orq@[upRq] = Some rqi /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (** Downward-requested *)
  Definition FootprintedDown (orq: ORq Msg) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists rqi,
      orq@[downRq] = Some rqi /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (** A rule making an upward request. *)
  Definition FootprintingUp (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    forall ost orq mins,
    exists (rqm: Id Msg) rqi,
      snd (fst (rule.(rule_trs) ost orq mins)) = orq+[upRq <- rqi] /\
      mins = [rqm] /\ rqi.(rqi_msg) = valOf rqm /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (** A rule making downward requests. *)
  Definition FootprintingDown (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    forall ost orq mins,
    exists (rqm: Id Msg) rqi,
      snd (fst (rule.(rule_trs) ost orq mins)) = orq+[downRq <- rqi] /\
      mins = [rqm] /\ rqi.(rqi_msg) = valOf rqm /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.
  
  (** A rule handling a _downward response_. *)
  Definition FootprintReleasingUp (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    (rule.(rule_precond) ->oprec (fun _ orq _ => FootprintedUp orq rssFrom rsbTo)) /\
    (forall ost orq mins,
        snd (fst (rule.(rule_trs) ost orq mins)) = orq -[upRq]).

  (** A rule handling _upward responses_. *)
  Definition FootprintReleasingDown (rule: Rule oifc) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    (rule.(rule_precond) ->oprec (fun _ orq _ => FootprintedDown orq rssFrom rsbTo)) /\
    (forall ost orq mins,
        snd (fst (rule.(rule_trs) ost orq mins)) = orq -[downRq]).

  Definition FootprintingUpToDown (rule: Rule oifc)
             (rssFrom nrssFrom: list IdxT) (rsbTo: IdxT) :=
    (rule.(rule_precond) ->oprec (fun _ orq _ => FootprintedUp orq rssFrom rsbTo)) /\
    forall ost orq mins,
    exists (rqm: Id Msg) rqi,
      snd (fst (rule.(rule_trs) ost orq mins)) = orq-[upRq]+[downRq <- rqi] /\
      mins = [rqm] /\ rqi.(rqi_msg) = valOf rqm /\
      rqi.(rqi_minds_rss) = nrssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.
  
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
    forall ost orq mins,
      let norq := snd (fst (rule.(rule_trs) ost orq mins)) in
      norq = orq.

  Definition MsgOutsOrthORq (rule: Rule oifc): Prop :=
    forall ost orq1 orq2 mins,
      snd (rule.(rule_trs) ost orq1 mins) =
      snd (rule.(rule_trs) ost orq2 mins).
  
End Conditions.

Section RqRsTopo.
  Variables (dtr: DTree) (oifc: OStateIfc).

  Definition rqEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (upEdgesFrom dtr oidx).

  Definition rsEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (tail (upEdgesFrom dtr oidx)).

  Definition edgeDownTo (oidx: IdxT): option IdxT :=
    hd_error (downEdgesTo dtr oidx).

  Definition FootprintUpOk (oidx: IdxT) (rqFrom rqTo rsFrom rsbTo: IdxT) :=
    exists cidx,
      parentIdxOf dtr cidx = Some oidx /\
      rqEdgeUpFrom cidx = Some rqFrom /\
      rqEdgeUpFrom oidx = Some rqTo /\
      edgeDownTo oidx = Some rsFrom /\
      edgeDownTo cidx = Some rsbTo.

  Definition RqRsDownMatch (oidx: IdxT) (rqTos: list IdxT) (rssFrom: list IdxT)
             (P: IdxT (* each child index *) -> Prop) :=
    List.length rqTos = List.length rssFrom /\
    Forall (fun rqrs =>
              exists cidx,
                P cidx /\
                parentIdxOf dtr cidx = Some oidx /\
                edgeDownTo cidx = Some (fst rqrs) /\
                rsEdgeUpFrom cidx = Some (snd rqrs))
           (combine rqTos rssFrom).
  
  Definition FootprintUpDownOk (oidx: IdxT)
             (rqFrom: IdxT) (rqTos: list IdxT)
             (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists upCIdx,
      parentIdxOf dtr upCIdx = Some oidx /\
      rqEdgeUpFrom upCIdx = Some rqFrom /\
      edgeDownTo upCIdx = Some rsbTo /\
      RqRsDownMatch oidx rqTos rssFrom (fun cidx => cidx <> upCIdx).

  Definition FootprintDownDownOk (oidx: IdxT)
             (rqFrom: IdxT) (rqTos: list IdxT)
             (rssFrom: list IdxT) (rsbTo: IdxT) :=
    edgeDownTo oidx = Some rqFrom /\
    rsEdgeUpFrom oidx = Some rsbTo /\
    RqRsDownMatch oidx rqTos rssFrom (fun _ => True).

  Lemma RqRsDownMatch_rq_In:
    forall oidx rqTos rssFrom P,
      RqRsDownMatch oidx rqTos rssFrom P ->
      forall rq,
        In rq rqTos ->
        exists cidx, P cidx /\
                     parentIdxOf dtr cidx = Some oidx /\
                     edgeDownTo cidx = Some rq.
  Proof.
    induction rqTos; simpl; intros; [elim H0|].
    destruct H0; subst.
    - red in H; dest.
      destruct rssFrom as [|rsFrom rssFrom]; [discriminate|].
      simpl in H0; inv H0.
      destruct H3 as [cidx ?]; dest; simpl in *.
      exists cidx; repeat split; assumption.
    - red in H; dest.
      destruct rssFrom as [|rsFrom rssFrom]; [discriminate|].
      simpl in H; inv H.
      simpl in H1; inv H1.
      eapply IHrqTos; eauto.
      split; eauto.
  Qed.

  Lemma RqRsDownMatch_rs_In:
    forall oidx rssFrom rqTos P,
      RqRsDownMatch oidx rqTos rssFrom P ->
      forall rs,
        In rs rssFrom ->
        exists cidx, P cidx /\
                     parentIdxOf dtr cidx = Some oidx /\
                     rsEdgeUpFrom cidx = Some rs.
  Proof.
    induction rssFrom; simpl; intros; [elim H0|].
    destruct H0; subst.
    - red in H; dest.
      destruct rqTos as [|rqTo rqTos]; [discriminate|].
      simpl in H0; inv H0.
      destruct H3 as [cidx ?]; dest; simpl in *.
      exists cidx; repeat split; assumption.
    - red in H; dest.
      destruct rqTos as [|rqTo rqTos]; [discriminate|].
      simpl in H; inv H.
      simpl in H1; inv H1.
      eapply IHrssFrom; eauto.
      split; eauto.
  Qed.

  Section RqRsDTree.

    Definition RqRsChnsOnDTree (sys: System oifc) :=
      forall oidx ups downs pidx,
        parentChnsOf dtr oidx = Some (ups, downs, pidx) ->
        exists rqUp rsUp down,
          ups = [rqUp; rsUp] /\ downs = [down] /\
          SubList [rqUp; rsUp] sys.(sys_minds) /\
          SubList [down] sys.(sys_minds).

    Definition RqRsDTree (sys: System oifc) :=
      WfDTree dtr /\ RqRsChnsOnDTree sys.
    
  End RqRsDTree.
  
  Section GoodRqRs.
    
    Section PerObject.
      Variable (oidx: IdxT).
      
      (* A rule making an immediate response to one of its children *)
      Definition ImmDownRule (rule: Rule oifc) :=
        exists cidx rqFrom rsTo,
          rqEdgeUpFrom cidx = Some rqFrom /\
          edgeDownTo cidx = Some rsTo /\
          parentIdxOf dtr cidx = Some oidx /\
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
        UpLockFreeSuff rule /\
        exists rqTo rsFrom rsbTo,
          rqTos = [rqTo] /\
          FootprintUpOk oidx rqFrom rqTo rsFrom rsbTo /\
          FootprintingUp rule [rsFrom] rsbTo /\
          FootprintDownSilent rule.

      Definition RqUpDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        (rule.(rule_precond) ->oprec DownLockFree) /\
        DownLockFreeSuff rule /\
        exists rssFrom rsbTo,
          FootprintUpDownOk oidx rqFrom rqTos rssFrom rsbTo /\
          FootprintingDown rule rssFrom rsbTo /\
          FootprintUpSilent rule.

      Definition RqDownDown (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        (rule.(rule_precond) ->oprec DownLockFree) /\
        DownLockFreeSuff rule /\
        exists rssFrom rsbTo,
          FootprintDownDownOk oidx rqFrom rqTos rssFrom rsbTo /\
          FootprintingDown rule rssFrom rsbTo /\
          FootprintUpSilent rule.

      Definition RqFwdFromTo (rqFrom: IdxT) (rqTos: list IdxT) (rule: Rule oifc) :=
        (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec RqAccepting)) /\
        MsgsTo rqTos rule /\ RqReleasing rule /\ StateSilent rule.

      Definition RqFwdRule (rule: Rule oifc) :=
        MsgOutsOrthORq rule /\
        exists rqFrom rqTos,
          (RqUpUp rqFrom rqTos rule \/
           RqUpDown rqFrom rqTos rule \/
           RqDownDown rqFrom rqTos rule) /\
          RqFwdFromTo rqFrom rqTos rule.

      Definition RsBackFromTo (rssFrom: list IdxT) (rsbTo: IdxT) (rule: Rule oifc) :=
        (rule.(rule_precond) ->oprec (MsgsFrom rssFrom /\oprec RsAccepting)) /\
        MsgsTo [rsbTo] rule /\ RsReleasing rule.
      
      Definition RsBackRule (rule: Rule oifc) :=
        exists rssFrom rsbTo,
          ((FootprintReleasingUp rule rssFrom rsbTo /\ FootprintDownSilent rule) \/
           (FootprintReleasingDown rule rssFrom rsbTo /\ FootprintUpSilent rule)) /\
          RsBackFromTo rssFrom rsbTo rule.

      Definition FootprintUpToDown (rule: Rule oifc) (rsFrom: IdxT) (rqTos: list IdxT) :=
        exists rqFrom rsbTo nrssFrom,
          FootprintingUpToDown rule [rsFrom] nrssFrom rsbTo /\
          FootprintUpDownOk oidx rqFrom rqTos nrssFrom rsbTo.
      
      Definition RsDownRqDownRule (rule: Rule oifc) :=
        exists rsFrom rqTos,
          FootprintUpToDown rule rsFrom rqTos /\
          edgeDownTo oidx = Some rsFrom /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rsFrom]
                    /\oprec RsAccepting
                    /\oprec DownLockFree)) /\
          MsgsTo rqTos rule /\ RqReleasing rule /\
          StateSilent rule.
      
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
      exists rqFrom rqTos,
        RqUpUp oidx rqFrom rqTos rule /\
        MsgOutsOrthORq rule /\
        RqFwdFromTo rqFrom rqTos rule.

    Definition RsToUpRule (oidx: IdxT) (rule: Rule oifc) :=
      ImmUpRule oidx rule \/
      (exists rssFrom rsbTo,
          FootprintReleasingDown rule rssFrom rsbTo /\
          RsBackFromTo rssFrom rsbTo rule).
    
    Definition RqUpRsUpOkObj (obj: Object oifc) :=
      forall rqUpRule rsUpRule,
        In rqUpRule obj.(obj_rules) -> RqToUpRule obj.(obj_idx) rqUpRule ->
        In rsUpRule obj.(obj_rules) -> RsToUpRule obj.(obj_idx) rsUpRule ->
        NonConflictingR rqUpRule rsUpRule.

    Definition RqUpRsUpOkSys (sys: System oifc) :=
      Forall RqUpRsUpOkObj sys.(sys_objs).
    
  End RqUpRsUpComm.

  Definition RqRsSys (sys: System oifc) :=
    RqRsDTree sys /\
    GoodRqRsSys sys /\
    RqUpRsUpOkSys sys.
  
End RqRsTopo.

Close Scope list.
Close Scope fmap.

