Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Section RqRsTopo.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree) (sys: System)
            (oinvs: IdxT -> ObjInv).

  Definition rqEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (upEdgesFrom dtr oidx).

  Definition rsEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (tail (upEdgesFrom dtr oidx)).

  Definition edgeDownTo (oidx: IdxT): option IdxT :=
    hd_error (downEdgesTo dtr oidx).

  (** General predicates *)

  Definition RulePrecSat (rule: Rule) (prec: OPrec): Prop :=
    rule.(rule_precond) ->oprec prec.

  Definition RulePostSat (rule: Rule)
             (pp: OState -> ORq Msg -> list (Id Msg) ->
                  OState -> ORq Msg -> list (Id Msg) -> Prop): Prop :=
    forall post porq rins,
      rule.(rule_precond) post porq rins ->
      forall nost norq routs,
        rule.(rule_trs) post porq rins = (nost, norq, routs) ->
        pp post porq rins nost norq routs.

  Local Notation "RULE '#prec' '<=' P" := (RulePrecSat RULE P) (at level 0).
  Local Notation "RULE '#post' '<=' PP" := (RulePostSat RULE PP) (at level 0).
  
  (** Preconditions and postconditions dealing with messages. *)
  Definition RqAccepting: OPrec :=
    fun _ _ mins =>
      Forall (fun idm => msg_type (valOf idm) = MRq) mins.

  Definition RsAccepting: OPrec :=
    fun _ _ mins =>
      Forall (fun idm => msg_type (valOf idm) = MRs) mins.

  Definition RqReleasing (rule: Rule) :=
    rule#post <=
    fun post porq rins nost norq routs =>
      Forall (fun idm => msg_type (valOf idm) = MRq) routs.

  Definition RsReleasing (rule: Rule) :=
    rule#post <=
    fun post porq rins nost norq routs =>
      Forall (fun idm => msg_type (valOf idm) = MRs) routs.

  (** Preconditions to check the lock state *)
  Definition upRq: IdxT := 0.
  Definition downRq: IdxT := 1.

  Definition UpLockFreeORq (orq: ORq Msg) :=
    orq@[upRq] = None.

  Definition DownLockFreeORq (orq: ORq Msg) :=
    orq@[downRq] = None.

  Definition UpLockFree: OPrec :=
    fun ost orq mins => UpLockFreeORq orq.

  Definition DownLockFree: OPrec :=
    fun ost orq mins => DownLockFreeORq orq.

  Definition UpLockFreeSuff (rule: Rule) :=
    forall ost orq1 orq2 rins,
      rule.(rule_precond) ost orq1 rins -> orq2@[upRq] = None ->
      rule.(rule_precond) ost orq2 rins.

  Definition DownLockFreeSuff (rule: Rule) :=
    forall ost orq1 orq2 rins,
      rule.(rule_precond) ost orq1 rins -> orq2@[downRq] = None ->
      rule.(rule_precond) ost orq2 rins.
  
  Definition StateSilent (rule: Rule): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      post = nost.

  Definition FootprintUpSilent (rule: Rule): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      porq@[upRq] = norq@[upRq].

  Definition FootprintDownSilent (rule: Rule): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      porq@[downRq] = norq@[downRq].

  Definition FootprintSilent (rule: Rule): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      porq = norq.

  Definition MsgOutsOrthORq (rule: Rule): Prop :=
    forall ost orq1 orq2 mins,
      snd (rule.(rule_trs) ost orq1 mins) =
      snd (rule.(rule_trs) ost orq2 mins).

  (** A rule making an upward request. *)
  Definition FootprintingUp (porq norq: ORq Msg)
             (rqfm: option Msg) (rsFrom: IdxT) (rsbTo: option IdxT) :=
    exists rqi,
      norq = porq+[upRq <- rqi] /\
      rqi.(rqi_msg) = rqfm /\
      rqi.(rqi_minds_rss) = [rsFrom] /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (** A rule making downward requests. *)
  Definition FootprintingDown (porq norq: ORq Msg) (rqfm: option Msg)
             (rssFrom: list IdxT) (rsbTo: option IdxT) :=
    exists rqi,
      norq = porq+[downRq <- rqi] /\
      rqi.(rqi_msg) = rqfm /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.

  Definition FootprintingUpToDown (porq norq: ORq Msg) (nrssFrom: list IdxT) :=
    exists prqi nrqi,
      porq@[upRq] = Some prqi /\
      norq = porq-[upRq]+[downRq <- nrqi] /\
      nrqi.(rqi_msg) = prqi.(rqi_msg) /\
      nrqi.(rqi_minds_rss) = nrssFrom /\
      nrqi.(rqi_midx_rsb) = prqi.(rqi_midx_rsb).
  
  (** Upward-requested *)
  Definition FootprintedUp (orq: ORq Msg) (rssFrom: list IdxT)
             (rsbTo: option IdxT) :=
    exists rqi,
      orq@[upRq] = Some rqi /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (** Downward-requested *)
  Definition FootprintedDown (orq: ORq Msg) (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists rqi,
      orq@[downRq] = Some rqi /\
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = Some rsbTo.

  Definition FootprintReleasingUpPost
             (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
             (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
    exists rssFrom rsbTo,
      FootprintedUp porq rssFrom rsbTo /\
      norq = porq -[upRq] /\
      idsOf rins = rssFrom /\
      (match rsbTo with
       | Some rsbTo => idsOf routs = [rsbTo]
       | None => routs = nil
       end).

  (** A rule handling a _downward response_. *)
  Definition FootprintReleasingUp (rule: Rule) :=
    rule#post <= FootprintReleasingUpPost.

  Definition FootprintReleasingDownPost
             (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
             (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
    exists rssFrom rsbTo rsm,
      FootprintedDown porq rssFrom rsbTo /\
      norq = porq -[downRq] /\
      idsOf rins = rssFrom /\
      routs = [(rsbTo, rsm)].

  (** A rule handling _upward responses_. *)
  Definition FootprintReleasingDown (rule: Rule) :=
    rule#post <= FootprintReleasingDownPost.

  Definition FootprintUpOk (oidx: IdxT)
             (rrFrom: option (IdxT * IdxT))
             (rqTo rsFrom: IdxT) :=
      (rrFrom >>=[True]
              (fun rrFrom =>
                 exists cidx,
                   parentIdxOf dtr cidx = Some oidx /\
                   let (rqFrom, rsbTo) := rrFrom in
                   rqEdgeUpFrom cidx = Some rqFrom /\
                   edgeDownTo cidx = Some rsbTo)) /\
      rqEdgeUpFrom oidx = Some rqTo /\
      edgeDownTo oidx = Some rsFrom.

  Definition RqRsDownMatch (oidx: IdxT) (rqTos: list IdxT) (rssFrom: list IdxT)
             (P: IdxT (* each child index *) -> Prop) :=
    rqTos <> nil /\
    List.length rqTos = List.length rssFrom /\
    Forall (fun rqrs =>
              exists cidx,
                P cidx /\
                parentIdxOf dtr cidx = Some oidx /\
                edgeDownTo cidx = Some (fst rqrs) /\
                rsEdgeUpFrom cidx = Some (snd rqrs))
           (combine rqTos rssFrom).
  
  Definition FootprintUpDownOk (oidx: IdxT)
             (rrFrom: option (IdxT * IdxT)) (rqTos: list IdxT)
             (rssFrom: list IdxT) :=
    match rrFrom with
    | Some (rqFrom, rsbTo) =>
      (exists upCIdx upCObj,
          In upCObj sys.(sys_objs) /\
          upCObj.(obj_idx) = upCIdx /\
          parentIdxOf dtr upCIdx = Some oidx /\
          rqEdgeUpFrom upCIdx = Some rqFrom /\
          edgeDownTo upCIdx = Some rsbTo /\
          RqRsDownMatch oidx rqTos rssFrom (fun cidx => cidx <> upCIdx))
    | None =>
      RqRsDownMatch oidx rqTos rssFrom (fun _ => True)
    end.

  Definition FootprintDownDownOk (oidx: IdxT)
             (rqFrom: IdxT) (rqTos: list IdxT)
             (rssFrom: list IdxT) (rsbTo: IdxT) :=
    edgeDownTo oidx = Some rqFrom /\
    rsEdgeUpFrom oidx = Some rsbTo /\
    RqRsDownMatch oidx rqTos rssFrom (fun _ => True).

  Section RqRsDTree.

    Definition RqRsChnsOnDTree :=
      forall oidx root pidx,
        parentChnsOf oidx dtr = Some (root, pidx) ->
        exists rqUp rsUp down,
          root.(dmc_ups) = [rqUp; rsUp] /\ root.(dmc_downs) = [down].

    Definition RqRsChnsOnSystem :=
      forall oidx root pidx,
        In oidx (map obj_idx sys.(sys_objs)) ->
        parentChnsOf oidx dtr = Some (root, pidx) ->
        SubList root.(dmc_ups) sys.(sys_minds) /\
        SubList root.(dmc_downs) sys.(sys_minds).

    Definition ExtRqsOnDTree :=
      forall erq,
        In erq sys.(sys_merqs) ->
        exists eoidx,
          rqEdgeUpFrom eoidx = Some erq.
          
    Definition ExtRssOnDTree :=
      forall ers,
        In ers sys.(sys_merss) ->
        exists eoidx,
          edgeDownTo eoidx = Some ers.

    Definition ExtsOnDTree :=
      ExtRqsOnDTree /\ ExtRssOnDTree.
    
    Definition RqRsDTree :=
      WfDTree dtr /\
      RqRsChnsOnDTree /\
      RqRsChnsOnSystem /\
      ExtsOnDTree.
    
  End RqRsDTree.
  
  Section GoodRqRs.
    
    Section PerObject.
      Variable (oidx: IdxT).

      Definition ImmDownOk (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
        (rins = nil /\ routs = nil) \/
        exists cidx rqFrom rqm rsTo rsm,
          rqEdgeUpFrom cidx = Some rqFrom /\
          edgeDownTo cidx = Some rsTo /\
          parentIdxOf dtr cidx = Some oidx /\
          rins = [(rqFrom, rqm)] /\
          routs = [(rsTo, rsm)].
      
      (* A rule making an immediate response to one of its children *)
      Definition ImmDownRule (rule: Rule) :=
        rule#prec <= RqAccepting /\
        rule#prec <= DownLockFree /\
        rule#prec <= UpLockFree /\
        RsReleasing rule /\
        FootprintSilent rule /\
        rule#post <= ImmDownOk.

      Definition ImmUpOk (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqFrom rqm rsTo rsm,
          edgeDownTo oidx = Some rqFrom /\
          rsEdgeUpFrom oidx = Some rsTo /\
          rins = [(rqFrom, rqm)] /\
          routs = [(rsTo, rsm)].

      (* A rule making an immediate response to the parent *)
      Definition ImmUpRule (rule: Rule) :=
        rule#prec <= RqAccepting /\
        rule#prec <= DownLockFree /\
        RsReleasing rule /\
        FootprintSilent rule /\
        rule#post <= ImmUpOk.

      Definition RqUpUpOk (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqTo rqtm rsFrom,
          ((rins = nil /\
            FootprintingUp porq norq None rsFrom None /\
            FootprintUpOk oidx None rqTo rsFrom) \/
           (exists rsbTo rqFrom rqfm,
               rins = [(rqFrom, rqfm)] /\
               FootprintingUp porq norq (Some rqfm) rsFrom (Some rsbTo) /\
               FootprintUpOk oidx (Some (rqFrom, rsbTo)) rqTo rsFrom)) /\
          routs = [(rqTo, rqtm)].
      
      Definition RqUpUp (rule: Rule) :=
        rule#prec <= UpLockFree /\
        FootprintDownSilent rule /\
        UpLockFreeSuff rule /\
        rule#post <= RqUpUpOk.

      Definition RqUpDownOk (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqTos rssFrom,
          ((rins = nil /\
            FootprintingDown porq norq None rssFrom None /\
            FootprintUpDownOk oidx None rqTos rssFrom) \/
           (exists rqFrom rqfm rsbTo,
               rins = [(rqFrom, rqfm)] /\
               FootprintingDown porq norq (Some rqfm) rssFrom (Some rsbTo) /\
               FootprintUpDownOk oidx (Some (rqFrom, rsbTo)) rqTos rssFrom)) /\
          idsOf routs = rqTos.

      Definition RqUpDown (rule: Rule) :=
        rule#prec <= DownLockFree /\
        FootprintUpSilent rule /\
        DownLockFreeSuff rule /\
        rule#post <= RqUpDownOk.

      Definition RqDownDownOk (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqFrom rqfm rqTos rssFrom rsbTo,
          FootprintingDown porq norq (Some rqfm) rssFrom (Some rsbTo) /\
          FootprintDownDownOk oidx rqFrom rqTos rssFrom rsbTo /\
          rins = [(rqFrom, rqfm)] /\
          idsOf routs = rqTos.
      
      Definition RqDownDown (rule: Rule) :=
        rule#prec <= DownLockFree /\
        FootprintUpSilent rule /\
        DownLockFreeSuff rule /\
        rule#post <= RqDownDownOk.

      Definition RqFwdRuleCommon (rule: Rule) :=
        rule#prec <= RqAccepting /\
        RqReleasing rule /\
        StateSilent rule /\
        MsgOutsOrthORq rule.

      (* A rule forwarding a request. Request-forwarding rules should satisfy
       * following two properties:
       * 1) No RqDown-RqUp in order to control iteration order.
       * 2) Correct footprinting (to [ORq])
       *)
      Definition RqFwdRule (rule: Rule) :=
        RqFwdRuleCommon rule /\
        (RqUpUp rule \/ RqUpDown rule \/ RqDownDown rule).
      
      Definition RsBackRuleCommon (rule: Rule) :=
        rule#prec <= RsAccepting /\ RsReleasing rule.

      Definition RsDownDown (rule: Rule) :=
        (* Below [DownLockFree] precondition is very important to ensure correctness. *)
        rule#prec <= DownLockFree /\
        FootprintReleasingUp rule /\
        FootprintDownSilent rule.

      Definition RsUp (rule: Rule) :=
        FootprintReleasingDown rule /\
        FootprintUpSilent rule.

      Definition RsBackRule (rule: Rule) :=
        (RsDownDown rule \/ RsUp rule) /\
        RsBackRuleCommon rule.

      Definition RsDownRqDownOk (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rsFrom rqTos rqOrig rsbTo rssFrom,
          FootprintUpDownOk oidx (Some (rqOrig, rsbTo)) rqTos rssFrom /\
          FootprintingUpToDown porq norq rssFrom /\
          FootprintedUp porq [rsFrom] (Some rsbTo) /\
          idsOf rins = [rsFrom] /\
          idsOf routs = rqTos.

      Definition RsDownRqDownRule (rule: Rule) :=
        rule#prec <= RsAccepting /\
        rule#prec <= DownLockFree /\
        RqReleasing rule /\
        rule#post <= RsDownRqDownOk.
      
      Definition GoodRqRsRule (rule: Rule) :=
        ImmDownRule rule \/ ImmUpRule rule \/
        RqFwdRule rule \/ RsBackRule rule \/
        RsDownRqDownRule rule.

    End PerObject.

    Definition GoodRqRsObj (obj: Object) :=
      Forall (GoodRqRsRule obj.(obj_idx)) obj.(obj_rules).

    Definition GoodRqRsSys :=
      Forall GoodRqRsObj sys.(sys_objs).
    
  End GoodRqRs.

  Section RqUpRsUpComm.

    Definition RqToUpRule (oidx: IdxT) (rule: Rule) :=
      RqFwdRuleCommon rule /\ RqUpUp oidx rule.

    Definition RsToUpRule (oidx: IdxT) (rule: Rule) :=
      ImmUpRule oidx rule \/
      (RsUp rule /\ RsBackRuleCommon rule).
    
    Definition RqUpRsUpOkObj (obj: Object) (oinv: ObjInv) :=
      forall rqUpRule rsUpRule,
        In rqUpRule obj.(obj_rules) -> RqToUpRule obj.(obj_idx) rqUpRule ->
        In rsUpRule obj.(obj_rules) -> RsToUpRule obj.(obj_idx) rsUpRule ->
        NonConflictingR oinv rqUpRule rsUpRule.

    Definition RqUpRsUpOkSys :=
      Forall (fun obj => RqUpRsUpOkObj obj (oinvs obj.(obj_idx)))
             sys.(sys_objs).
    
  End RqUpRsUpComm.

  Section GoodExtRss.

    Definition GoodExtRssRule (rule: Rule) :=
      forall post porq mins nost norq mouts,
        rule_precond rule post porq mins ->
        rule_trs rule post porq mins = (nost, norq, mouts) ->
        forall mout,
          In mout mouts ->
          In (idOf mout) sys.(sys_merss) ->
          msg_type (valOf mout) = MRs.

    Definition GoodExtRssObj (obj: Object) :=
      Forall GoodExtRssRule obj.(obj_rules).

    Definition GoodExtRssSys :=
      Forall GoodExtRssObj sys.(sys_objs).

  End GoodExtRss.

  Definition GoodRqRsInterfSys :=
    RqUpRsUpOkSys /\ GoodExtRssSys.

  Definition RqRsSys :=
    RqRsDTree /\ GoodRqRsSys /\ GoodRqRsInterfSys.
  
End RqRsTopo.

Arguments FootprintUpDownOk: simpl never.

Hint Unfold RqAccepting RsAccepting RqReleasing RsReleasing
     UpLockFreeORq DownLockFreeORq
     UpLockFree DownLockFree UpLockFreeSuff DownLockFreeSuff
     StateSilent FootprintUpSilent FootprintDownSilent FootprintSilent
     MsgOutsOrthORq FootprintingUp FootprintingDown FootprintingUpToDown
     FootprintedUp FootprintedDown FootprintReleasingUpPost
     FootprintReleasingUp FootprintReleasingDownPost
     FootprintReleasingDown FootprintUpOk RqRsDownMatch
     FootprintUpDownOk FootprintDownDownOk
     ImmDownOk ImmDownRule ImmUpOk ImmUpRule
     RqUpUpOk RqUpUp RqUpDownOk RqUpDown RqDownDownOk
     RqDownDown RqFwdRuleCommon RqFwdRule
     RsBackRuleCommon RsDownDown RsUp RsBackRule
     RsDownRqDownOk RsDownRqDownRule : RuleConds.

Hint Unfold RqToUpRule RsToUpRule : RuleConds.

Hint Unfold getRq addRq addRqS removeRq : RuleConds.

Global Opaque upRq downRq.

Close Scope list.
Close Scope fmap.

