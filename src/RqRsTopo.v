Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section RqRsTopo.
  Context {oifc: OStateIfc}.
  Variable (dtr: DTree) (sys: System oifc).

  Definition rqEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (upEdgesFrom dtr oidx).

  Definition rsEdgeUpFrom (oidx: IdxT): option IdxT :=
    hd_error (tail (upEdgesFrom dtr oidx)).

  Definition edgeDownTo (oidx: IdxT): option IdxT :=
    hd_error (downEdgesTo dtr oidx).

  (** General predicates *)

  Definition RulePrecSat (rule: Rule oifc) (prec: OPrec oifc): Prop :=
    rule.(rule_precond) ->oprec prec.

  Definition RulePostSat (rule: Rule oifc)
             (pp: OState oifc -> ORq Msg -> list (Id Msg) ->
                  OState oifc -> ORq Msg -> list (Id Msg) -> Prop): Prop :=
    forall post porq rins,
      rule.(rule_precond) post porq rins ->
      forall nost norq routs,
        rule.(rule_trs) post porq rins = (nost, norq, routs) ->
        pp post porq rins nost norq routs.

  Local Notation "RULE '#prec' '<=' P" := (RulePrecSat RULE P) (at level 0).
  Local Notation "RULE '#post' '<=' PP" := (RulePostSat RULE PP) (at level 0).
  
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
    rule#post <=
    fun post porq rins nost norq routs =>
      Forall (fun idm => msg_type (valOf idm) = MRq) routs.

  Definition RsReleasing (rule: Rule oifc) :=
    rule#post <=
    fun post porq rins nost norq routs =>
      Forall (fun idm => msg_type (valOf idm) = MRs) routs.

  (** Preconditions to check the lock state *)
  Definition upRq := 0.
  Definition downRq := 1.

  Definition UpLockFreeORq (orq: ORq Msg) :=
    orq@[upRq] = None.

  Definition DownLockFreeORq (orq: ORq Msg) :=
    orq@[downRq] = None.

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
  
  Definition StateSilent (rule: Rule oifc): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      post = nost.

  Definition FootprintUpSilent (rule: Rule oifc): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      porq@[upRq] = norq@[upRq].

  Definition FootprintDownSilent (rule: Rule oifc): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      porq@[downRq] = norq@[downRq].

  Definition FootprintSilent (rule: Rule oifc): Prop :=
    rule#post <=
    fun post porq rins nost norq routs =>
      porq = norq.

  Definition MsgOutsOrthORq (rule: Rule oifc): Prop :=
    forall ost orq1 orq2 mins,
      snd (rule.(rule_trs) ost orq1 mins) =
      snd (rule.(rule_trs) ost orq2 mins).

  (** A rule making an upward request. *)
  Definition FootprintingUp (porq norq: ORq Msg) (rqfm: Msg) (rsFrom rsbTo: IdxT) :=
    exists rqi,
      norq = porq+[upRq <- rqi] /\
      rqi.(rqi_msg) = rqfm /\
      rqi.(rqi_minds_rss) = [rsFrom] /\
      rqi.(rqi_midx_rsb) = rsbTo.

  (** A rule making downward requests. *)
  Definition FootprintingDown (porq norq: ORq Msg) (rqfm: Msg)
             (rssFrom: list IdxT) (rsbTo: IdxT) :=
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

  Definition FootprintReleasingUpPost
             (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
             (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
    exists rssFrom rsbTo rsm,
      FootprintedUp porq rssFrom rsbTo /\
      norq = porq -[upRq] /\
      idsOf rins = rssFrom /\
      routs = [(rsbTo, rsm)].

  (** A rule handling a _downward response_. *)
  Definition FootprintReleasingUp (rule: Rule oifc) :=
    rule#post <= FootprintReleasingUpPost.

  Definition FootprintReleasingDownPost
             (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
             (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
    exists rssFrom rsbTo rsm,
      FootprintedDown porq rssFrom rsbTo /\
      norq = porq -[downRq] /\
      idsOf rins = rssFrom /\
      routs = [(rsbTo, rsm)].

  (** A rule handling _upward responses_. *)
  Definition FootprintReleasingDown (rule: Rule oifc) :=
    rule#post <= FootprintReleasingDownPost.
  
  Definition FootprintUpOk (oidx: IdxT) (rqFrom rqTo rsFrom rsbTo: IdxT) :=
    exists cidx,
      parentIdxOf dtr cidx = Some oidx /\
      rqEdgeUpFrom cidx = Some rqFrom /\
      rqEdgeUpFrom oidx = Some rqTo /\
      edgeDownTo oidx = Some rsFrom /\
      edgeDownTo cidx = Some rsbTo.

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
             (rqFrom: IdxT) (rqTos: list IdxT)
             (rssFrom: list IdxT) (rsbTo: IdxT) :=
    exists upCIdx upCObj,
      In upCObj sys.(sys_objs) /\
      upCObj.(obj_idx) = upCIdx /\
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

  Section RqRsDTree.

    Definition RqRsChnsOnDTree :=
      forall oidx root pidx,
        parentChnsOf oidx dtr = Some (root, pidx) ->
        exists rqUp rsUp down,
          root.(dmc_ups) = [rqUp; rsUp] /\ root.(dmc_downs) = [down].

    Definition RqRsChnsOnSystem :=
      forall oidx root pidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
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

      Definition ImmDownOk (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists cidx rqFrom rqm rsTo rsm,
          rqEdgeUpFrom cidx = Some rqFrom /\
          edgeDownTo cidx = Some rsTo /\
          parentIdxOf dtr cidx = Some oidx /\
          rins = [(rqFrom, rqm)] /\
          routs = [(rsTo, rsm)].
      
      (* A rule making an immediate response to one of its children *)
      Definition ImmDownRule (rule: Rule oifc) :=
        rule#prec <= RqAccepting /\
        rule#prec <= DownLockFree /\
        rule#prec <= UpLockFree /\
        RsReleasing rule /\
        FootprintSilent rule /\
        rule#post <= ImmDownOk.

      Definition ImmUpOk (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqFrom rqm rsTo rsm,
          edgeDownTo oidx = Some rqFrom /\
          rsEdgeUpFrom oidx = Some rsTo /\
          rins = [(rqFrom, rqm)] /\
          routs = [(rsTo, rsm)].

      (* A rule making an immediate response to the parent *)
      Definition ImmUpRule (rule: Rule oifc) :=
        rule#prec <= RqAccepting /\
        rule#prec <= DownLockFree /\
        RsReleasing rule /\
        FootprintSilent rule /\
        rule#post <= ImmUpOk.

      Definition RqUpUpOk (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqFrom rqfm rqTo rqtm rsFrom rsbTo,
          FootprintingUp porq norq rqfm rsFrom rsbTo /\
          FootprintUpOk oidx rqFrom rqTo rsFrom rsbTo /\
          rins = [(rqFrom, rqfm)] /\
          routs = [(rqTo, rqtm)].
      
      Definition RqUpUp (rule: Rule oifc) :=
        rule#prec <= UpLockFree /\
        FootprintDownSilent rule /\
        UpLockFreeSuff rule /\
        rule#post <= RqUpUpOk.

      Definition RqUpDownOk (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqFrom rqfm rqTos rssFrom rsbTo,
          FootprintingDown porq norq rqfm rssFrom rsbTo /\
          FootprintUpDownOk oidx rqFrom rqTos rssFrom rsbTo /\
          rins = [(rqFrom, rqfm)] /\
          idsOf routs = rqTos.

      Definition RqUpDown (rule: Rule oifc) :=
        rule#prec <= DownLockFree /\
        FootprintUpSilent rule /\
        DownLockFreeSuff rule /\
        rule#post <= RqUpDownOk.

      Definition RqDownDownOk (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rqFrom rqfm rqTos rssFrom rsbTo,
          FootprintingDown porq norq rqfm rssFrom rsbTo /\
          FootprintDownDownOk oidx rqFrom rqTos rssFrom rsbTo /\
          rins = [(rqFrom, rqfm)] /\
          idsOf routs = rqTos.
      
      Definition RqDownDown (rule: Rule oifc) :=
        rule#prec <= DownLockFree /\
        FootprintUpSilent rule /\
        DownLockFreeSuff rule /\
        rule#post <= RqDownDownOk.

      Definition RqFwdRuleCommon (rule: Rule oifc) :=
        rule#prec <= RqAccepting /\
        RqReleasing rule /\
        StateSilent rule /\
        MsgOutsOrthORq rule.

      (* A rule forwarding a request. Request-forwarding rules should satisfy
       * following two properties:
       * 1) No RqDown-RqUp in order to control iteration order.
       * 2) Correct footprinting (to [ORq])
       *)
      Definition RqFwdRule (rule: Rule oifc) :=
        RqFwdRuleCommon rule /\
        (RqUpUp rule \/ RqUpDown rule \/ RqDownDown rule).
      
      Definition RsBackRuleCommon (rule: Rule oifc) :=
        rule#prec <= RsAccepting /\ RsReleasing rule.

      Definition RsDownDown (rule: Rule oifc) :=
        (* Below [DownLockFree] precondition is very important to ensure correctness. *)
        rule#prec <= DownLockFree /\
        FootprintReleasingUp rule /\
        FootprintDownSilent rule.

      Definition RsUp (rule: Rule oifc) :=
        FootprintReleasingDown rule /\
        FootprintUpSilent rule.

      Definition RsBackRule (rule: Rule oifc) :=
        (RsDownDown rule \/ RsUp rule) /\
        RsBackRuleCommon rule.

      Definition RsDownRqDownOk (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
                 (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)) :=
        exists rsFrom rsm rqTos rqOrig rsbTo rssFrom,
          FootprintUpDownOk oidx rqOrig rqTos rssFrom rsbTo /\
          FootprintingUpToDown porq norq rssFrom /\
          FootprintedUp porq [rsFrom] rsbTo /\
          edgeDownTo oidx = Some rsFrom /\
          rins = [(rsFrom, rsm)] /\
          idsOf routs = rqTos.
      
      Definition RsDownRqDownRule (rule: Rule oifc) :=
        rule#prec <= RsAccepting /\
        rule#prec <= DownLockFree /\
        RqReleasing rule /\
        StateSilent rule /\
        rule#post <= RsDownRqDownOk.
      
      Definition GoodRqRsRule (rule: Rule oifc) :=
        ImmDownRule rule \/ ImmUpRule rule \/
        RqFwdRule rule \/ RsBackRule rule \/
        RsDownRqDownRule rule.

    End PerObject.

    Definition GoodRqRsObj (obj: Object oifc) :=
      Forall (GoodRqRsRule obj.(obj_idx)) obj.(obj_rules).

    Definition GoodRqRsSys :=
      Forall GoodRqRsObj sys.(sys_objs).
    
  End GoodRqRs.

  Section RqUpRsUpComm.

    Definition RqToUpRule (oidx: IdxT) (rule: Rule oifc) :=
      RqFwdRuleCommon rule /\ RqUpUp oidx rule.

    Definition RsToUpRule (oidx: IdxT) (rule: Rule oifc) :=
      ImmUpRule oidx rule \/
      (RsUp rule /\ RsBackRuleCommon rule).
    
    Definition RqUpRsUpOkObj (obj: Object oifc) :=
      forall rqUpRule rsUpRule,
        In rqUpRule obj.(obj_rules) -> RqToUpRule obj.(obj_idx) rqUpRule ->
        In rsUpRule obj.(obj_rules) -> RsToUpRule obj.(obj_idx) rsUpRule ->
        NonConflictingR rqUpRule rsUpRule.

    Definition RqUpRsUpOkSys :=
      Forall RqUpRsUpOkObj sys.(sys_objs).
    
  End RqUpRsUpComm.

  Section GoodExtRss.

    Definition GoodExtRssRule (rule: Rule oifc) :=
      forall post porq mins nost norq mouts,
        rule_precond rule post porq mins ->
        rule_trs rule post porq mins = (nost, norq, mouts) ->
        forall mout,
          In mout mouts ->
          In (idOf mout) sys.(sys_merss) ->
          msg_type (valOf mout) = MRs.

    Definition GoodExtRssObj (obj: Object oifc) :=
      Forall GoodExtRssRule obj.(obj_rules).

    Definition GoodExtRssSys :=
      Forall GoodExtRssObj sys.(sys_objs).

  End GoodExtRss.

  Definition GoodRqRsInterfSys :=
    RqUpRsUpOkSys /\ GoodExtRssSys.

  Definition RqRsSys :=
    RqRsDTree /\ GoodRqRsSys /\ GoodRqRsInterfSys.
  
End RqRsTopo.

Hint Unfold MsgsFrom MsgIdsFrom MsgsFromORq MsgsTo
     RqAccepting RsAccepting RqReleasing RsReleasing
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

Hint Unfold getRq addRq removeRq : RuleConds.

Close Scope list.
Close Scope fmap.

