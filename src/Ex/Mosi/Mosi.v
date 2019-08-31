Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecSv Ex.Template Ex.Mosi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** Design choices:
 * - Multi-level (for arbitrary tree structure)
 * - MOSI
 * - Directory (not snooping)
 * - Invalidate (not update)
 * - Write-back (not write-through)
 * - NINE (non-inclusive non-exclusive)
 *)

Section System.
  Variable (tr: tree).

  Definition topo := fst (tree2Topo tr 0).
  Definition cifc := snd (tree2Topo tr 0).
  
  Definition implValueIdx: Fin.t 3 := F1.
  Definition implStatusIdx: Fin.t 3 := F2.
  Definition implDirIdx: Fin.t 3 := F3.

  Section Directory.
    
    Record DirT: Set :=
      { dir_st: MOSI; (* the summary status for children *)
        dir_owner: IdxT; (* the owner has a status either M or O *)
        dir_sharers: list IdxT
      }.

    Definition dirInit: DirT :=
      {| dir_st := mosiS;
         dir_owner := ii;
         dir_sharers := nil (** FIXME: should be children indices. *) |}.

    Import CaseNotations.
    Definition getDir (oidx: IdxT) (dir: DirT): MOSI :=
      match case dir.(dir_st) on eq_nat_dec default mosiI with
      | mosiM: if idx_dec oidx dir.(dir_owner) then mosiM else mosiI
      | mosiO: if idx_dec oidx dir.(dir_owner) then mosiO else mosiI
      | mosiS: if in_dec idx_dec oidx dir.(dir_sharers)
               then mosiS else mosiI
      | mosiI: mosiI
      end.

    Definition setDirM (oidx: IdxT) :=
      {| dir_st := mosiM;
         dir_owner := oidx;
         dir_sharers := nil |}.

    Definition setDirO (oidx: IdxT) :=
      {| dir_st := mosiO;
         dir_owner := oidx;
         dir_sharers := [oidx] |}.

    Definition setDirS (oinds: list IdxT) :=
      {| dir_st := mosiS;
         dir_owner := ii;
         dir_sharers := oinds |}.
    
    Definition setDirI :=
      {| dir_st := mosiI;
         dir_owner := ii;
         dir_sharers := nil |}.

    Definition addSharer (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := dir.(dir_st);
         dir_owner := dir.(dir_owner);
         dir_sharers := oidx :: dir.(dir_sharers) |}.
    
    Definition removeSharer (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := dir.(dir_st);
         dir_owner := dir.(dir_owner);
         dir_sharers := removeOnce idx_dec oidx dir.(dir_sharers) |}.

    Definition removeOwner (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := mosiS;
         dir_owner := ii;
         dir_sharers := removeOnce idx_dec oidx dir.(dir_sharers) |}.
    
  End Directory.

  Instance ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; MOSI:Type; DirT:Type]%vector |}.

  Definition implOStateInit: OState :=
    (0, (mosiS, (dirInit, tt))).
  
  Definition implOStatesInit: OStates :=
    fold_left (fun m i => m +[i <- implOStateInit])
              (cifc.(c_l1_indices) ++ cifc.(c_li_indices)) [].

  Definition implORqsInit: ORqs Msg :=
    initORqs (cifc.(c_l1_indices) ++ cifc.(c_li_indices)).

  (** A core idea: a "summary" status in each object *)

  Definition summaryOf (ost: OState): MOSI :=
    if Compare_dec.le_gt_dec mosiS ost#[implStatusIdx]
    then ost#[implStatusIdx]
    else ost#[implDirIdx].(dir_st).

  Section Rules.
    Variables (oidx cidx: IdxT).

    Section GetTrs.

      Definition l1GetSImm: Rule :=
        rule.immd[cidx~>0~>0]
        :accepts mosiRqS
        :from cidx
        :requires (fun ost orq mins => mosiS <= ost#[implStatusIdx])
        :transition
           (!|ost, _| --> (ost, {| miv_id := mosiRsS;
                                   miv_value := ost#[implValueIdx]
                                |})).

      Definition liGetSImmOS: Rule :=
        rule.immd[0~>0~>0~~cidx]
        :accepts mosiRqS
        :from cidx
        :requires
           (fun ost orq mins =>
              ost#[implStatusIdx] = mosiS \/ ost#[implStatusIdx] = mosiO)
        :transition
           (!|ost, _|
            --> (ost +#[implDirIdx <- addSharer cidx ost#[implDirIdx]],
                 {| miv_id := mosiRsS;
                    miv_value := ost#[implValueIdx]
                 |})).

      Definition liGetSImmM: Rule :=
        rule.immd[0~>0~>1~~cidx]
        :accepts mosiRqS
        :from cidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mosiM)
        :transition
           (!|ost, _| --> (ost +#[implStatusIdx <- mosiO]
                               +#[implDirIdx <- setDirS [cidx]],
                           {| miv_id := mosiRsS;
                              miv_value := ost#[implValueIdx]
                           |})).

      Definition l1GetSRqUpUp: Rule :=
        rule.rquu[cidx~>0~>1]
        :accepts mosiRqS
        :from cidx
        :me oidx
        :requires (fun ost mins => summaryOf ost = mosiI)
        :transition (!|ost, msg| --> {| miv_id := mosiRqS; miv_value := O |}).

      Definition liGetSRqUpUp: Rule :=
        rule.rquu[0~>1~~cidx]
        :accepts mosiRqS
        :from cidx
        :me oidx
        :requires (fun ost mins => summaryOf ost = mosiI)
        :transition (!|ost, msg| --> {| miv_id := mosiRqS; miv_value := O |}).
      
      Definition l1GetSRsDownDownS: Rule :=
        rule.rsdd[0~>2]
        :accepts mosiRsS
        :holding mosiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implValueIdx <- msg_value min]
                     +#[implStatusIdx <- mosiS],
                 {| miv_id := mosiRsS;
                    miv_value := msg_value min |})).

      Definition liGetSRsDownDownS: Rule :=
        rule.rsdd[0~>2]
        :accepts mosiRsS
        :holding mosiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implDirIdx <- setDirS [objIdxOf rsbTo]],
                 {| miv_id := mosiRsS;
                    miv_value := msg_value min |})).

      Definition liGetSRqUpDownS: Rule :=
        rule.rqud[0~>3~>0~~cidx]
        :accepts mosiRqS
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mosiI)
                  (ost#[implDirIdx].(dir_st) = mosiS))
        :transition
           (!|ost, msg| --> ([hd ii (ost#[implDirIdx].(dir_sharers))],
                             {| miv_id := mosiDownRqS;
                                miv_value := O |})).

      Definition liGetSRqUpDownMO: Rule :=
        rule.rqud[0~>3~>1~~cidx]
        :accepts mosiRqS
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mosiI)
                  (mosiS <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_owner)],
                             {| miv_id := mosiDownRqS;
                                miv_value := O |})).

      (* commonly used *)
      Definition downSImmS: Rule :=
        rule.immu[0~>4~>0]
        :accepts mosiDownRqS
        :me oidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mosiS)
        :transition
           (!|ost, min| --> (ost, {| miv_id := mosiDownRsS;
                                     miv_value := ost#[implValueIdx] |})).

      (* commonly used *)
      Definition downSImmMO: Rule :=
        rule.immu[0~>4~>1]
        :accepts mosiDownRqS
        :me oidx
        :requires (fun ost orq mins => mosiO <= ost#[implStatusIdx])
        :transition
           (!|ost, min| --> (ost +#[implStatusIdx <- mosiO],
                             {| miv_id := mosiDownRsS;
                                miv_value := ost#[implValueIdx] |})).

      Definition liDownSRsUpDownS: Rule :=
        rule.rsud[0~>5~>0]
        :accepts mosiDownRsS
        :holding mosiRqS
        :requires
           (FirstMsg /\ (fun ost orq mins => ost#[implDirIdx].(dir_st) = mosiS))
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                 rsFrom ::= getFirstIdxFromI rssFrom;
                 (ost, {| miv_id := mosiRsS;
                          miv_value := msg_value msg |}))).

      Definition liDownSRsUpDownMO: Rule :=
        rule.rsud[0~>5~>1]
        :accepts mosiDownRsS
        :holding mosiRqS
        :requires
           (FirstMsg /\ (fun ost orq mins => mosiO <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                 rsFrom ::= getFirstIdxFromI rssFrom;
                 (ost +#[implDirIdx
                           <- addSharer (objIdxOf rsbTo) (setDirO (objIdxOf rsFrom))],
                  {| miv_id := mosiRsS;
                     miv_value := msg_value msg |}))).

      Definition liDownSRqDownDownS: Rule :=
        rule.rqdd[0~>6~>0]
        :accepts mosiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mosiI)
                  (ost#[implDirIdx].(dir_st) = mosiS))
        :transition
           (!|ost, msg| --> ([hd ii (ost#[implDirIdx].(dir_sharers))],
                             {| miv_id := mosiDownRqS;
                                miv_value := O |})).

      Definition liDownSRqDownDownMO: Rule :=
        rule.rqdd[0~>6~>1]
        :accepts mosiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mosiI)
                  (mosiO <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_owner)],
                             {| miv_id := mosiDownRqS;
                                miv_value := O |})).

      Definition liDownSRsUpUpS: Rule :=
        rule.rsuu[0~>7~>0]
        :accepts mosiDownRsS
        :holding mosiDownRqS
        :requires
           (FirstMsg /\ (fun ost orq mins => ost#[implDirIdx].(dir_st) = mosiS))
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                 rsFrom ::= getFirstIdxFromI rssFrom;
                 (ost, {| miv_id := mosiDownRsS;
                          miv_value := msg_value msg |}))).

      Definition liDownSRsUpUpMO: Rule :=
        rule.rsuu[0~>7~>1]
        :accepts mosiDownRsS
        :holding mosiDownRqS
        :requires
           (FirstMsg /\ (fun ost orq mins => mosiO <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                 rsFrom ::= getFirstIdxFromI rssFrom;
                 (ost +#[implDirIdx <- setDirO (objIdxOf rsFrom)],
                  {| miv_id := mosiRsS;
                     miv_value := msg_value msg |}))).

    End GetTrs.

    Section SetTrs.

      Definition l1GetMImm: Rule :=
        rule.immd[cidx~>1~>0]
        :accepts mosiRqM
        :from cidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mosiM)
        :transition
           (!|ost, msg|
            --> (ost +#[implValueIdx <- msg_value msg],
                 {| miv_id := mosiRsM;
                    miv_value := O |})).

      Definition liGetMImm: Rule :=
        rule.immd[1~>0~~cidx]
        :accepts mosiRqM
        :from cidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mosiM)
        :transition
           (!|ost, msg| --> (ost +#[implStatusIdx <- mosiI]
                                 +#[implDirIdx <- setDirM cidx],
                             {| miv_id := mosiRsM;
                                miv_value := O |})).

      Definition l1GetMRqUpUp: Rule :=
        rule.rquu[cidx~>1~>1]
        :accepts mosiRqM
        :from cidx
        :me oidx
        :requires (fun ost mins => summaryOf ost < mosiM)
        :transition (!|ost, msg| --> {| miv_id := mosiRqM; miv_value := O |}).

      Definition liGetMRqUpUp: Rule :=
        rule.rquu[1~>1~~cidx]
        :accepts mosiRqM
        :from cidx
        :me oidx
        :requires (fun ost mins => summaryOf ost < mosiM)
        :transition (!|ost, msg| --> {| miv_id := mosiRqM; miv_value := O |}).
      
      Definition l1GetMRsDownDown: Rule :=
        rule.rsdd[1~>2]
        :accepts mosiRsM
        :holding mosiRqM
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implStatusIdx <- mosiM]
                     +#[implValueIdx <- msg_value rq],
                 {| miv_id := mosiRsM;
                    miv_value := O |})).

      (* This is the case where it's possible to directly respond a [mosiRsM]
       * message back since there are no internal sharers to invalidate.
       *)
      Definition liGetMRsDownDownDirI: Rule :=
        rule.rsdd[1~>3]
        :accepts mosiRsM
        :holding mosiRqM
        :requires (fun ost orq mins => ost#[implDirIdx].(dir_st) = mosiI)
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implStatusIdx <- mosiI]
                     +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mosiRsM;
                    miv_value := O |})).

      (* This is the case where internal invalidation is required due to
       * sharers. 
       *)
      Definition liGetMRsDownRqDownDirOS: Rule :=
        rule.rsrq[1~>4]
        :accepts mosiRsM
        :holding mosiRqM
        :me oidx
        :requires (fun ost orq mins =>
                     ost#[implDirIdx].(dir_st) = mosiO \/
                     ost#[implDirIdx].(dir_st) = mosiS)
        :transition
           (!|ost, rq| --> (ost#[implDirIdx].(dir_sharers),
                            {| miv_id := mosiDownRqI;
                               miv_value := O |})).

      Definition liGetMRqUpDownM: Rule :=
        rule.rqud[1~>5~~cidx]
        :accepts mosiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mosiI)
                  (ost#[implDirIdx].(dir_st) = mosiM))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_owner)],
                             {| miv_id := mosiDownRqI;
                                miv_value := O |})).

      Definition liDownIRsUpDown: Rule :=
        rule.rsud[1~>6]
        :accepts mosiDownRsI
        :holding mosiRqM
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
              --> (ost +#[implStatusIdx <- mosiI]
                       +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                   {| miv_id := mosiRsM;
                      miv_value := O |})).

      Definition l1DownIImm: Rule :=
        rule.immu[1~>7]
        :accepts mosiDownRqI
        :me oidx
        :requires (fun ost orq mins => mosiS <= ost#[implStatusIdx])
        :transition
           (!|ost, min| --> (ost +#[implStatusIdx <- mosiI],
                              {| miv_id := mosiDownRsI;
                                 miv_value := O |})).

      Definition liDownIImm: Rule :=
        rule.immu[1~>8]
        :accepts mosiDownRqI
        :me oidx
        :requires (fun ost orq mins => ost#[implDirIdx].(dir_st) = mosiI)
        :transition
           (!|ost, min| --> (ost +#[implStatusIdx <- mosiI],
                             {| miv_id := mosiDownRsI;
                                miv_value := O |})).

      Definition liDownIRqDownDownDirOS: Rule :=
        rule.rqdd[1~>9]
        :accepts mosiDownRqI
        :me oidx
        :requires (fun ost mins =>
                     ost#[implDirIdx].(dir_st) = mosiS \/
                     ost#[implDirIdx].(dir_st) = mosiO)
        :transition
           (!|ost, msg| --> (ost#[implDirIdx].(dir_sharers),
                             {| miv_id := mosiDownRqI;
                                miv_value := O |})).

      Definition liDownIRqDownDownDirM: Rule :=
        rule.rqdd[1~>10]
        :accepts mosiDownRqI
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mosiI)
                  (ost#[implDirIdx].(dir_st) = mosiM))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_owner)],
                              {| miv_id := mosiDownRqI;
                                 miv_value := O |})).

      Definition liDownIRsUpUp: Rule :=
        rule.rsuu[1~>11]
        :accepts mosiDownRsI
        :holding mosiDownRqI
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[implStatusIdx <- mosiI]
                     +#[implDirIdx <- setDirI],
                   {| miv_id := mosiDownRsI;
                      miv_value := O |})).

      Definition memGetMRqUpDown: Rule :=
        rule.rqud[1~>12~~cidx]
        :accepts mosiRqM
        :from cidx
        :me oidx
        :requires (fun ost mins => ost#[implStatusIdx] < mosiM)
        :transition
           (!|ost, msg| --> (ost#[implDirIdx].(dir_sharers),
                             {| miv_id := mosiDownRqI;
                                miv_value := O |})).

    End SetTrs.

    Section EvictTrs.

      Definition putRqUpUp: Rule :=
        rule.rqu[2~>0]
        :me oidx
        :requires (fun ost mins => ost#[implStatusIdx] < mosiO)
        :transition
           (ost --> {| miv_id := mosiRqI;
                       miv_value := O |}).

      Definition putRqUpUpMO: Rule :=
        rule.rqu[2~>1]
        :me oidx
        :requires (fun ost mins => mosiO <= ost#[implStatusIdx])
        :transition
           (ost --> {| miv_id := mosiRqI;
                       miv_value := ost#[implValueIdx] |}).

      Definition putRsDownDown: Rule :=
        rule.rsd[2~>2]
        :accepts mosiRsI
        :requires ⊤
        :transition (!|ost, _| --> ost +#[implStatusIdx <- mosiI]).

      Definition liPutImmI: Rule :=
        rule.immd[2~>3~~cidx]
        :accepts mosiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mosiI)
        :transition
           (!|ost, _| --> (ost, {| miv_id := mosiRsI;
                                   miv_value := O
                                |})).

      Definition liPutImmS: Rule :=
        rule.immd[2~>4~~cidx]
        :accepts mosiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mosiS)
        :transition
           (!|ost, _|
              --> (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
                   {| miv_id := mosiRsI;
                      miv_value := O
                   |})).

      Definition memPutImmSNotLast: Rule :=
        rule.immd[2~>4~>0~~cidx]
        :accepts mosiRqI
        :from cidx
        :requires
           ((fun ost orq mins => getDir cidx ost#[implDirIdx] = mosiS) /\
            (fun ost orq mins => List.length ost#[implDirIdx].(dir_sharers) >= 2))
        :transition
           (!|ost, msg|
              --> (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
                   {| miv_id := mosiRsI;
                      miv_value := O
                   |})).

      Definition memPutImmSLast: Rule :=
        rule.immd[2~>4~>1~~cidx]
        :accepts mosiRqI
        :from cidx
        :requires
           ((fun ost orq mins => getDir cidx ost#[implDirIdx] = mosiS) /\
            (fun ost orq mins => List.length ost#[implDirIdx].(dir_sharers) = 1))
        :transition
           (!|ost, msg| --> (ost +#[implStatusIdx <- mosiM]
                                 +#[implDirIdx <- setDirI],
                             {| miv_id := mosiRsI;
                                miv_value := O
                             |})).

      Definition liPutImmO: Rule :=
        rule.immd[2~>5~~cidx]
        :accepts mosiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mosiO)
        :transition
           (!|ost, msg| --> (ost +#[implStatusIdx <- mosiO]
                                 +#[implValueIdx <- msg_value msg]
                                 +#[implDirIdx <- removeOwner cidx ost#[implDirIdx]],
                             {| miv_id := mosiRsI;
                                miv_value := O
                             |})).

      Definition liPutImmM: Rule :=
        rule.immd[2~>6~~cidx]
        :accepts mosiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mosiM)
        :transition
           (!|ost, msg|
              --> (ost +#[implStatusIdx <- mosiM]
                       +#[implValueIdx <- msg_value msg]
                       +#[implDirIdx <- setDirI],
                   {| miv_id := mosiRsI;
                      miv_value := O |})).

    End EvictTrs.

  End Rules.

  Section Objects.
    Variable (oidx: IdxT).

    Section L1.

      Local Notation eidx := (l1ExtOf oidx).

      Program Definition l1: Object :=
        {| obj_idx := oidx;
           obj_rules :=
             [(** rules involved with [GetS] *)
               l1GetSImm eidx; l1GetSRqUpUp oidx eidx;
                 l1GetSRsDownDownS; downSImmS oidx; downSImmMO oidx;
                   (** rules involved with [GetM] *)
                   l1GetMImm eidx; l1GetMRqUpUp oidx eidx;
                     l1GetMRsDownDown; l1DownIImm oidx;
                       (** rules involved with [Put] *)
                       putRqUpUp oidx; putRqUpUpMO oidx; putRsDownDown];
           obj_rules_valid := _ |}.
      Next Obligation.
        inds_valid_tac.
      Qed.

    End L1.

    Definition liRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmOS cidx; liGetSImmM cidx; liGetSRqUpUp oidx cidx;
         liGetSRqUpDownS oidx cidx; liGetSRqUpDownMO oidx cidx;
           liGetMImm cidx; liGetMRqUpUp oidx cidx; liGetMRqUpDownM oidx cidx;
             liPutImmI cidx; liPutImmS cidx;
               liPutImmO cidx; liPutImmM cidx].

    Definition liRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map liRulesFromChild coinds).

    Hint Unfold liRulesFromChild liRulesFromChildren: RuleConds.

    Ltac disc_child_inds_disj :=
      pose proof (tree2Topo_TreeTopo tr 0);
      try match goal with
          | [Hn: ?n1 <> ?n2,
             H1: nth_error (subtreeChildrenIndsOf ?topo ?sidx) ?n1 = Some _,
             H2: nth_error (subtreeChildrenIndsOf ?topo ?sidx) ?n2 = Some _ |- _] =>
            eapply TreeTopo_children_inds_disj in Hn; eauto; destruct Hn
          end.

    Program Definition li: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (liRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [(** rules involved with [GetS] *)
               liGetSRsDownDownS; downSImmS oidx; downSImmMO oidx;
                 liDownSRsUpDownS; liDownSRsUpDownMO;
                 liDownSRqDownDownS oidx; liDownSRqDownDownMO oidx;
                   liDownSRsUpUpS; liDownSRsUpUpMO;
                   (** rules involved with [GetM] *)
                     liGetMRsDownDownDirI; liGetMRsDownRqDownDirOS oidx;
                       liDownIRsUpDown; liDownIImm oidx;
                       liDownIRqDownDownDirOS oidx; liDownIRqDownDownDirM oidx;
                         liDownIRsUpUp;
                         (** rules involved with [Put] *)
                         putRqUpUp oidx; putRqUpUpMO oidx; putRsDownDown];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

    Definition memRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmOS cidx; liGetSImmM cidx;
         liGetSRqUpDownS oidx cidx; liGetSRqUpDownMO oidx cidx;
           liGetMImm cidx; memGetMRqUpDown oidx cidx;
             liPutImmI cidx; liPutImmS cidx;
               liPutImmO cidx; liPutImmM cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map memRulesFromChild coinds).

    Hint Unfold memRulesFromChild memRulesFromChildren: RuleConds.

    Program Definition mem: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (memRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [liDownSRsUpDownS; liDownSRsUpDownMO; liDownIRsUpDown];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.
    
  End Objects.

  Program Definition impl: System :=
    {| sys_objs :=
         (map li cifc.(c_li_indices)) ++ (map l1 cifc.(c_l1_indices));
       sys_oinds_valid := _;
       sys_minds := cifc.(c_minds);
       sys_merqs := cifc.(c_merqs);
       sys_merss := cifc.(c_merss);
       sys_msg_inds_valid := _;
       sys_oss_inits := implOStatesInit;
       sys_orqs_inits := implORqsInit |}.
  Next Obligation.
    unfold li, l1.
    rewrite map_app.
    do 2 rewrite map_trans; simpl.
    do 2 rewrite map_id.
    apply tree2Topo_WfCIfc.
  Qed.
  Next Obligation.
    apply tree2Topo_WfCIfc.
  Qed.
  
End System.

