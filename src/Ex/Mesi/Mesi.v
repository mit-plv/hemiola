Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecSv Ex.Template Ex.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** Design choices:
 * - Multi-level (for arbitrary tree structure)
 * - MESI
 * - Directory (not snooping)
 * - Invalidate (not update)
 * - Write-back (not write-through)
 * - NINE (non-inclusive non-exclusive)
 *)

Section System.
  Variable (tr: tree).

  Definition topo := fst (tree2Topo tr 0).
  Definition cifc := snd (tree2Topo tr 0).
  Opaque topo cifc.
  
  Definition implValueIdx: Fin.t 3 := F1.
  Definition implStatusIdx: Fin.t 3 := F2.
  Definition implDirIdx: Fin.t 3 := F3.

  Section Directory.
    
    Record DirT: Set :=
      { dir_st: MESI; (* the summary status for children *)
        dir_excl: IdxT;
        dir_sharers: list IdxT
      }.

    Definition dirInit: DirT :=
      {| dir_st := mesiS;
         dir_excl := ii;
         dir_sharers := nil (** FIXME: should be children indices. *) |}.

    Import CaseNotations.
    Definition getDir (oidx: IdxT) (dir: DirT): MESI :=
      match case dir.(dir_st) on eq_nat_dec default mesiI with
      | mesiM: if idx_dec oidx dir.(dir_excl) then mesiM else mesiI
      | mesiE: if idx_dec oidx dir.(dir_excl) then mesiE else mesiI
      | mesiS: if in_dec idx_dec oidx dir.(dir_sharers)
               then mesiS else mesiI
      | mesiI: mesiI
      end.

    Definition setDirM (oidx: IdxT) :=
      {| dir_st := mesiM;
         dir_excl := oidx;
         dir_sharers := nil |}.

    Definition setDirE (oidx: IdxT) :=
      {| dir_st := mesiE;
         dir_excl := oidx;
         dir_sharers := nil |}.

    Definition setDirS (oinds: list IdxT) :=
      {| dir_st := mesiS;
         dir_excl := 0;
         dir_sharers := oinds |}.
    
    Definition setDirI :=
      {| dir_st := mesiI;
         dir_excl := 0;
         dir_sharers := nil |}.

    Definition addSharer (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := dir.(dir_st);
         dir_excl := dir.(dir_excl);
         dir_sharers := oidx :: dir.(dir_sharers) |}.

    Definition removeSharer (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := dir.(dir_st);
         dir_excl := dir.(dir_excl);
         dir_sharers := removeOnce idx_dec oidx dir.(dir_sharers) |}.

  End Directory.

  Instance ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; MESI:Type; DirT:Type]%vector |}.

  Definition implOStateInit: OState :=
    (0, (mesiS, (dirInit, tt))).
  
  Definition implOStatesInit: OStates :=
    fold_left (fun m i => m +[i <- implOStateInit])
              (cifc.(c_l1_indices) ++ cifc.(c_li_indices)) [].

  Definition implORqsInit: ORqs Msg :=
    initORqs (cifc.(c_l1_indices) ++ cifc.(c_li_indices)).

  (** A core idea: a "summary" status in each object *)

  Definition summaryOf (ost: OState): MESI :=
    if Compare_dec.le_gt_dec mesiS ost#[implStatusIdx]
    then ost#[implStatusIdx]
    else ost#[implDirIdx].(dir_st).

  Section Rules.
    Variables (oidx cidx: IdxT).

    Section GetTrs.

      Definition l1GetSImm: Rule :=
        rule.immd[cidx~>0~>0]
        :accepts mesiRqS
        :from cidx
        :requires (fun ost orq mins => mesiS <= ost#[implStatusIdx])
        :transition
           (!|ost, _| --> (ost, {| miv_id := mesiRsS;
                                   miv_value := ost#[implValueIdx]
                                |})).

      Definition liGetSImmS: Rule :=
        rule.immd[cidx~>0~>0~>0]
        :accepts mesiRqS
        :from cidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mesiS)
        :transition
           (!|ost, _|
            --> (ost +#[implDirIdx <- addSharer cidx ost#[implDirIdx]],
                 {| miv_id := mesiRsS;
                    miv_value := ost#[implValueIdx]
                 |})).

      Definition liGetSImmME: Rule :=
        rule.immd[cidx~>0~>0~>1]
        :accepts mesiRqS
        :from cidx
        :requires (fun ost orq mins => mesiE <= ost#[implStatusIdx])
        :transition
           (!|ost, _|
            --> (ost +#[implStatusIdx <- mesiS]
                     +#[implDirIdx <- setDirS [cidx]],
                 {| miv_id := mesiRsS;
                    miv_value := ost#[implValueIdx]
                 |})).

      (** NOTE (common rules): some rules do not require distinguishing L1 and Li 
       * caches. In correctness proof we may have to prove invariants, e.g., the
       * directory status of L1 is always [mesiI] since it does not have children.
       *)

      (* commonly used *)
      Definition getSRqUpUp: Rule :=
        rule.rquu[cidx~>0~>1]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires (fun ost mins => summaryOf ost = mesiI)
        :transition
           (!|ost, msg| --> {| miv_id := mesiRqS;
                               miv_value := O |}).

      Definition l1GetSRsDownDownS: Rule :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding mesiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implValueIdx <- msg_value min]
                     +#[implStatusIdx <- mesiS],
                 {| miv_id := mesiRsS;
                    miv_value := msg_value min |})).

      Definition l1GetSRsDownDownE: Rule :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding mesiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implValueIdx <- msg_value min]
                     +#[implStatusIdx <- mesiE],
                 {| miv_id := mesiRsS;
                    miv_value := msg_value min |})).

      Definition liGetSRsDownDownS: Rule :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding mesiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implValueIdx <- msg_value min]
                     +#[implStatusIdx <- mesiS]
                     +#[implDirIdx <- setDirS [objIdxOf rsbTo]],
                 {| miv_id := mesiRsS;
                    miv_value := msg_value min |})).

      Definition liGetSRsDownDownE: Rule :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding mesiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implDirIdx <- setDirE (objIdxOf rsbTo)],
                 {| miv_id := mesiRsE;
                    miv_value := msg_value min |})).

      (* commonly used *)
      Definition downSImm: Rule :=
        rule.immu[0~>3]
        :accepts mesiDownRqS
        :me oidx
        :requires (fun ost orq mins => mesiS <= ost#[implStatusIdx])
        :transition
           (!|ost, min| --> (ost +#[implStatusIdx <- mesiS],
                             {| miv_id := mesiDownRsS;
                                miv_value := ost#[implValueIdx] |})).

      Definition liGetSRqUpDownME: Rule :=
        rule.rqud[cidx~>0~>4~>0]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mesiI)
                  (mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_excl)],
                             {| miv_id := mesiDownRqS;
                                miv_value := O |})).

      (** TODO: if we pick a representative among sharers to get a clean value,
       * what is the difference between this protocol and MOSI? *)
      Definition liGetSRqUpDownS: Rule :=
        rule.rqud[cidx~>0~>4~>1]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           ((fun ost mins =>
               and (ost#[implStatusIdx] = mesiI)
                   (ost#[implDirIdx].(dir_st) = mesiS)))
        :transition
           (!|ost, msg| --> ([hd ii (ost#[implDirIdx].(dir_sharers))],
                             {| miv_id := mesiDownRqS;
                                miv_value := O |})).

      Definition liDownSRsUpDown: Rule :=
        rule.rsud[0~>5]
        :accepts mesiDownRsS
        :holding mesiRqS
        :requires FirstMsg
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                           (ost +#[implValueIdx <- msg_value msg]
                                +#[implStatusIdx <- mesiS]
                                +#[implDirIdx <- setDirS (objIdxOf rsbTo :: map objIdxOf rssFrom)],
                            {| miv_id := mesiRsS;
                               miv_value := msg_value msg |}))).

      Definition liDownSRqDownDownME: Rule :=
        rule.rqdd[0~>6~>0]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mesiI)
                  (mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_excl)],
                             {| miv_id := mesiDownRqS;
                                miv_value := O |})).

      Definition liDownSRqDownDownS: Rule :=
        rule.rqdd[0~>6~>1]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mesiI)
                  (ost#[implDirIdx].(dir_st) = mesiS))
        :transition
           (!|ost, msg|
            --> ([hd ii (ost#[implDirIdx].(dir_sharers))],
                 {| miv_id := mesiDownRqS;
                    miv_value := O |})).

      Definition liDownSRsUpUp: Rule :=
        rule.rsuu[0~>7]
        :accepts mesiDownRsS
        :holding mesiDownRqS
        :requires FirstMsg
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                           (ost +#[implValueIdx <- msg_value msg]
                                +#[implStatusIdx <- mesiS]
                                +#[implDirIdx <- setDirS (map objIdxOf rssFrom)],
                            {| miv_id := mesiDownRsS;
                               miv_value := msg_value msg |}))).

    End GetTrs.

    Section SetTrs.

      Definition l1GetMImmE: Rule :=
        rule.immd[cidx~>1~>0~>0]
        :accepts mesiRqM
        :from cidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mesiE)
        :transition
           (!|ost, msg|
            --> (ost +#[implStatusIdx <- mesiM]
                     +#[implValueIdx <- msg_value msg],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      Definition l1GetMImmM: Rule :=
        rule.immd[cidx~>1~>0~>1]
        :accepts mesiRqM
        :from cidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mesiM)
        :transition
           (!|ost, msg|
            --> (ost +#[implValueIdx <- msg_value msg],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      Definition liGetMImm: Rule :=
        rule.immd[cidx~>1~>0]
        :accepts mesiRqM
        :from cidx
        :requires (fun ost orq mins => mesiE <= ost#[implStatusIdx])
        :transition
           (!|ost, msg| --> (ost +#[implStatusIdx <- mesiI]
                                 +#[implDirIdx <- setDirM cidx],
                             {| miv_id := mesiRsM;
                                miv_value := O |})).

      (* commonly used *)
      Definition getMRqUpUp: Rule :=
        rule.rquu[cidx~>1~>1]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires (fun ost mins => summaryOf ost <= mesiS)
        :transition
           (!|ost, msg| --> {| miv_id := mesiRqM;
                               miv_value := O |}).

      Definition l1GetMRsDownDown: Rule :=
        rule.rsdd[1~>2]
        :accepts mesiRsM
        :holding mesiRqM
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implStatusIdx <- mesiM]
                     +#[implValueIdx <- msg_value rq],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      (* This is the case where it's possible to directly respond a [mesiRsM]
       * message back since there are no internal sharers to invalidate.
       *)
      Definition liGetMRsDownDownDirI: Rule :=
        rule.rsdd[1~>3]
        :accepts mesiRsM
        :holding mesiRqM
        :requires (fun ost orq mins => ost#[implDirIdx].(dir_st) = mesiI)
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[implStatusIdx <- mesiI]
                     +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      (* This is the case where internal invalidation is required due to
       * sharers. 
       *)
      Definition liGetMRsDownRqDownDirS: Rule :=
        rule.rsrq[1~>4]
        :accepts mesiRsM
        :holding mesiRqM
        :me oidx
        :requires (fun ost orq mins => ost#[implDirIdx].(dir_st) = mesiS)
        :transition
           (!|ost, rq| --> (ost#[implDirIdx].(dir_sharers),
                            {| miv_id := mesiDownRqI;
                               miv_value := O |})).

      Definition liDownIRsUpDownDirS: Rule :=
        rule.rsud[1~>5]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[implStatusIdx <- mesiI]
                     +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      Definition liGetMRqUpDownME: Rule :=
        rule.rqud[cidx~>1~>6]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mesiI)
                  (mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_excl)],
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liDownIRsUpDownME: Rule :=
        rule.rsud[1~>7]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[implStatusIdx <- mesiI]
                     +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      Definition l1DownIImm: Rule :=
        rule.immu[1~>8]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => mesiS <= ost#[implStatusIdx])
        :transition
           (!|ost, min| --> (ost +#[implStatusIdx <- mesiI],
                             {| miv_id := mesiDownRsI;
                                miv_value := O |})).

      Definition liDownIImm: Rule :=
        rule.immu[1~>9]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => mesiE <= ost#[implStatusIdx])
        :transition
           (!|ost, min| --> (ost +#[implStatusIdx <- mesiI],
                             {| miv_id := mesiDownRsI;
                                miv_value := O |})).

      Definition liDownIRqDownDownDirS: Rule :=
        rule.rqdd[1~>10]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost mins => ost#[implDirIdx].(dir_st) = mesiS)
        :transition
           (!|ost, msg| --> (ost#[implDirIdx].(dir_sharers),
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liDownIRqDownDownDirME: Rule :=
        rule.rqdd[1~>11]
        :accepts mesiDownRqI
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] = mesiI)
                  (mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[implDirIdx].(dir_excl)],
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liDownIRsUpUp: Rule :=
        rule.rsuu[1~>12]
        :accepts mesiDownRsI
        :holding mesiDownRqI
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[implStatusIdx <- mesiI]
                     +#[implDirIdx <- setDirI],
                 {| miv_id := mesiDownRsI;
                    miv_value := O |})).

      Definition memGetMRqUpDownDirS: Rule :=
        rule.rqud[cidx~>1~>13]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[implStatusIdx] <= mesiS)
                  (mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (!|ost, msg| --> (ost#[implDirIdx].(dir_sharers),
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

    End SetTrs.

    Section EvictTrs.

      (* NOTE: in MESI protocol, it makes a crucial difference whether it is 
       * required to send an up-to-date value or not during eviction. For example,
       * when in E status we don't need to write the data back since it is never 
       * written to a new value, i.e., the value is clean.
       *)

      Definition putRqUpUp: Rule :=
        rule.rqu[2~>0]
        :me oidx
        :requires (fun ost mins => ost#[implStatusIdx] < mesiM)
        :transition
           (ost --> {| miv_id := mesiRqI;
                       miv_value := O |}).

      Definition putRqUpUpM: Rule :=
        rule.rqu[2~>1]
        :me oidx
        :requires (fun ost mins => ost#[implStatusIdx] = mesiM)
        :transition
           (ost --> {| miv_id := mesiRqI;
                       miv_value := ost#[implValueIdx] |}).

      Definition putRsDownDown: Rule :=
        rule.rsd[2~>2]
        :accepts mesiRsI
        :holding mesiRqI
        :requires ⊤
        :transition
           (!|ost, _, _| --> ost +#[implStatusIdx <- mesiI]).

      Definition liPutImmI: Rule :=
        rule.immd[cidx~>2~>3]
        :accepts mesiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiI)
        :transition
           (!|ost, _| --> (ost, {| miv_id := mesiRsI;
                                   miv_value := O
                                |})).

      Definition liPutImmS: Rule :=
        rule.immd[cidx~>2~>4]
        :accepts mesiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiS)
        :transition
           (!|ost, _|
            --> (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
                 {| miv_id := mesiRsI;
                    miv_value := O
                 |})).

      Definition memPutImmSNotLast: Rule :=
        rule.immd[cidx~>2~>4~>0]
        :accepts mesiRqI
        :from cidx
        :requires
           ((fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiS) /\
            (fun ost orq mins => List.length ost#[implDirIdx].(dir_sharers) >= 2))
        :transition
           (!|ost, msg|
            --> (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
                 {| miv_id := mesiRsI;
                    miv_value := O
                 |})).

      Definition memPutImmSLast: Rule :=
        rule.immd[cidx~>2~>4~>1]
        :accepts mesiRqI
        :from cidx
        :requires
           ((fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiS) /\
            (fun ost orq mins => List.length ost#[implDirIdx].(dir_sharers) = 1))
        :transition
           (!|ost, msg| --> (ost +#[implStatusIdx <- mesiM]
                                 +#[implDirIdx <- setDirI],
                             {| miv_id := mesiRsI;
                                miv_value := O
                             |})).

      Definition liPutImmE: Rule :=
        rule.immd[cidx~>2~>5]
        :accepts mesiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiE)
        :transition
           (!|ost, msg| --> (ost +#[implStatusIdx <- mesiM]
                                 +#[implDirIdx <- setDirI],
                             {| miv_id := mesiRsI;
                                miv_value := O
                             |})).

      Definition liPutImmM: Rule :=
        rule.immd[cidx~>2~>6]
        :accepts mesiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiM)
        :transition
           (!|ost, msg|
            --> (ost +#[implStatusIdx <- mesiM]
                     +#[implValueIdx <- msg_value msg]
                     +#[implDirIdx <- setDirI],
                 {| miv_id := mesiRsI;
                    miv_value := O |})).

    End EvictTrs.

  End Rules.

  Section Objects.
    Variable (oidx: IdxT).

    Section L1.

      Local Notation eidx := (l1ExtOf oidx).

      Definition l1: Object :=
        {| obj_idx := oidx;
           obj_rules :=
             [(** rules involved with [GetS] *)
               l1GetSImm eidx; getSRqUpUp oidx eidx;
                 l1GetSRsDownDownS; l1GetSRsDownDownE; downSImm oidx;
                   (** rules involved with [GetM] *)
                   l1GetMImmE eidx; l1GetMImmM eidx;
                     getMRqUpUp oidx eidx;
                     l1GetMRsDownDown; l1DownIImm oidx;
                       (** rules involved with [Put] *)
                       putRqUpUp oidx; putRqUpUpM oidx; putRsDownDown];
           obj_rules_valid := ltac:(inds_valid_tac) |}.

    End L1.

    Definition liRulesFromChild (cidx: IdxT): list (Rule) :=
      [liGetSImmS cidx; liGetSImmME cidx; getSRqUpUp oidx cidx;
         liGetSRqUpDownME oidx cidx; liGetSRqUpDownS oidx cidx;
           liGetMImm cidx; getMRqUpUp oidx cidx; liGetMRsDownDownDirI;
             liGetMRqUpDownME oidx cidx;
             liPutImmI cidx; liPutImmS cidx;
               liPutImmE cidx; liPutImmM cidx].

    Definition liRulesFromChildren (coinds: list IdxT): list (Rule) :=
      List.concat (map liRulesFromChild coinds).

    Program Definition li: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (liRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [(** rules involved with [GetS] *)
               liGetSRsDownDownS; liGetSRsDownDownE; downSImm oidx;
                 liDownSRsUpDown;
                 liDownSRqDownDownME oidx; liDownSRqDownDownS oidx;
                   liDownSRsUpUp;
                   (** rules involved with [GetM] *)
                   liGetMRsDownDownDirI; liDownIRsUpDownME;
                     liGetMRsDownRqDownDirS oidx; liDownIRsUpDownDirS;
                       liDownIImm oidx;
                       liDownIRqDownDownDirS oidx; liDownIRqDownDownDirME oidx;
                         liDownIRsUpUp;
                         (** rules involved with [Put] *)
                         putRqUpUp oidx; putRqUpUpM oidx; putRsDownDown];
         obj_rules_valid := _ |}.
    Next Obligation.
    Admitted.

    Definition memRulesFromChild (cidx: IdxT): list (Rule) :=
      [liGetSImmS cidx; liGetSImmME cidx;
         liGetSRqUpDownME oidx cidx; liGetSRqUpDownS oidx cidx;
           liGetMImm cidx; liGetMRqUpDownME oidx cidx; memGetMRqUpDownDirS oidx cidx;
             liPutImmI cidx;
             memPutImmSNotLast cidx; memPutImmSLast cidx;
               liPutImmE cidx; liPutImmM cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list (Rule) :=
      List.concat (map memRulesFromChild coinds).
    
    Program Definition mem: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (memRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [liDownSRsUpDown; liDownIRsUpDownME; liDownIRsUpDownDirS];
         obj_rules_valid := _ |}.
    Next Obligation.
    Admitted.
    
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
  Admitted.
  Next Obligation.
  Admitted.
  
End System.

Hint Unfold l1GetSImm liGetSImmS liGetSImmME
     getSRqUpUp l1GetSRsDownDownS l1GetSRsDownDownE
     liGetSRsDownDownS liGetSRsDownDownE
     downSImm liGetSRqUpDownME liGetSRqUpDownS
     liDownSRsUpDown liDownSRqDownDownME liDownSRqDownDownS liDownSRsUpUp
  : MesiRules.

Hint Unfold l1GetMImmE l1GetMImmM liGetMImm
     getMRqUpUp l1GetMRsDownDown liGetMRsDownDownDirI liGetMRsDownRqDownDirS
     liDownIRsUpDownDirS liGetMRqUpDownME liDownIRsUpDownME
     l1DownIImm liDownIImm liDownIRqDownDownDirS liDownIRqDownDownDirME
     liDownIRsUpUp memGetMRqUpDownDirS
  : MesiRules.

Hint Unfold putRqUpUp putRqUpUpM putRsDownDown
     liPutImmI liPutImmS memPutImmSNotLast memPutImmSLast
     liPutImmE liPutImmM
  : MesiRules.

