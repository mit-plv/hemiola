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
  Definition objIdxOf (midx: IdxT) := idxTl midx.
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
           (fun ost _ =>
              (ost, {| msg_id := mesiRsS;
                       msg_type := MRs;
                       msg_value := VNat (ost#[implValueIdx])
                    |})).

      Definition liGetSImmS: Rule :=
        rule.immd[cidx~>0~>0~>0]
        :accepts mesiRqS
        :from cidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mesiS)
        :transition
           (fun ost _ =>
              (ost, {| msg_id := mesiRsS;
                       msg_type := MRs;
                       msg_value := VNat (ost#[implValueIdx])
                    |})).

      Definition liGetSImmME: Rule :=
        rule.immd[cidx~>0~>0~>1]
        :accepts mesiRqS
        :from cidx
        :requires (fun ost orq mins => mesiE <= ost#[implStatusIdx])
        :transition
           (fun ost _ =>
              (ost +#[implStatusIdx <- mesiS]
                   +#[implDirIdx <- setDirS [cidx]],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat (ost#[implValueIdx])
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
        :requires (fun ost orq mins => summaryOf ost = mesiI)
        :transition
           (fun ost msg =>
              {| msg_id := mesiRqS;
                 msg_type := MRq;
                 msg_value := VUnit |}).

      (** * FIXME: how to get "n"? *)
      Definition l1GetSRsDownDownS: Rule :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun ost min rq rsbTo =>
              (* n <-- getNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n]
                   +#[implStatusIdx <- mesiS],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      Definition l1GetSRsDownDownE: Rule :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun ost min rq rsbTo =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n]
                   +#[implStatusIdx <- mesiE],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      Definition liGetSRsDownDownS: Rule :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun ost min rq rsbTo =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n]
                   +#[implStatusIdx <- mesiS]
                   +#[implDirIdx <- setDirS [objIdxOf rsbTo]],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      Definition liGetSRsDownDownE: Rule :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun ost min rq rsbTo =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implDirIdx <- setDirE (objIdxOf rsbTo)],
               {| msg_id := mesiRsE;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      (* commonly used *)
      Definition downSImm: Rule :=
        rule.immu[0~>3]
        :accepts mesiDownRqS
        :me oidx
        :requires (fun ost orq mins => mesiS <= ost#[implStatusIdx])
        :transition
           (fun ost min =>
              (ost +#[implStatusIdx <- mesiS],
               {| msg_id := mesiDownRsS;
                  msg_type := MRs;
                  msg_value := VNat (ost#[implValueIdx]) |})).

      Definition liGetSRqUpDownME: Rule :=
        rule.rqud[cidx~>0~>4~>0]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           ((fun ost orq mins => ost#[implStatusIdx] = mesiI) /\
            (fun ost orq mins => mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun ost msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      (** TODO: if we pick a representative among sharers to get a clean value,
       * what is the difference between this protocol and MOSI? *)
      Definition liGetSRqUpDownS: Rule :=
        rule.rqud[cidx~>0~>4~>1]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           ((fun ost orq mins => ost#[implStatusIdx] = mesiI) /\
            (fun ost orq mins => ost#[implDirIdx].(dir_st) = mesiS))
        :transition
           (fun ost msg =>
              let scidx := hd ii (ost#[implDirIdx].(dir_sharers)) in
              ([scidx],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownSRsUpDown: Rule :=
        rule.rsud[0~>5]
        :accepts mesiDownRsS
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun ost mins rq rssFrom rsbTo =>
              (* nv <-- getFirstNatMsg; *)
              let nv := O in
              (ost +#[implValueIdx <- nv]
                   +#[implStatusIdx <- mesiS]
                   +#[implDirIdx <- setDirS (objIdxOf rsbTo :: map objIdxOf rssFrom)],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat nv |})).

      Definition liDownSRqDownDownME: Rule :=
        rule.rqdd[0~>6~>0]
        :accepts mesiDownRqS
        :me oidx
        :requires
           ((fun ost orq mins => ost#[implStatusIdx] = mesiI) /\
            (fun ost orq mins => mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun ost msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownSRqDownDownS: Rule :=
        rule.rqdd[0~>6~>1]
        :accepts mesiDownRqS
        :me oidx
        :requires
           ((fun ost orq mins => ost#[implStatusIdx] = mesiI) /\
            (fun ost orq mins => ost#[implDirIdx].(dir_st) = mesiS))
        :transition
           (fun ost msg =>
              let cidx := hd ii (ost#[implDirIdx].(dir_sharers)) in
              ([cidx],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownSRsUpUp: Rule :=
        rule.rsuu[0~>7]
        :accepts mesiDownRsS
        :holding mesiDownRqS
        :requires FirstNatMsg
        :transition
           (fun ost mins rq rssFrom rsbTo =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n]
                   +#[implStatusIdx <- mesiS]
                   +#[implDirIdx <- setDirS (map objIdxOf rssFrom)],
               {| msg_id := mesiDownRsS;
                  msg_type := MRs;
                  msg_value := VNat n |})).

    End GetTrs.

    Section SetTrs.

      Definition l1GetMImmE: Rule :=
        rule.immd[cidx~>1~>0~>0]
        :accepts mesiRqM
        :from cidx
        :requires
           (FirstNatMsg /\
            (fun ost orq mins => ost#[implStatusIdx] = mesiE))
        :transition
           (fun ost msg =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implStatusIdx <- mesiM]
                   +#[implValueIdx <- n],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition l1GetMImmM: Rule :=
        rule.immd[cidx~>1~>0~>1]
        :accepts mesiRqM
        :from cidx
        :requires
           (FirstNatMsg /\
            (fun ost orq mins => ost#[implStatusIdx] = mesiM))
        :transition
           (fun ost msg =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liGetMImm: Rule :=
        rule.immd[cidx~>1~>0]
        :accepts mesiRqM
        :from cidx
        :requires (fun ost orq mins => mesiE <= ost#[implStatusIdx])
        :transition
           (fun ost msg =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM cidx],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      (* commonly used *)
      Definition getMRqUpUp: Rule :=
        rule.rquu[cidx~>1~>1]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires (fun ost orq mins => summaryOf ost <= mesiS)
        :transition
           (fun ost msg =>
              {| msg_id := mesiRqM;
                 msg_type := MRq;
                 msg_value := VUnit |}).

      Definition l1GetMRsDownDown: Rule :=
        rule.rsdd[1~>2]
        :accepts mesiRsM
        :holding mesiRqM
        :requires (fun _ _ _ => True)
        :transition
           (fun ost min rq rsbTo =>
              (* n <-- getUpLockNatMsg; *)
              let n := O in
              (ost +#[implStatusIdx <- mesiM]
                   +#[implValueIdx <- n],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      (* This is the case where it's possible to directly respond a [mesiRsM]
       * message back since there are no internal sharers to invalidate.
       *)
      Definition liGetMRsDownDownDirI: Rule :=
        rule.rsdd[1~>3]
        :accepts mesiRsM
        :holding mesiRqM
        :requires (fun ost orq mins => ost#[implDirIdx].(dir_st) = mesiI)
        :transition
           (fun ost min rq rsbTo =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      (* This is the case where internal invalidation is required due to
       * sharers. 
       *)
      Definition liGetMRsDownRqDownDirS: Rule :=
        rule.rsrq[1~>4]
        :accepts mesiRsM
        :holding mesiRqM
        :requires
           (fun ost orq mins =>
              ost#[implDirIdx].(dir_st) = mesiS)
        :transition
           (fun ost rq =>
              (ost#[implDirIdx].(dir_sharers),
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRsUpDownDirS: Rule :=
        rule.rsud[1~>5]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires (fun _ _ _ => True)
        :transition
           (fun ost mins rq rssFrom rsbTo =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liGetMRqUpDownME: Rule :=
        rule.rqud[cidx~>1~>6]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           ((fun ost orq mins => ost#[implStatusIdx] = mesiI) /\
            (fun ost orq mins => mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun ost msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRsUpDownME: Rule :=
        rule.rsud[1~>7]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires (fun _ _ _ => True)
        :transition
           (fun ost mins rq rssFrom rsbTo =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition l1DownIImm: Rule :=
        rule.immu[1~>8]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => mesiS <= ost#[implStatusIdx])
        :transition
           (fun ost min =>
              (ost +#[implStatusIdx <- mesiI],
               {| msg_id := mesiDownRsI;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liDownIImm: Rule :=
        rule.immu[1~>9]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => mesiE <= ost#[implStatusIdx])
        :transition
           (fun ost min =>
              (ost +#[implStatusIdx <- mesiI],
               {| msg_id := mesiDownRsI;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liDownIRqDownDownDirS: Rule :=
        rule.rqdd[1~>10]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => ost#[implDirIdx].(dir_st) = mesiS)
        :transition
           (fun ost msg =>
              (ost#[implDirIdx].(dir_sharers),
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRqDownDownDirME: Rule :=
        rule.rqdd[1~>11]
        :accepts mesiDownRqI
        :me oidx
        :requires
           ((fun ost orq mins => ost#[implStatusIdx] = mesiI) /\
            (fun ost orq mins => mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun ost msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRsUpUp: Rule :=
        rule.rsuu[1~>12]
        :accepts mesiDownRsI
        :holding mesiDownRqI
        :requires (fun _ _ _ => True)
        :transition
           (fun ost mins rq rssFrom rsbTo =>
              (ost +#[implDirIdx <- setDirI],
               {| msg_id := mesiDownRsI;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition memGetMRqUpDownDirS: Rule :=
        rule.rqud[cidx~>1~>13]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           ((fun ost orq mins => ost#[implStatusIdx] <= mesiS) /\
            (fun ost orq mins => mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun ost msg =>
              (ost#[implDirIdx].(dir_sharers),
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

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
        :requires (fun ost orq mins => ost#[implStatusIdx] < mesiM)
        :transition
           (fun ost =>
              {| msg_id := mesiRqI;
                 msg_type := MRq;
                 msg_value := VUnit |}).

      Definition putRqUpUpM: Rule :=
        rule.rqu[2~>1]
        :me oidx
        :requires (fun ost orq mins => ost#[implStatusIdx] = mesiM)
        :transition
           (fun ost =>
              {| msg_id := mesiRqI;
                 msg_type := MRq;
                 msg_value := VNat (ost#[implValueIdx]) |}).

      Definition putRsDownDown: Rule :=
        rule.rsd[2~>2]
        :accepts mesiRsI
        :holding mesiRqI
        :requires (fun _ _ _ => True)
        :transition
           (fun ost min rq =>
              ost +#[implStatusIdx <- mesiI]).

      Definition liPutImmI: Rule :=
        rule.immd[cidx~>2~>3]
        :accepts mesiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiI)
        :transition
           (fun ost msg =>
              (ost, {| msg_id := mesiRsI;
                       msg_type := MRs;
                       msg_value := VUnit
                    |})).

      Definition liPutImmS: Rule :=
        rule.immd[cidx~>2~>4]
        :accepts mesiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiS)
        :transition
           (fun ost msg =>
              (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition memPutImmSNotLast: Rule :=
        rule.immd[cidx~>2~>4~>0]
        :accepts mesiRqI
        :from cidx
        :requires
           ((fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiS) /\
            (fun ost orq mins => List.length ost#[implDirIdx].(dir_sharers) >= 2))
        :transition
           (fun ost msg =>
              (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition memPutImmSLast: Rule :=
        rule.immd[cidx~>2~>4~>1]
        :accepts mesiRqI
        :from cidx
        :requires
           ((fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiS) /\
            (fun ost orq mins => List.length ost#[implDirIdx].(dir_sharers) = 1))
        :transition
           (fun ost msg =>
              (ost +#[implStatusIdx <- mesiM]
                   +#[implDirIdx <- setDirI],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition liPutImmE: Rule :=
        rule.immd[cidx~>2~>5]
        :accepts mesiRqI
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiE)
        :transition
           (fun ost msg =>
              (ost +#[implStatusIdx <- mesiM]
                   +#[implDirIdx <- setDirI],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition liPutImmM: Rule :=
        rule.immd[cidx~>2~>6]
        :accepts mesiRqI
        :from cidx
        :requires
           (FirstNatMsg /\
            (fun ost orq mins => getDir cidx ost#[implDirIdx] = mesiM))
        :transition
           (fun ost msg =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implStatusIdx <- mesiM]
                   +#[implValueIdx <- n]
                   +#[implDirIdx <- setDirI],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit |})).

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
                     liGetMRsDownRqDownDirS; liDownIRsUpDownDirS;
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

