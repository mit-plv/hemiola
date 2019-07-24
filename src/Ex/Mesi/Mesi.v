Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecSv Ex.Mesi Ex.ImplTemplate.

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

  Definition ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; MESI:Type; DirT:Type]%vector |}.

  Definition implOStateInit: OState ImplOStateIfc :=
    (0, (mesiS, (dirInit, tt))).
  
  Definition implOStatesInit: OStates ImplOStateIfc :=
    fold_left (fun m i => m +[i <- implOStateInit])
              (cifc.(c_l1_indices) ++ cifc.(c_li_indices)) [].

  Definition implORqsInit: ORqs Msg :=
    initORqs (cifc.(c_l1_indices) ++ cifc.(c_li_indices)).

  (** A core idea: a "summary" status in each object *)

  Definition summaryOf (ost: OState ImplOStateIfc): MESI :=
    if Compare_dec.le_gt_dec mesiS ost#[implStatusIdx]
    then ost#[implStatusIdx]
    else ost#[implDirIdx].(dir_st).

  Section Rules.
    Variables (oidx cidx: IdxT).

    Local Notation opRq := (rqUpFrom oidx).
    Local Notation opRs := (rsUpFrom oidx).
    Local Notation po := (downTo oidx).

    Local Notation coRq := (rqUpFrom cidx).
    Local Notation coRs := (rsUpFrom cidx).
    Local Notation oc := (downTo cidx).

    Section GetTrs.

      Definition l1GetSImm: Rule ImplOStateIfc :=
        rule[cidx~>0~>0]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqS] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiS <= ost#[implStatusIdx]))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost, orq,
               [(oc, {| msg_id := mesiRsS;
                        msg_type := MRs;
                        msg_value := VNat (ost#[implValueIdx])
                     |})])).

      Definition liGetSImmS: Rule ImplOStateIfc :=
        rule[cidx~>0~>0~>0]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqS] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiS))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost, orq,
               [(oc, {| msg_id := mesiRsS;
                        msg_type := MRs;
                        msg_value := VNat (ost#[implValueIdx])
                     |})])).

      Definition liGetSImmME: Rule ImplOStateIfc :=
        rule[cidx~>0~>0~>1]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqS] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implStatusIdx]))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implStatusIdx <- mesiS]
                   +#[implDirIdx <- setDirS [objIdxOf coRq]],
               orq,
               [(oc, {| msg_id := mesiRsS;
                        msg_type := MRs;
                        msg_value := VNat (ost#[implValueIdx])
                     |})])).

      (** NOTE (common rules): some rules do not require distinguishing L1 and Li 
       * caches. In correctness proof we may have to prove invariants, e.g., the
       * directory status of L1 is always [mesiI] since it does not have children.
       *)

      (* commonly used *)
      Definition getSRqUpUp: Rule ImplOStateIfc :=
        rule[cidx~>0~>1]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqS] /\
            RqAccepting /\ UpLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               summaryOf ost = mesiI))
        :transition
           (do (msg <-- getFirstMsg;
                  st --> (st.ost,
                          addRq (st.orq) upRq msg [po] oc,
                          [(opRq, {| msg_id := mesiRqS;
                                     msg_type := MRq;
                                     msg_value := VUnit |})]))).

      Definition l1GetSRsDownDownS: Rule ImplOStateIfc :=
        rule[0~>2~>0]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsS] /\
            RsAccepting /\ FirstNatMsg /\ UpLockMsgId MRq mesiRqS /\
            DownLockFree)
        :transition
           (do (n <-- getFirstNatMsg;
                  rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implValueIdx <- n]
                                 +#[implStatusIdx <- mesiS],
                          removeRq (st.orq) upRq,
                          [(rsbTo, {| msg_id := mesiRsS;
                                      msg_type := MRs;
                                      msg_value := VNat n |})]))).

      Definition l1GetSRsDownDownE: Rule ImplOStateIfc :=
        rule[0~>2~>1]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsE] /\
            RsAccepting /\ FirstNatMsg /\ UpLockMsgId MRq mesiRqS /\
            DownLockFree)
        :transition
           (do (n <-- getFirstNatMsg;
                  rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implValueIdx <- n]
                                 +#[implStatusIdx <- mesiE],
                          removeRq (st.orq) upRq,
                          [(rsbTo, {| msg_id := mesiRsS;
                                      msg_type := MRs;
                                      msg_value := VNat n |})]))).

      Definition liGetSRsDownDownS: Rule ImplOStateIfc :=
        rule[0~>2~>0]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsS] /\
            RsAccepting /\ FirstNatMsg /\ UpLockMsgId MRq mesiRqS /\
            DownLockFree)
        :transition
           (do (n <-- getFirstNatMsg;
                  rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implValueIdx <- n]
                                 +#[implStatusIdx <- mesiS]
                                 +#[implDirIdx <- setDirS [objIdxOf rsbTo]],
                          removeRq (st.orq) upRq,
                          [(rsbTo, {| msg_id := mesiRsS;
                                      msg_type := MRs;
                                      msg_value := VNat n |})]))).

      Definition liGetSRsDownDownE: Rule ImplOStateIfc :=
        rule[0~>2~>1]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsE]
            /\ RsAccepting /\ FirstNatMsg /\ UpLockMsgId MRq mesiRqS
            /\ DownLockFree)
        :transition
           (do (n <-- getFirstNatMsg;
                  rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implDirIdx <- setDirE (objIdxOf rsbTo)],
                          removeRq (st.orq) upRq,
                          [(rsbTo, {| msg_id := mesiRsE;
                                      msg_type := MRs;
                                      msg_value := VNat n |})]))).

      (* commonly used *)
      Definition downSImm: Rule ImplOStateIfc :=
        rule[0~>3]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqS] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiS <= ost#[implStatusIdx]))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implStatusIdx <- mesiS],
               orq,
               [(opRs, {| msg_id := mesiDownRsS;
                          msg_type := MRs;
                          msg_value := VNat (ost#[implValueIdx]) |})])).

      Definition liGetSRqUpDownME: Rule ImplOStateIfc :=
        rule[cidx~>0~>4~>0]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqS] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cidx := st.ost#[implDirIdx].(dir_excl) in
                     (st.ost,
                      addRq (st.orq) downRq msg [rsUpFrom cidx] oc,
                      [(downTo cidx, {| msg_id := mesiDownRqS;
                                        msg_type := MRq;
                                        msg_value := VUnit |})]))).

      Definition liGetSRqUpDownS: Rule ImplOStateIfc :=
        rule[cidx~>0~>4~>1]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqS] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               and (ost#[implStatusIdx] = mesiI)
                   (ost#[implDirIdx].(dir_st) = mesiS)))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cidx := hd ii (st.ost#[implDirIdx].(dir_sharers)) in
                     (st.ost,
                      addRq (st.orq) downRq msg [rsUpFrom cidx] oc,
                      [(downTo cidx, {| msg_id := mesiDownRqS;
                                        msg_type := MRq;
                                        msg_value := VUnit |})]))).

      Definition liDownSRsUpDown: Rule ImplOStateIfc :=
        rule[0~>5]
        :requires
           (MsgsFromORq downRq /\ MsgIdsFrom [mesiDownRsS] /\
            RsAccepting /\ FirstNatMsg /\ DownLockMsgId MRq mesiDownRqS)
        :transition
           (do (nv <-- getFirstNatMsg;
                  rssFrom <-- getDownLockIndsFrom;
                  rsbTo <-- getDownLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implValueIdx <- nv]
                                 +#[implStatusIdx <- mesiS]
                                 +#[implDirIdx
                                      <- setDirS (objIdxOf rsbTo :: map objIdxOf rssFrom)],
                          removeRq (st.orq) downRq,
                          [(rsbTo, {| msg_id := mesiRsS;
                                      msg_type := MRs;
                                      msg_value := VNat nv |})]))).

      Definition liDownSRqDownDownME: Rule ImplOStateIfc :=
        rule[0~>6~>0]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqS] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cidx := st.ost#[implDirIdx].(dir_excl) in
                     (st.ost,
                      addRq (st.orq) downRq msg [rsUpFrom cidx] opRs,
                      [(downTo cidx, {| msg_id := mesiDownRqS;
                                        msg_type := MRq;
                                        msg_value := VUnit |})]))).

      Definition liDownSRqDownDownS: Rule ImplOStateIfc :=
        rule[0~>6~>1]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqS] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               and (ost#[implStatusIdx] = mesiI)
                   (ost#[implDirIdx].(dir_st) = mesiS)))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cidx := hd ii (st.ost#[implDirIdx].(dir_sharers)) in
                     (st.ost,
                      addRq (st.orq) downRq msg [rsUpFrom cidx] opRs,
                      [(downTo cidx, {| msg_id := mesiDownRqS;
                                        msg_type := MRq;
                                        msg_value := VUnit |})]))).

      Definition liDownSRsUpUp: Rule ImplOStateIfc :=
        rule[0~>7]
        :requires
           (MsgsFromORq downRq /\ MsgIdsFrom [mesiDownRsS] /\
            RsAccepting /\ FirstNatMsg /\ DownLockMsgId MRq mesiDownRqS)
        :transition
           (do (n <-- getFirstNatMsg;
                  rsbTo <-- getDownLockIdxBack;
                  rssFrom <-- getDownLockIndsFrom;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implValueIdx <- n]
                                 +#[implStatusIdx <- mesiS]
                                 +#[implDirIdx <- setDirS (map objIdxOf rssFrom)],
                          removeRq (st.orq) downRq,
                          [(rsbTo, {| msg_id := mesiDownRsS;
                                      msg_type := MRs;
                                      msg_value := VNat n |})]))).

    End GetTrs.

    Section SetTrs.

      Definition l1GetMImmE: Rule ImplOStateIfc :=
        rule[cidx~>1~>0~>0]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\ FirstNatMsg /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiE))
        :transition
           (do (n <-- getFirstNatMsg;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implStatusIdx <- mesiM]
                                 +#[implValueIdx <- n],
                          st.orq,
                          [(oc, {| msg_id := mesiRsM;
                                   msg_type := MRs;
                                   msg_value := VUnit |})]))).

      Definition l1GetMImmM: Rule ImplOStateIfc :=
        rule[cidx~>1~>0~>1]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\ FirstNatMsg /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiM))
        :transition
           (do (n <-- getFirstNatMsg;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implValueIdx <- n],
                          st.orq,
                          [(oc, {| msg_id := mesiRsM;
                                   msg_type := MRs;
                                   msg_value := VUnit |})]))).

      Definition liGetMImm: Rule ImplOStateIfc :=
        rule[cidx~>1~>0]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implStatusIdx]))
        :transition
           (do (st {{ ImplOStateIfc }}
                   --> (st.ost +#[implStatusIdx <- mesiI]
                               +#[implDirIdx <- setDirM (objIdxOf coRq)],
                        st.orq,
                        [(oc, {| msg_id := mesiRsM;
                                 msg_type := MRs;
                                 msg_value := VUnit |})]))).

      (* commonly used *)
      Definition getMRqUpUp: Rule ImplOStateIfc :=
        rule[cidx~>1~>1]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               summaryOf ost <= mesiS))
        :transition
           (do (msg <-- getFirstMsg;
                  st --> (st.ost,
                          addRq (st.orq) upRq msg [po] oc,
                          [(opRq, {| msg_id := mesiRqM;
                                     msg_type := MRq;
                                     msg_value := VUnit |})]))).

      Definition l1GetMRsDownDown: Rule ImplOStateIfc :=
        rule[1~>2]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsM] /\
            RsAccepting /\ UpLockMsgId MRq mesiRqM /\
            DownLockFree)
        :transition
           (do (n <-- getUpLockNatMsg;
                  rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implStatusIdx <- mesiM]
                                 +#[implValueIdx <- n],
                          removeRq (st.orq) upRq,
                          [(rsbTo, {| msg_id := mesiRsM;
                                      msg_type := MRs;
                                      msg_value := VUnit |})]))).

      (* This is the case where it's possible to directly respond a [mesiRsM]
       * message back since there are no internal sharers to invalidate.
       *)
      Definition liGetMRsDownDownDirI: Rule ImplOStateIfc :=
        rule[1~>3]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsM] /\
            RsAccepting /\ UpLockMsgId MRq mesiRqM /\
            DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implDirIdx].(dir_st) = mesiI))
        :transition
           (do (rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implStatusIdx <- mesiI]
                                 +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                          removeRq (st.orq) upRq,
                          [(rsbTo, {| msg_id := mesiRsM;
                                      msg_type := MRs;
                                      msg_value := VUnit |})]))).

      (* This is the case where internal invalidation is required due to
       * sharers. 
       *)
      Definition liGetMRsDownRqDownDirS: Rule ImplOStateIfc :=
        rule[1~>4]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsM] /\
            RsAccepting /\ UpLockMsgId MRq mesiRqM /\
            DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implDirIdx].(dir_st) = mesiS))
        :transition
           (do (msg <-- getUpLockMsg;
                  rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }} -->
                     let cinds := st.ost#[implDirIdx].(dir_sharers) in
                     (st.ost,
                      addRq (removeRq (st.orq) upRq) downRq msg (map rsUpFrom cinds) rsbTo,
                      map (fun cidx =>
                             (downTo cidx, {| msg_id := mesiDownRqI;
                                              msg_type := MRq;
                                              msg_value := VUnit |})) cinds))).

      Definition liDownIRsUpDownDirS: Rule ImplOStateIfc :=
        rule[1~>5]
        :requires
           (MsgsFromORq downRq /\ MsgIdFromEach mesiDownRsI /\
            RsAccepting /\ DownLockMsgId MRq mesiRqM)
        :transition
           (do (rssFrom <-- getDownLockIndsFrom;
                  rsbTo <-- getDownLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implStatusIdx <- mesiI]
                                 +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                          removeRq (st.orq) downRq,
                          [(rsbTo, {| msg_id := mesiRsM;
                                      msg_type := MRs;
                                      msg_value := VUnit |})]))).

      Definition liGetMRqUpDownME: Rule ImplOStateIfc :=
        rule[cidx~>1~>6]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cidx := st.ost#[implDirIdx].(dir_excl) in
                     (st.ost,
                      addRq (st.orq) downRq msg [rsUpFrom cidx] oc,
                      [(downTo cidx, {| msg_id := mesiDownRqI;
                                        msg_type := MRq;
                                        msg_value := VUnit |})]))).

      Definition liDownIRsUpDownME: Rule ImplOStateIfc :=
        rule[1~>7]
        :requires
           (MsgsFromORq downRq /\ MsgIdsFrom [mesiDownRsI] /\
            RsAccepting /\ DownLockMsgId MRq mesiRqM)
        :transition
           (do (rssFrom <-- getDownLockIndsFrom;
                  rsbTo <-- getDownLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implStatusIdx <- mesiI]
                                 +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                          removeRq (st.orq) downRq,
                          [(rsbTo, {| msg_id := mesiRsM;
                                      msg_type := MRs;
                                      msg_value := VUnit |})]))).

      Definition l1DownIImm: Rule ImplOStateIfc :=
        rule[1~>8]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqI] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiS <= ost#[implStatusIdx]))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implStatusIdx <- mesiI],
               orq,
               [(opRs, {| msg_id := mesiDownRsI;
                          msg_type := MRs;
                          msg_value := VUnit |})])).

      Definition liDownIImm: Rule ImplOStateIfc :=
        rule[1~>9]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqI] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implStatusIdx]))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implStatusIdx <- mesiI],
               orq,
               [(opRs, {| msg_id := mesiDownRsI;
                          msg_type := MRs;
                          msg_value := VUnit |})])).

      Definition liDownIRqDownDownDirS: Rule ImplOStateIfc :=
        rule[1~>10]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqI] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implDirIdx].(dir_st) = mesiS))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cinds := st.ost#[implDirIdx].(dir_sharers) in
                     (st.ost,
                      addRq (st.orq) downRq msg (map rsUpFrom cinds) opRs,
                      map (fun cidx =>
                             (downTo cidx, {| msg_id := mesiDownRqI;
                                              msg_type := MRq;
                                              msg_value := VUnit |})) cinds))).

      Definition liDownIRqDownDownDirME: Rule ImplOStateIfc :=
        rule[1~>11]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqI] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cidx := st.ost#[implDirIdx].(dir_excl) in
                     (st.ost,
                      addRq (st.orq) downRq msg [rsUpFrom cidx] opRs,
                      [(downTo cidx, {| msg_id := mesiDownRqI;
                                        msg_type := MRq;
                                        msg_value := VUnit |})]))).

      Definition liDownIRsUpUp: Rule ImplOStateIfc :=
        rule[1~>12]
        :requires
           (MsgsFromORq downRq /\ MsgIdFromEach mesiDownRsI /\
            RsAccepting /\ DownLockMsgId MRq mesiDownRqI)
        :transition
           (do (rsbTo <-- getDownLockIdxBack;
                  rssFrom <-- getDownLockIndsFrom;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implDirIdx <- setDirI],
                          removeRq (st.orq) downRq,
                          [(rsbTo, {| msg_id := mesiDownRsI;
                                      msg_type := MRs;
                                      msg_value := VUnit |})]))).

      Definition memGetMRqUpDownDirS: Rule ImplOStateIfc :=
        rule[cidx~>1~>13]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] <= mesiS) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (do (msg <-- getFirstMsg;
                  st {{ ImplOStateIfc }} -->
                     let cinds := st.ost#[implDirIdx].(dir_sharers) in
                     (st.ost,
                      addRq (st.orq) downRq msg (map rsUpFrom cinds) oc,
                      map (fun cidx =>
                             (downTo cidx, {| msg_id := mesiDownRqI;
                                              msg_type := MRq;
                                              msg_value := VUnit |})) cinds))).

    End SetTrs.

    Section EvictTrs.

      (* NOTE: in MESI protocol, it makes a crucial difference whether it is 
       * required to send an up-to-date value or not during eviction. For example,
       * when in E status we don't need to write the data back since it is never 
       * written to a new value, i.e., the value is clean.
       *)

      Definition putRqUpUp: Rule ImplOStateIfc :=
        rule[2~>0]
        :requires
           (MsgsFrom nil /\ UpLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] < mesiM))
        :transition
           (do (st {{ ImplOStateIfc }}
                   --> (st.ost,
                        addSilentUpRq (st.orq) [po],
                        [(opRs, {| msg_id := mesiRqI;
                                   msg_type := MRq;
                                   msg_value := VUnit
                                |})]))).

      Definition putRqUpUpM: Rule ImplOStateIfc :=
        rule[2~>1]
        :requires
           (MsgsFrom nil /\ UpLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiM))
        :transition
           (do (st {{ ImplOStateIfc }}
                   --> (st.ost,
                        addSilentUpRq (st.orq) [po],
                        [(opRs, {| msg_id := mesiRqI;
                                   msg_type := MRq;
                                   msg_value := VNat (st.ost#[implValueIdx])
                                |})]))).

      Definition putRsDownDown: Rule ImplOStateIfc :=
        rule[2~>2]
        :requires
           (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsI] /\
            RsAccepting /\ UpLockMsgId MRq mesiRqI /\
            DownLockFree)
        :transition
           (do (rsbTo <-- getUpLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implStatusIdx <- mesiI],
                          removeRq (st.orq) upRq,
                          nil))).

      Definition liPutImmI: Rule ImplOStateIfc :=
        rule[cidx~>2~>3]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqI] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               getDir (objIdxOf coRq) ost#[implDirIdx] = mesiI))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost, orq,
               [(oc, {| msg_id := mesiRsI;
                        msg_type := MRs;
                        msg_value := VUnit
                     |})])).

      Definition liPutImmS: Rule ImplOStateIfc :=
        rule[cidx~>2~>4]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqI] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               getDir (objIdxOf coRq) ost#[implDirIdx] = mesiS))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implDirIdx <- removeSharer (objIdxOf coRq) ost#[implDirIdx]],
               orq,
               [(oc, {| msg_id := mesiRsI;
                        msg_type := MRs;
                        msg_value := VUnit
                     |})])).

      Definition memPutImmSNotLast: Rule ImplOStateIfc :=
        rule[cidx~>2~>4~>0]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqI] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               and (getDir (objIdxOf coRq) ost#[implDirIdx] = mesiS)
                   (List.length ost#[implDirIdx].(dir_sharers) >= 2)))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implDirIdx <- removeSharer (objIdxOf coRq) ost#[implDirIdx]],
               orq,
               [(oc, {| msg_id := mesiRsI;
                        msg_type := MRs;
                        msg_value := VUnit
                     |})])).

      Definition memPutImmSLast: Rule ImplOStateIfc :=
        rule[cidx~>2~>4~>1]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqI] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               and (getDir (objIdxOf coRq) ost#[implDirIdx] = mesiS)
                   (List.length ost#[implDirIdx].(dir_sharers) = 1)))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implStatusIdx <- mesiM]
                   +#[implDirIdx <- removeSharer (objIdxOf coRq) ost#[implDirIdx]],
               orq,
               [(oc, {| msg_id := mesiRsI;
                        msg_type := MRs;
                        msg_value := VUnit
                     |})])).

      Definition liPutImmE: Rule ImplOStateIfc :=
        rule[cidx~>2~>5]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqI] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               getDir (objIdxOf coRq) ost#[implDirIdx] = mesiE))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implStatusIdx <- mesiM]
                   +#[implDirIdx <- setDirI],
               orq,
               [(oc, {| msg_id := mesiRsI;
                        msg_type := MRs;
                        msg_value := VUnit
                     |})])).

      Definition liPutImmM: Rule ImplOStateIfc :=
        rule[cidx~>2~>6]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqI] /\
            RqAccepting /\ FirstNatMsg /\
            UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               getDir (objIdxOf coRq) ost#[implDirIdx] = mesiM))
        :transition
           (do (n <-- getFirstNatMsg;
                  st {{ ImplOStateIfc }} -->
                     (st.ost +#[implStatusIdx <- mesiM]
                             +#[implValueIdx <- n]
                             +#[implDirIdx <- setDirI],
                      st.orq,
                      [(oc, {| msg_id := mesiRsI;
                               msg_type := MRs;
                               msg_value := VUnit |})]))).

    End EvictTrs.

  End Rules.

  Section Objects.
    Variable (oidx: IdxT).

    Section L1.

      Local Notation eidx := (l1ExtOf oidx).

      Definition l1: Object ImplOStateIfc :=
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

    Definition liRulesFromChild (cidx: IdxT): list (Rule ImplOStateIfc) :=
      [liGetSImmS cidx; liGetSImmME cidx; getSRqUpUp oidx cidx;
         liGetSRqUpDownME cidx; liGetSRqUpDownS cidx;
           liGetMImm cidx; getMRqUpUp oidx cidx; liGetMRsDownDownDirI;
             liGetMRqUpDownME cidx;
             liPutImmI cidx; liPutImmS cidx;
               liPutImmE cidx; liPutImmM cidx].

    Definition liRulesFromChildren (coinds: list IdxT): list (Rule ImplOStateIfc) :=
      List.concat (map liRulesFromChild coinds).

    Program Definition li: Object ImplOStateIfc :=
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

    Definition memRulesFromChild (cidx: IdxT): list (Rule ImplOStateIfc) :=
      [liGetSImmS cidx; liGetSImmME cidx;
         liGetSRqUpDownME cidx; liGetSRqUpDownS cidx;
           liGetMImm cidx; liGetMRqUpDownME cidx; memGetMRqUpDownDirS cidx;
             liPutImmI cidx;
             memPutImmSNotLast cidx; memPutImmSLast cidx;
               liPutImmE cidx; liPutImmM cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list (Rule ImplOStateIfc) :=
      List.concat (map memRulesFromChild coinds).
             
    Program Definition mem: Object ImplOStateIfc :=
      {| obj_idx := oidx;
         obj_rules :=
           (memRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [liDownSRsUpDown; liDownIRsUpDownME; liDownIRsUpDownDirS];
         obj_rules_valid := _ |}.
    Next Obligation.
    Admitted.
    
  End Objects.

  Program Definition impl: System ImplOStateIfc :=
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

