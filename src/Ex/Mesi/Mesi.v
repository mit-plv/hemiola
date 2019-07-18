Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecSv Ex.Mesi Ex.ImplTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Definition ii: IdxT := nil.
Definition idxTl (idx: IdxT): IdxT :=
  List.tl idx.

Definition rqUpFrom (cidx: IdxT): IdxT :=
  cidx~>rqUpIdx.
Definition rsUpFrom (cidx: IdxT): IdxT :=
  cidx~>rsUpIdx.
Definition downTo (cidx: IdxT): IdxT :=
  cidx~>downIdx.

(** Design choices:
 * - Multi-level (for arbitrary tree structure)
 * - MESI
 * - Directory (not snooping)
 * - Invalidate (not update)
 * - Write-back (not write-through)
 * - Inclusive (not exclusive)
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

  End Directory.

  Definition ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; MESI:Type; DirT:Type]%vector |}.

  Definition implOStateInit: OState ImplOStateIfc :=
    (0, (mesiS, (dirInit, tt))).
  
  Definition implOStatesInit: OStates ImplOStateIfc :=
    fold_left (fun m i => m +[i <- implOStateInit]) cifc.(c_indices) [].

  Definition implORqsInit: ORqs Msg :=
    fold_left (fun m i => m +[i <- []]) cifc.(c_indices) [].

  (** A core idea: a "summary" status in each object *)

  Definition summaryOf (ost: OState ImplOStateIfc): MESI :=
    if Compare_dec.le_gt_dec mesiS ost#[implStatusIdx]
    then ost#[implStatusIdx]
    else ost#[implDirIdx].(dir_st).

  Section CommonRules.
    Variable (oidx: IdxT).
    Variables (coRq coRs oc opRq opRs po: IdxT).

    Section GetTrs.

      Definition getSImm: Rule ImplOStateIfc :=
        rule[0~>0]
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

      Definition getSRqUpUp: Rule ImplOStateIfc :=
        rule[0~>1]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqS] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               summaryOf ost = mesiI))
        :transition
           (do (msg <-- getFirstMsg;
                  st --> (st.ost,
                          addRq (st.orq) upRq msg [po] oc,
                          [(opRq, {| msg_id := mesiRqS;
                                     msg_type := MRq;
                                     msg_value := VUnit |})]))).

      Definition getSRsDownDown: Rule ImplOStateIfc :=
        rule[0~>2]
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

      Definition downSRqUpDown: Rule ImplOStateIfc :=
        rule[0~>3]
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

      Definition downSRsUpDown: Rule ImplOStateIfc :=
        rule[0~>4]
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

      Definition downSImm: Rule ImplOStateIfc :=
        rule[0~>5]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqS] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implStatusIdx]))
        :transition
           (fun (ost: OState ImplOStateIfc) orq mins =>
              (ost +#[implStatusIdx <- mesiS],
               orq,
               [(opRs, {| msg_id := mesiDownRsS;
                          msg_type := MRs;
                          msg_value := VNat (ost#[implValueIdx]) |})])).

      Definition downSRqDownDown: Rule ImplOStateIfc :=
        rule[0~>6]
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

      (* NOTE: maybe it is not a good for performance to make all caches as inclusive? *)
      Definition downSRsUpUp: Rule ImplOStateIfc :=
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

      Definition getMImmE: Rule ImplOStateIfc :=
        rule[1~>0]
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

      Definition getMImmM: Rule ImplOStateIfc :=
        rule[1~>1]
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

      Definition getMRqUpUp: Rule ImplOStateIfc :=
        rule[1~>2]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               summaryOf ost <= mesiS))
        :transition
           (do (msg <-- getFirstMsg;
                  st --> (st.ost,
                          addRq (st.orq) upRq msg [po] oc,
                          [(opRq, {| msg_id := mesiRqM;
                                     msg_type := MRq;
                                     msg_value := VUnit |})]))).

      Definition downIRqUpDownME: Rule ImplOStateIfc :=
        rule[1~>3]
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

      Definition downIRsUpDownME: Rule ImplOStateIfc :=
        rule[1~>4]
        :requires
           (MsgsFromORq downRq /\ MsgIdsFrom [mesiDownRsI] /\
            RsAccepting /\ DownLockMsgId MRq mesiDownRqI)
        :transition
           (do (rssFrom <-- getDownLockIndsFrom;
                  rsbTo <-- getDownLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                          removeRq (st.orq) downRq,
                          [(rsbTo, {| msg_id := mesiRsM;
                                      msg_type := MRs;
                                      msg_value := VUnit |})]))).

      Definition downIRqUpDownS: Rule ImplOStateIfc :=
        rule[1~>5]
        :requires
           (MsgsFrom [coRq] /\ MsgIdsFrom [mesiRqM] /\
            RqAccepting /\ UpLockFree /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiS) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implDirIdx].(dir_st) = mesiS))
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

      Definition downIRsUpDownS: Rule ImplOStateIfc :=
        rule[1~>6]
        :requires
           (MsgsFromORq downRq /\ MsgIdFromEach mesiDownRsI /\
            RsAccepting /\ DownLockMsgId MRq mesiDownRqI)
        :transition
           (do (rssFrom <-- getDownLockIndsFrom;
                  rsbTo <-- getDownLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                          removeRq (st.orq) downRq,
                          [(rsbTo, {| msg_id := mesiRsM;
                                      msg_type := MRs;
                                      msg_value := VUnit |})]))).

      Definition downIImm: Rule ImplOStateIfc :=
        rule[1~>7]
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

      Definition downIRqDownDownME: Rule ImplOStateIfc :=
        rule[1~>8]
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

      Definition downIRqDownDownS: Rule ImplOStateIfc :=
        rule[1~>9]
        :requires
           (MsgsFrom [po] /\ MsgIdsFrom [mesiDownRqI] /\
            RqAccepting /\ DownLockFree /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiS) /\
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

      Definition downIRsUpUp: Rule ImplOStateIfc :=
        rule[1~>10]
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

    End SetTrs.

  End CommonRules.

  Section L1Rules.
    Variable (oidx: IdxT).
    Variables (coRq coRs oc opRq opRs po: IdxT).

    Definition l1GetSRsDownDownE: Rule ImplOStateIfc :=
      rule[2~>0]
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

    Definition l1GetMRsDownDown: Rule ImplOStateIfc :=
      rule[2~>1]
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

  End L1Rules.

  Section LiRules.
    Variable (oidx: IdxT).
    Variables (coRq coRs oc opRq opRs po: IdxT).

    Definition getSRsDownE: Rule ImplOStateIfc :=
      rule[3~>0]
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

    Definition getMRsDownDownI: Rule ImplOStateIfc :=
      rule[3~>1]
      :requires
         (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsM] /\
          RsAccepting /\ UpLockMsgId MRq mesiRqM /\
          DownLockFree /\
          (fun (ost: OState ImplOStateIfc) orq mins =>
             ost#[implStatusIdx] = mesiI))
      :transition
         (do (rsbTo <-- getUpLockIdxBack;
                st {{ ImplOStateIfc }}
                   --> (st.ost +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
                        removeRq (st.orq) upRq,
                        [(rsbTo, {| msg_id := mesiRsM;
                                    msg_type := MRs;
                                    msg_value := VUnit |})]))).

    Definition getMRsDownRqDownS: Rule ImplOStateIfc :=
      rule[3~>2]
      :requires
         (MsgsFromORq upRq /\ MsgIdsFrom [mesiRsM] /\
          RsAccepting /\ UpLockMsgId MRq mesiRqM /\
          DownLockFree /\
          (fun (ost: OState ImplOStateIfc) orq mins =>
             ost#[implStatusIdx] = mesiS))
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

  End LiRules.

End System.

