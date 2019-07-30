Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecSv Ex.Mesi Ex.ImplTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Section Template.
  Variable (dtr: DTree).
  Context {ifc: OStateIfc}.
  Variables (ridx msgId: IdxT).

  (* Heads-up: [cidx] is not the index of itself, but of a child. *)
  Definition immDownRule (cidx: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc -> Msg -> OState ifc * Msg): Rule ifc :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (ost, out) := trs (st.ost) msg in
                     (ost, st.orq, [(downTo cidx, out)]))).

  Definition immUpRule (oidx: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc -> Msg -> OState ifc * Msg): Rule ifc :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (ost, out) := trs (st.ost) msg in
                     (ost, st.orq, [(rqUpFrom oidx, out)]))).

  Definition rqUpUpRule (cidx oidx: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc -> Msg -> Msg): Rule ifc :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> (st.ost,
                      addRq (st.orq) upRq msg [downTo oidx] (downTo cidx),
                      [(rqUpFrom oidx, trs (st.ost) msg)]))).

  Definition rqUpUpRuleS (oidx: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc -> Msg): Rule ifc :=
    rule[ridx]
    :requires (MsgsFrom nil /\ RqAccepting /\ UpLockFree /\ prec)
    :transition
       (fun ost orq _ =>
          (ost,
           addSilentUpRq orq [downTo oidx],
           [(rqUpFrom oidx, trs ost)])).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rqUpDownRule (cidx oidx: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc -> Msg -> list IdxT * Msg): Rule ifc :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (cinds, out) := trs (st.ost) msg in
                     (st.ost,
                      addRq (st.orq) downRq msg (map rsUpFrom cinds) (downTo cidx),
                      map (fun cidx => (downTo cidx, msg)) cinds))).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rqDownDownRule (oidx: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc -> Msg -> list IdxT * Msg): Rule ifc :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (cinds, out) := trs (st.ost) msg in
                     (st.ost,
                      addRq (st.orq) downRq msg (map rsUpFrom cinds) (rsUpFrom oidx),
                      map (fun cidx => (downTo cidx, msg)) cinds))).

  Definition rsDownDownRule (rqId: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc ->
                   Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   OState ifc * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\ UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              rq <-- getUpLockMsg;
              rsbTo <-- getUpLockIdxBack;
              st --> let (ost, out) := trs (st.ost) msg rq rsbTo in
                     (ost, removeRq (st.orq) upRq, [(rsbTo, out)]))).

  Definition rsDownDownRuleS (rqId: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc ->
                   Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   OState ifc) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\ UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              rq <-- getUpLockMsg;
              rsbTo <-- getUpLockIdxBack;
              st --> (trs (st.ost) msg rq,
                      removeRq (st.orq) upRq,
                      nil))).

  Definition rsUpDownRule (rqId: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   list IdxT (* responses from *) ->
                   IdxT (* response back to *) ->
                   OState ifc * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ RsAccepting /\ prec)
    :transition
       (do (rq <-- getDownLockMsg;
              rssFrom <-- getDownLockIndsFrom;
              rsbTo <-- getDownLockIdxBack;
              st --> let (ost, out) := trs (st.ost) (st.msgs) rq rssFrom rsbTo in
                     (ost,
                      removeRq (st.orq) downRq,
                      [(rsbTo, out)]))).

  Definition rsUpUpRule (rqId: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   list IdxT (* responses from *) ->
                   IdxT (* response back to *) ->
                   OState ifc * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ RsAccepting /\ prec)
    :transition
       (do (rq <-- getDownLockMsg;
              rssFrom <-- getDownLockIndsFrom;
              rsbTo <-- getDownLockIdxBack;
              st --> let (ost, out) := trs (st.ost) (st.msgs) rq rssFrom rsbTo in
                     (ost,
                      removeRq (st.orq) downRq,
                      [(rsbTo, out)]))).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rsDownRqDownRule (rqId: IdxT)
             (prec: OPrec ifc)
             (trs: OState ifc -> Msg -> list IdxT * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\
               UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (rq <-- getUpLockMsg;
              rsbTo <-- getUpLockIdxBack;
              st --> let (cinds, out) := trs (st.ost) rq in
                     (st.ost,
                      addRq (removeRq (st.orq) upRq)
                            downRq rq (map rsUpFrom cinds) rsbTo,
                      map (fun cidx => (downTo cidx, out)) cinds))).
  
End Template.

Notation "'rule.immd' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':requires' PREC ':transition' TRS" :=
  (immDownRule RIDX MSGID FROM PREC%prec TRS%trs) (at level 5, only parsing).
Notation "'rule.immu' '[' RIDX ']' ':accepts' MSGID ':me' ME ':requires' PREC ':transition' TRS" :=
  (immUpRule RIDX MSGID ME PREC%prec TRS%trs) (at level 5).

Notation "'rule.rquu' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpUpRule RIDX MSGID FROM ME PREC%prec TRS%trs) (at level 5).
Notation "'rule.rqu' '[' RIDX ']' ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpUpRuleS RIDX ME PREC%prec TRS%trs) (at level 5).
Notation "'rule.rqud' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpDownRule RIDX MSGID FROM ME PREC%prec TRS%trs) (at level 5).
Notation "'rule.rqdd' '[' RIDX ']' ':accepts' MSGID ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqDownDownRule RIDX MSGID ME PREC%prec TRS%trs) (at level 5).

Notation "'rule.rsdd' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsDownDownRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).
Notation "'rule.rsd' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsDownDownRuleS RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).
Notation "'rule.rsud' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpDownRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).
Notation "'rule.rsuu' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpUpRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).

Notation "'rule.rsrq' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsDownRqDownRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).

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

    Section GetTrs.

      Definition l1GetSImm: Rule ImplOStateIfc :=
        rule.immd[cidx~>0~>0]
        :accepts mesiRqS
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiS <= ost#[implStatusIdx])
        :transition
           (fun (ost: OState ImplOStateIfc) _ =>
              (ost, {| msg_id := mesiRsS;
                       msg_type := MRs;
                       msg_value := VNat (ost#[implValueIdx])
                    |})).

      Definition liGetSImmS: Rule ImplOStateIfc :=
        rule.immd[cidx~>0~>0~>0]
        :accepts mesiRqS
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiS)
        :transition
           (fun (ost: OState ImplOStateIfc) _ =>
              (ost, {| msg_id := mesiRsS;
                       msg_type := MRs;
                       msg_value := VNat (ost#[implValueIdx])
                    |})).

      Definition liGetSImmME: Rule ImplOStateIfc :=
        rule.immd[cidx~>0~>0~>1]
        :accepts mesiRqS
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              mesiE <= ost#[implStatusIdx])
        :transition
           (fun (ost: OState ImplOStateIfc) _ =>
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
      Definition getSRqUpUp: Rule ImplOStateIfc :=
        rule.rquu[cidx~>0~>1]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              summaryOf ost = mesiI)
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              {| msg_id := mesiRqS;
                 msg_type := MRq;
                 msg_value := VUnit |}).

      (** * FIXME: how to get "n"? *)
      Definition l1GetSRsDownDownS: Rule ImplOStateIfc :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun (ost: OState ImplOStateIfc) min rq rsbTo =>
              (* n <-- getNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n]
                   +#[implStatusIdx <- mesiS],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      Definition l1GetSRsDownDownE: Rule ImplOStateIfc :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun (ost: OState ImplOStateIfc) min rq rsbTo =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n]
                   +#[implStatusIdx <- mesiE],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      Definition liGetSRsDownDownS: Rule ImplOStateIfc :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun (ost: OState ImplOStateIfc) min rq rsbTo =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n]
                   +#[implStatusIdx <- mesiS]
                   +#[implDirIdx <- setDirS [objIdxOf rsbTo]],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      Definition liGetSRsDownDownE: Rule ImplOStateIfc :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun (ost: OState ImplOStateIfc) min rq rsbTo =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implDirIdx <- setDirE (objIdxOf rsbTo)],
               {| msg_id := mesiRsE;
                  msg_type := MRs;
                  msg_value := VNat n |})).

      (* commonly used *)
      Definition downSImm: Rule ImplOStateIfc :=
        rule.immu[0~>3]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              mesiS <= ost#[implStatusIdx])
        :transition
           (fun (ost: OState ImplOStateIfc) min =>
              (ost +#[implStatusIdx <- mesiS],
               {| msg_id := mesiDownRsS;
                  msg_type := MRs;
                  msg_value := VNat (ost#[implValueIdx]) |})).

      Definition liGetSRqUpDownME: Rule ImplOStateIfc :=
        rule.rqud[cidx~>0~>4~>0]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      (** TODO: if we pick a representative among sharers to get a clean value,
       * what is the difference between this protocol and MOSI? *)
      Definition liGetSRqUpDownS: Rule ImplOStateIfc :=
        rule.rqud[cidx~>0~>4~>1]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implDirIdx].(dir_st) = mesiS))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              let scidx := hd ii (ost#[implDirIdx].(dir_sharers)) in
              ([scidx],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownSRsUpDown: Rule ImplOStateIfc :=
        rule.rsud[0~>5]
        :accepts mesiDownRsS
        :holding mesiRqS
        :requires FirstNatMsg
        :transition
           (fun (ost: OState ImplOStateIfc) mins rq rssFrom rsbTo =>
              (* nv <-- getFirstNatMsg; *)
              let nv := O in
              (ost +#[implValueIdx <- nv]
                   +#[implStatusIdx <- mesiS]
                   +#[implDirIdx <- setDirS (objIdxOf rsbTo :: map objIdxOf rssFrom)],
               {| msg_id := mesiRsS;
                  msg_type := MRs;
                  msg_value := VNat nv |})).

      Definition liDownSRqDownDownME: Rule ImplOStateIfc :=
        rule.rqdd[0~>6~>0]
        :accepts mesiDownRqS
        :me oidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownSRqDownDownS: Rule ImplOStateIfc :=
        rule.rqdd[0~>6~>1]
        :accepts mesiDownRqS
        :me oidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implDirIdx].(dir_st) = mesiS))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              let cidx := hd ii (ost#[implDirIdx].(dir_sharers)) in
              ([cidx],
               {| msg_id := mesiDownRqS;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownSRsUpUp: Rule ImplOStateIfc :=
        rule.rsuu[0~>7]
        :accepts mesiDownRsS
        :holding mesiDownRqS
        :requires FirstNatMsg
        :transition
           (fun (ost: OState ImplOStateIfc) mins rq rssFrom rsbTo =>
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

      Definition l1GetMImmE: Rule ImplOStateIfc :=
        rule.immd[cidx~>1~>0~>0]
        :accepts mesiRqM
        :from cidx
        :requires
           (FirstNatMsg /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiE))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implStatusIdx <- mesiM]
                   +#[implValueIdx <- n],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition l1GetMImmM: Rule ImplOStateIfc :=
        rule.immd[cidx~>1~>0~>1]
        :accepts mesiRqM
        :from cidx
        :requires
           (FirstNatMsg /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiM))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (* n <-- getFirstNatMsg; *)
              let n := O in
              (ost +#[implValueIdx <- n],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liGetMImm: Rule ImplOStateIfc :=
        rule.immd[cidx~>1~>0]
        :accepts mesiRqM
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              mesiE <= ost#[implStatusIdx])
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM cidx],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      (* commonly used *)
      Definition getMRqUpUp: Rule ImplOStateIfc :=
        rule.rquu[cidx~>1~>1]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              summaryOf ost <= mesiS)
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              {| msg_id := mesiRqM;
                 msg_type := MRq;
                 msg_value := VUnit |}).

      Definition l1GetMRsDownDown: Rule ImplOStateIfc :=
        rule.rsdd[1~>2]
        :accepts mesiRsM
        :holding mesiRqM
        :requires (fun _ _ _ => True)
        :transition
           (fun (ost: OState ImplOStateIfc) min rq rsbTo =>
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
      Definition liGetMRsDownDownDirI: Rule ImplOStateIfc :=
        rule.rsdd[1~>3]
        :accepts mesiRsM
        :holding mesiRqM
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implDirIdx].(dir_st) = mesiI)
        :transition
           (fun (ost: OState ImplOStateIfc) min rq rsbTo =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      (* This is the case where internal invalidation is required due to
       * sharers. 
       *)
      Definition liGetMRsDownRqDownDirS: Rule ImplOStateIfc :=
        rule.rsrq[1~>4]
        :accepts mesiRsM
        :holding mesiRqM
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              ost#[implDirIdx].(dir_st) = mesiS)
        :transition
           (fun (ost: OState ImplOStateIfc) rq =>
              (ost#[implDirIdx].(dir_sharers),
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRsUpDownDirS: Rule ImplOStateIfc :=
        rule.rsud[1~>5]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires (fun _ _ _ => True)
        :transition
           (fun (ost: OState ImplOStateIfc) mins rq rssFrom rsbTo =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liGetMRqUpDownME: Rule ImplOStateIfc :=
        rule.rqud[cidx~>1~>6]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRsUpDownME: Rule ImplOStateIfc :=
        rule.rsud[1~>7]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires (fun _ _ _ => True)
        :transition
           (fun (ost: OState ImplOStateIfc) mins rq rssFrom rsbTo =>
              (ost +#[implStatusIdx <- mesiI]
                   +#[implDirIdx <- setDirM (objIdxOf rsbTo)],
               {| msg_id := mesiRsM;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition l1DownIImm: Rule ImplOStateIfc :=
        rule.immu[1~>8]
        :accepts mesiDownRqI
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              mesiS <= ost#[implStatusIdx])
        :transition
           (fun (ost: OState ImplOStateIfc) min =>
              (ost +#[implStatusIdx <- mesiI],
               {| msg_id := mesiDownRsI;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liDownIImm: Rule ImplOStateIfc :=
        rule.immu[1~>9]
        :accepts mesiDownRqI
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              mesiE <= ost#[implStatusIdx])
        :transition
           (fun (ost: OState ImplOStateIfc) min =>
              (ost +#[implStatusIdx <- mesiI],
               {| msg_id := mesiDownRsI;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition liDownIRqDownDownDirS: Rule ImplOStateIfc :=
        rule.rqdd[1~>10]
        :accepts mesiDownRqI
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              ost#[implDirIdx].(dir_st) = mesiS)
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (ost#[implDirIdx].(dir_sharers),
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRqDownDownDirME: Rule ImplOStateIfc :=
        rule.rqdd[1~>11]
        :accepts mesiDownRqI
        :me oidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] = mesiI) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              ([ost#[implDirIdx].(dir_excl)],
               {| msg_id := mesiDownRqI;
                  msg_type := MRq;
                  msg_value := VUnit |})).

      Definition liDownIRsUpUp: Rule ImplOStateIfc :=
        rule.rsuu[1~>12]
        :accepts mesiDownRsI
        :holding mesiDownRqI
        :requires (fun _ _ _ => True)
        :transition
           (fun (ost: OState ImplOStateIfc) mins rq rssFrom rsbTo =>
              (ost +#[implDirIdx <- setDirI],
               {| msg_id := mesiDownRsI;
                  msg_type := MRs;
                  msg_value := VUnit |})).

      Definition memGetMRqUpDownDirS: Rule ImplOStateIfc :=
        rule.rqud[cidx~>1~>13]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               ost#[implStatusIdx] <= mesiS) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               mesiE <= ost#[implDirIdx].(dir_st)))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
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

      Definition putRqUpUp: Rule ImplOStateIfc :=
        rule.rqu[2~>0]
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              ost#[implStatusIdx] < mesiM)
        :transition
           (fun (ost: OState ImplOStateIfc) =>
              {| msg_id := mesiRqI;
                 msg_type := MRq;
                 msg_value := VUnit |}).

      Definition putRqUpUpM: Rule ImplOStateIfc :=
        rule.rqu[2~>1]
        :me oidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              ost#[implStatusIdx] = mesiM)
        :transition
           (fun (ost: OState ImplOStateIfc) =>
              {| msg_id := mesiRqI;
                 msg_type := MRq;
                 msg_value := VNat (ost#[implValueIdx]) |}).

      Definition putRsDownDown: Rule ImplOStateIfc :=
        rule.rsd[2~>2]
        :accepts mesiRsI
        :holding mesiRqI
        :requires (fun _ _ _ => True)
        :transition
           (fun (ost: OState ImplOStateIfc) min rq =>
              ost +#[implStatusIdx <- mesiI]).

      Definition liPutImmI: Rule ImplOStateIfc :=
        rule.immd[cidx~>2~>3]
        :accepts mesiRqI
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              getDir cidx ost#[implDirIdx] = mesiI)
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (ost, {| msg_id := mesiRsI;
                       msg_type := MRs;
                       msg_value := VUnit
                    |})).

      Definition liPutImmS: Rule ImplOStateIfc :=
        rule.immd[cidx~>2~>4]
        :accepts mesiRqI
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              getDir cidx ost#[implDirIdx] = mesiS)
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition memPutImmSNotLast: Rule ImplOStateIfc :=
        rule.immd[cidx~>2~>4~>0]
        :accepts mesiRqI
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              and (getDir cidx ost#[implDirIdx] = mesiS)
                  (List.length ost#[implDirIdx].(dir_sharers) >= 2))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (ost +#[implDirIdx <- removeSharer cidx ost#[implDirIdx]],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition memPutImmSLast: Rule ImplOStateIfc :=
        rule.immd[cidx~>2~>4~>1]
        :accepts mesiRqI
        :from cidx
        :requires
           ((fun (ost: OState ImplOStateIfc) orq mins =>
               getDir cidx ost#[implDirIdx] = mesiS) /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               List.length ost#[implDirIdx].(dir_sharers) = 1))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (ost +#[implStatusIdx <- mesiM]
                   +#[implDirIdx <- setDirI],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition liPutImmE: Rule ImplOStateIfc :=
        rule.immd[cidx~>2~>5]
        :accepts mesiRqI
        :from cidx
        :requires
           (fun (ost: OState ImplOStateIfc) orq mins =>
              getDir cidx ost#[implDirIdx] = mesiE)
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
              (ost +#[implStatusIdx <- mesiM]
                   +#[implDirIdx <- setDirI],
               {| msg_id := mesiRsI;
                  msg_type := MRs;
                  msg_value := VUnit
               |})).

      Definition liPutImmM: Rule ImplOStateIfc :=
        rule.immd[cidx~>2~>6]
        :accepts mesiRqI
        :from cidx
        :requires
           (FirstNatMsg /\
            (fun (ost: OState ImplOStateIfc) orq mins =>
               getDir cidx ost#[implDirIdx] = mesiM))
        :transition
           (fun (ost: OState ImplOStateIfc) msg =>
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
         liGetSRqUpDownME oidx cidx; liGetSRqUpDownS oidx cidx;
           liGetMImm cidx; getMRqUpUp oidx cidx; liGetMRsDownDownDirI;
             liGetMRqUpDownME oidx cidx;
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
         liGetSRqUpDownME oidx cidx; liGetSRqUpDownS oidx cidx;
           liGetMImm cidx; liGetMRqUpDownME oidx cidx; memGetMRqUpDownDirS oidx cidx;
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

