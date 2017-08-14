Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Tactics FMap Language.

Section System.
  Context {MsgT ValT StateT: Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).
  Hypothesis (valT_dec : forall v1 v2 : ValT, {v1 = v2} + {v1 <> v2}).

  Local Notation Object := (Object MsgT ValT StateT).
  Local Notation System := (System MsgT ValT StateT).
  Local Notation MsgId := (MsgId MsgT).
  Local Notation Msg := (Msg MsgT ValT).
  Local Notation msg_dec := (msg_dec msgT_dec valT_dec). 
  Local Notation PMsg := (PMsg MsgT ValT StateT).
  Local Notation Label := (Label MsgT ValT).
  Local Notation isTrsPair := (isTrsPair msgT_dec).

  Local Notation ObjectStates := (ObjectStates StateT).
  Local Notation State := (State MsgT ValT StateT).
  Local Notation steps := (steps msgT_dec valT_dec).

  (*! Now about monotonicity *)

  Definition FromExt (sys: System) (m: Msg) :=
    isExternal sys (msgFrom (msg_id m)) = true /\
    isInternal sys (msgTo (msg_id m)) = true.

  Definition ToExt (sys: System) (m: Msg) :=
    isExternal sys (msgTo (msg_id m)) = true /\
    isInternal sys (msgFrom (msg_id m)) = true.
  
  (* A pair of labels is [ImmediateL] if one handles a request and the other 
   * sends the response of it.
   *)
  Definition ImmediateL (obj: Object) (rql rsl: Label) (rq rs: Msg) :=
    rql = buildLabel (rq :: nil) None nil /\
    rsl = buildLabel nil (Some rq) (rs :: nil) /\
    FromExt (obj :: nil) rq /\ ToExt (obj :: nil) rs /\
    isTrsPair (msg_id rq) (msg_id rs) = true.

  (* "Four labels" [rq1], [rq2], [rs1], and [rs2] are [ForwardingL] if
   * 1) [rq1] comes as a request,
   * 2) [rs1] is handled and [rq2] is sent as a forwarded request,
   * 3) [rs2] comes as a response for [rq2], and
   * 4) [rs2] is handled and finally [rs1] is sent as a response for [rs1].
   *)
  Definition ForwardingL (obj: Object) (rql1 rql2 rsl1 rsl2: Label) (rq1 rq2 rs1 rs2: Msg) :=
    rql1 = buildLabel (rq1 :: nil) None nil /\
    rql2 = buildLabel nil (Some rq1) (rq2 :: nil) /\
    rsl2 = buildLabel (rs2 :: nil) None nil /\
    rsl1 = buildLabel nil (Some rs2) (rs1 :: nil) /\
    FromExt (obj :: nil) rq1 /\ ToExt (obj :: nil) rq2 /\
    FromExt (obj :: nil) rs2 /\ ToExt (obj :: nil) rs1 /\
    isTrsPair (msg_id rq1) (msg_id rs1) = true /\
    isTrsPair (msg_id rq2) (msg_id rs2) = true.
    
  (* A monotone transaction [MTransaction] is a sequence of label explicitly
   * indicating the start of a request and the out of corresponding response.
   * The sequence is composed of an [Immediate] labels as a base case, and
   * some [Forwarding] labels inductively chained.
   *)
  Inductive MTrs: System ->
                  Label (* start of a request *) ->
                  list Label (* intermediate request trace (w/o the start) *) ->
                  option Label (* end of a request *) ->
                  option Label (* start of a response *) ->
                  list Label (* intermediate response trace (w/o the end) *) ->
                  Label (* end of a response *) -> Prop :=
  | MTrsImm: forall obj rql rsl erq ers,
      ImmediateL obj rql rsl erq ers ->
      MTrs (obj :: nil) rql nil None None nil rsl
  | MTrsFwd: forall obj rql1 rql2 rsl1 rsl2 rq1 rq2 rs1 rs2,
      ForwardingL obj rql1 rql2 rsl1 rsl2 rq1 rq2 rs1 rs2 ->
      MTrs (obj :: nil) rql1 nil (Some rql2) (Some rsl2) nil rsl1
  | MTrsCom:
      forall sys1 rqin1 rqll1 rqout1 rsin1 rsll1 rsout1,
        MTrs sys1 rqin1 rqll1 rqout1 rsin1 rsll1 rsout1 ->
        forall sys2 rqin2 rqll2 rqout2 rsin2 rsll2 rsout2,
          MTrs sys2 rqin2 rqll2 (Some rqout2) (Some rsin2) rsll2 rsout2 ->
          lbl_outs rqout2 = lbl_ins rqin1 -> lbl_ins rsin2 = lbl_outs rsout1 ->
          Forall (FromExt (sys1 ++ sys2)) (lbl_ins rqin2) ->
          Forall (ToExt (sys1 ++ sys2)) (lbl_outs rsout2) ->
          MTrs (sys1 ++ sys2)
               rqin2 (rqll1 ++ (buildLabel nil (lbl_hdl rqout2) nil) :: rqll2) rqout1
               rsin1 (rsll2 ++ (buildLabel nil (lbl_hdl rsout1) nil) :: rsll1) rsout2.

  Definition MTransaction (sys: System) (ll: list Label) :=
    exists rqin rqll rqout rsin rsll rsout,
      ll = rsout :: rsll ++ rsin ::> rqout ::> rqll ++ rqin :: nil /\
      MTrs sys rqin rqll rqout rsin rsll rsout.

  Section PerObject.
    Variable obj: Object.
  
    (* A predicated message is [ImmediateP] if it handles a request and immediately
     * sends the response of it.
     *)
    Definition ImmediateP (rq: PMsg) :=
      msg_rqrs (pmsg_mid rq) = Rq /\
      forall st mt, exists rs,
          pmsg_outs rq st mt = rs :: nil /\
          isTrsPair (pmsg_mid rq) (msg_id rs) = true.

    (* A pair of predicated messages [rq1] and [rs2] is [ForwardingP] if
     * 1) [rq1] handles a request,
     * 2) [rs2] handles a response (NOT the response of [rq1]),
     * 3) [rq1] sends a request [rq2] which matches with [rs2], and
     * 4) [rs2] sends a response [rs1] which matches with [rq1].
     *)
    Definition ForwardingP (rq1 rs2: PMsg) :=
      msg_rqrs (pmsg_mid rq1) = Rq /\
      msg_rqrs (pmsg_mid rs2) = Rs /\
      (forall st mt, exists rq2,
            pmsg_outs rq1 st mt = rq2 :: nil /\
            msgTo (msg_id rq2) <> msgFrom (pmsg_mid rq1) /\
            isTrsPair (msg_id rq2) (pmsg_mid rs2) = true) /\
      (forall st mt, exists rs1,
            pmsg_outs rs2 st mt = rs1 :: nil /\
            isTrsPair (pmsg_mid rq1) (msg_id rs1) = true).

    (* A predicated message [pmsg] is a unique handler in [pmsgs] if it is
     * the only one handling a certain [MsgId].
     *)
    (* NOTE: Do we need this? *)
    (* Definition UniqueHandler (pmsgs: list PMsg) (pmsg: PMsg) := *)
    (*   In pmsg pmsgs /\ *)
    (*   forall pmsg', In pmsg' pmsgs -> (pmsg_mid pmsg) <> (pmsg_mid pmsg'). *)

    (* Monotonicity regulates the form of how requests are handled in a whole
     * message-passing system. It basically requires that the system always 
     * performs a "monotone" transaction. Informally, predicated messages in an
     * object is monotone if they are composed only of [ImmediateP] or 
     * [ForwardingP] messages.
     *)
    Definition MonotonePMsgs (pmsgs: list PMsg): Prop :=
      forall pmsg: PMsg,
        In pmsg pmsgs ->
        (ImmediateP pmsg \/
         (exists rs: PMsg,
             In rs pmsgs /\
             ForwardingP pmsg rs) \/
         (exists rq: PMsg,
             In rq pmsgs /\
             ForwardingP rq pmsg
        (* UniqueHandler pmsgs pmsg *))).

    Definition MonotoneObj := MonotonePMsgs (obj_pmsgs obj).

  End PerObject.

  Definition MonotoneSys (sys: System) := Forall MonotoneObj sys.

  Inductive Interleaving {A}: list A -> list (list A) -> Prop :=
  | ItlNil: forall lll, Interleaving nil lll
  | ItlCons:
      forall ll sll lll1 lll2,
        Interleaving ll (lll1 ++ sll :: lll2) ->
        forall l, Interleaving (l :: ll) (lll1 ++ (l :: sll) :: lll2).

  Theorem monotoneSys_monotone:
    forall sys,
      MonotoneSys sys ->
      forall ll st,
        steps sys (getStateInit sys) ll st ->
        exists mtrsl: list (list Label),
          Forall (MTransaction sys) mtrsl /\
          Interleaving ll mtrsl.
  Proof.
  Admitted.

End System.

