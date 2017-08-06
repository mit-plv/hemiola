Require Import Bool List String Peano_dec.
Require Import FnMap Language.

Section System.
  Context {MsgT StateT: Type}.
  Context {MvalT: MsgT -> RqRs -> Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).

  Local Notation isTrsPair := (isTrsPair msgT_dec).

  Definition CondT := StateT -> Prop.
  Definition condImp (c1 c2: CondT) := forall st, c1 st -> c2 st.
  Infix "-->" := condImp (at level 30).
  Definition postOf (pmsg: PMsg MvalT StateT): CondT :=
    fun post => forall pre mt, pmsg_postcond pmsg pre mt post.

  Definition Disjoint (c1 c2: CondT) := forall st, c1 st -> c2 st -> False.
  Infix "-*-" := Disjoint (at level 30).

  Section PerObject.
    Variable obj: Object MvalT StateT.

    (*! Transaction *)

    Definition Responder (rsr: PMsg MvalT StateT) (rs: Msg MvalT) :=
      exists st mt, In rs (pmsg_outs rsr st mt).

    (* A VERY SUBTLE POINT:
     * [rsr] is not a [PMsg] that handles the response,
     * but a [PMsg] that _sends_ the response.
     *)
    Definition Transaction (rq rsr: PMsg MvalT StateT) (rs: Msg MvalT) :=
      In rq (obj_pmsgs obj) /\ In rsr (obj_pmsgs obj) /\
      Responder rsr rs /\
      isTrsPair (pmsg_mid rq) (msg_id rs) = true.

    Inductive TransactionInv: PMsg MvalT StateT (* request *) ->
                              CondT ->
                              PMsg MvalT StateT (* response *) -> Prop :=
    | TrsInv: forall rq rsr trsinv,
        postOf rq --> trsinv ->
        trsinv --> pmsg_precond rsr ->
        TransactionInv rq trsinv rsr.

    (*! LocallyDisjoint *)

    Definition DisjointTrsInv (rsr: PMsg MvalT StateT) (trsinv: CondT) :=
      forall pmsg, In pmsg (obj_pmsgs obj) ->
                   pmsg <> rsr ->
                   (pmsg_precond pmsg) -*- trsinv.

    Definition LocallyDisjoint :=
      forall rq rsr rs,
        Transaction rq rsr rs ->
        exists trsinv,
          TransactionInv rq trsinv rsr /\
          DisjointTrsInv rsr trsinv.

    (*! Prioritized interference *)

    (* [LocallyDisjoint] is too strong for practical protocol designs. It is
     * quite easy to think a deadlock condition because of this condition:
     * 
     *  rq    /--(rq)->\    rq
     * [O1] -x          x- [O2]
     *        \<-(rq)--/
     *
     * If two objects, [O1] and [O2], are handling requests respectively and
     * forward requests to each other, then because of the [LocallyDisjoint] 
     * conditions for [O1] and [O2], a deadlock occurs -- [O1] is waiting for
     * the response from [O2], while [O2] is waiting for the response from [O1].
     *
     * However, if we allow arbitrary interleavings among transactions, then
     * even a simple case is not linearizable anymore. In the above example, if
     * [O1] and [O2] handle the request from the each other at the same time,
     * the system is not linearizable.
     *
     * Prioritized interference allows certain interleavings. Basically, only
     * "prioritized" processes can interleave. Specifically, during a given
     * transaction that handles a request from a process (object) with index "i":
     * 1) Any other transactions with indices >= i should be disjoint.
     * 2) Transactions with indices < i are allowed to interleave, but they should
     *    be locally linearizable.
     *)

    (* TODO: better definition? *)
    Definition PDisjointTrsInv (rq rsr: PMsg MvalT StateT) (trsinv: CondT) :=
      forall pmsg, In pmsg (obj_pmsgs obj) ->
                   pmsg <> rsr ->
                   (msg_rqrs (pmsg_mid pmsg) = Rq ->
                    msg_rq (pmsg_mid pmsg) >= msg_rq (pmsg_mid rq)) ->
                   (msg_rqrs (pmsg_mid pmsg) = Rs ->
                    forall rs, Responder pmsg rs ->
                               msg_rs (msg_id rs) >= msg_rq (pmsg_mid rq)) ->
                   (pmsg_precond pmsg) -*- trsinv.

    Definition PInterfering :=
      forall rq rsr rs,
        Transaction rq rsr rs ->
        exists trsinv,
          TransactionInv rq trsinv rsr /\
          PDisjointTrsInv rq rsr trsinv.

    (*! Monotonicity *)

    (* A predicated message is [Immediate] if it handles a request and immediately
     * sends the response of it.
     *)
    Definition Immediate (rq: PMsg MvalT StateT) :=
      msg_rqrs (pmsg_mid rq) = Rq /\
      forall st mt, exists rs,
          pmsg_outs rq st mt = rs :: nil /\
          isTrsPair (pmsg_mid rq) (msg_id rs) = true.

    (* A pair of predicated messages [rq1] and [rs2] is [Forwarding] if
     * 1) [rq1] handles a request,
     * 2) [rs2] handles a response (NOT the response of [rq1]),
     * 3) [rq1] sends a request [rq2] which matches with [rs2], and
     * 4) [rs2] sends a response [rs1] which matches with [rq1].
     *)
    Definition Forwarding (rq1 rs2: PMsg MvalT StateT) :=
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
    Definition UniqueHandler (pmsgs: list (PMsg MvalT StateT))
               (pmsg: PMsg MvalT StateT) :=
      In pmsg pmsgs /\
      forall pmsg', In pmsg' pmsgs -> (pmsg_mid pmsg) <> (pmsg_mid pmsg').

    (* Monotonicity regulates the form of how requests are handled in a whole
     * message-passing system. It basically requires that the system always 
     * performs a "monotone" transaction. Informally, predicated messages in an
     * object is monotone if they are composed only of [Immediate] or 
     * [Forwarding] messages.
     *)
    Definition MonotonePMsgs (pmsgs: list (PMsg MvalT StateT)): Prop :=
      forall (pmsg: PMsg MvalT StateT),
        In pmsg pmsgs ->
        (Immediate pmsg \/
         (exists (rs: PMsg MvalT StateT),
             In rs pmsgs /\
             Forwarding pmsg rs) \/
         (exists (rq: PMsg MvalT StateT),
             In rq pmsgs /\
             Forwarding rq pmsg /\
             UniqueHandler pmsgs pmsg)).

    Definition Monotone := MonotonePMsgs (obj_pmsgs obj).

  End PerObject.

End System.

Section Facts.
  Context {MsgT StateT: Type}.
  Context {MvalT: MsgT -> RqRs -> Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).

  Theorem sequential_linear:
    forall sys: System MvalT StateT,
      SequentialSys msgT_dec sys -> Linear msgT_dec sys.
  Proof.
  Admitted.

  Theorem locally_disjoint_sequential:
    forall obj: Object MvalT StateT,
      LocallyDisjoint msgT_dec obj -> SequentialSys msgT_dec (obj :: nil).
  Proof.
  Admitted.

  Corollary locally_disjoint_linear:
    forall obj: Object MvalT StateT,
      LocallyDisjoint msgT_dec obj -> Linear msgT_dec (obj :: nil).
  Proof.
    intros; apply sequential_linear, locally_disjoint_sequential; auto.
  Qed.

  Theorem linear_sequential_compositional:
    forall (sys: System MvalT StateT),
      Forall (Monotone msgT_dec) sys ->
      Forall (fun obj => SequentialSys msgT_dec (obj :: nil)) sys ->
      Linear msgT_dec sys.
  Proof.
  Admitted.

  Corollary disjoint_linear:
    forall (sys: System MvalT StateT),
      Forall (Monotone msgT_dec) sys ->
      Forall (LocallyDisjoint msgT_dec) sys ->
      Linear msgT_dec sys.
  Proof.
    intros; apply linear_sequential_compositional; auto.
    apply Forall_impl with (P:= LocallyDisjoint msgT_dec); auto.
    intros; apply locally_disjoint_sequential; auto.
  Qed.

  Theorem prioritized_interf_linear_compositional:
    forall (sys: System MvalT StateT),
      Forall (Monotone msgT_dec) sys ->
      Forall (fun obj => Linear msgT_dec (obj :: nil)) sys ->
      Forall (PInterfering msgT_dec) sys ->
      Linear msgT_dec sys.
  Proof.
  Admitted.

End Facts.

