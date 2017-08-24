Require Import Bool List String Peano_dec.
Require Import FMap Language.

Section System.
  Context {MsgT ValT StateT: Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).
  Hypothesis (valT_dec : forall v1 v2 : ValT, {v1 = v2} + {v1 <> v2}).

  Local Notation Object := (Object MsgT ValT StateT).
  Local Notation System := (System MsgT ValT StateT).
  Local Notation MsgId := (MsgId MsgT).
  Local Notation Msg := (Msg MsgT ValT).
  Local Notation PMsg := (PMsg MsgT ValT StateT).
  Local Notation CondT := (CondT StateT).
  Local Notation Label := (Label MsgT ValT).
  Local Notation isTrsPair := (isTrsPair msgT_dec).

  Section PerObject.
    Variable obj: Object.

    (* A predicated message [pmsg] is a unique handler in [pmsgs] if it is
     * the only one handling a certain message type (MsgT).
     *)
    Definition UniqueHandler (pmsg: PMsg) :=
      forall pmsg', In pmsg' (obj_pmsgs obj) ->
                    msg_type (pmsg_mid pmsg) <> msg_type (pmsg_mid pmsg').

    (*! Transaction *)

    Definition RqHandler (rqh: PMsg) :=
      msg_rqrs (pmsg_mid rqh) = Rq.

    Definition Responder (rsr: PMsg) (rs: MsgId) :=
      msg_rqrs rs = Rs /\
      forall st v, exists mrs,
          pmsg_outs rsr st v = mrs :: nil /\
          msg_id mrs = rs.

    Definition Transaction (rqh rsr: PMsg) :=
      In rqh (obj_pmsgs obj) /\ In rsr (obj_pmsgs obj) /\
      exists rs,
        Responder rsr rs /\
        isTrsPair (pmsg_mid rqh) rs = true.

    Inductive TransactionInv: PMsg (* request *) -> CondT -> PMsg (* response *) -> Prop :=
    | TrsInv: forall rq rsr trsinv,
        postOf rq --> trsinv ->
        trsinv --> pmsg_precond rsr ->
        TransactionInv rq trsinv rsr.

    (*! Stable transactions *)
    
    (* A transaction is stable if 
     * 1) the target object has a unique responder for this transaction and
     * 2) a transaction invariant is disjoint to the precondition of the 
     *    request handler, so that there is no interleaving between the same
     *    transactions.
     *)
    Definition StableTransaction (rqh rsr: PMsg) :=
      UniqueHandler rsr /\ Transaction rqh rsr /\
      exists trsinv,
        TransactionInv rqh trsinv rsr /\
        pmsg_precond rqh -*- trsinv.

    (*! Locally-disjoint transactions *)

    Definition DisjointTrsInv (rsr: PMsg) (trsinv: CondT) :=
      forall pmsg, In pmsg (obj_pmsgs obj) ->
                   pmsg <> rsr ->
                   (pmsg_precond pmsg) -*- trsinv.

    Definition LocallyDisjoint :=
      forall rqh rsr,
        Transaction rqh rsr ->
        exists trsinv,
          TransactionInv rqh trsinv rsr /\
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
    Definition PDisjointTrsInv (rq rsr: PMsg) (trsinv: CondT) :=
      forall pmsg, In pmsg (obj_pmsgs obj) ->
                   pmsg <> rsr ->
                   (msg_rqrs (pmsg_mid pmsg) = Rq ->
                    msg_rq (pmsg_mid pmsg) >= msg_rq (pmsg_mid rq)) ->
                   (msg_rqrs (pmsg_mid pmsg) = Rs ->
                    forall rs, Responder pmsg rs ->
                               msg_rs rs >= msg_rq (pmsg_mid rq)) ->
                   (pmsg_precond pmsg) -*- trsinv.

    Definition PInterfering :=
      forall rqh rsr,
        Transaction rqh rsr ->
        exists trsinv,
          TransactionInv rqh trsinv rsr /\
          PDisjointTrsInv rqh rsr trsinv.

  End PerObject.

  Section Facts.
    Theorem sequential_linear:
      forall sys: System,
        SequentialSys msgT_dec valT_dec sys -> Linear msgT_dec valT_dec sys.
    Proof.
    Admitted.

    Theorem locally_disjoint_sequential:
      forall obj: Object,
        LocallyDisjoint obj -> SequentialSys msgT_dec valT_dec (obj :: nil).
    Proof.
    Admitted.

    Corollary locally_disjoint_linear:
      forall obj: Object,
        LocallyDisjoint obj -> Linear msgT_dec valT_dec (obj :: nil).
    Proof.
      intros; apply sequential_linear, locally_disjoint_sequential; auto.
    Qed.

  End Facts.

End System.

