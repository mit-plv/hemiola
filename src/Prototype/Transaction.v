Require Import Bool List String Peano_dec.
Require Import FnMap Language.

Section System.
  Variable MsgT: Type.
  Variable StateT: Type.

  Definition CondT := StateT -> Prop.
  Definition condImp (c1 c2: CondT) := forall st, c1 st -> c2 st.
  Infix "-->" := condImp (at level 30).
  Definition postOf (postcond: StateT -> StateT -> Prop): CondT :=
    fun post => forall pre, postcond pre post.

  Definition Separated (c1 c2: CondT) := forall st, c1 st -> c2 st -> False.
  Infix "-*-" := Separated (at level 30).

  Section PerObject.
    Variable obj: Object MsgT StateT.

    Definition Transaction (rq rsr: PMsg MsgT StateT) (rs: MsgId MsgT) :=
      pmsgOf obj rq /\ pmsgOf obj rsr /\
      (exists st, In rs (outsOf rsr st)) /\
      isTrsPair (midOf rq) rs = true.

    (* A VERY SUBTLE POINT:
     * [rsr] is not a [PMsg] that handles the response,
     * but a [PMsg] that _sends_ the response.
     *)
    Inductive TransactionInv: PMsg MsgT StateT (* request *) ->
                              CondT ->
                              PMsg MsgT StateT (* response *) -> Prop :=
    | TrsInv: forall rq rsr trsinv,
        postOf (postcondOf rq) --> trsinv ->
        trsinv --> precondOf rsr ->
        (forall pmsg, pmsgOf obj pmsg -> (precondOf pmsg) -*- trsinv) ->
        TransactionInv rq trsinv rsr.

    Definition LocallyDisjoint :=
      forall rq rsr rs,
        Transaction rq rsr rs ->
        exists trsinv, TransactionInv rq trsinv rsr.

    (* NOTE: this well-formedness for [PMsg] is too narrow.
     * Should be extended enough to cover practical protocols.
     *)
    Inductive WfPMsg: PMsg MsgT StateT -> Prop :=
    | WpRqRq:
        forall pmsg,
          msg_rqrs (midOf pmsg) = Rq ->
          (forall st,
              exists msg_out,
                outsOf pmsg st = msg_out :: nil /\
                msg_rqrs msg_out = Rq /\
                (* need this? *) msg_rs (midOf pmsg) = msg_rq msg_out /\
                msg_rq (midOf pmsg) <> msg_rs msg_out) ->
          WfPMsg pmsg
    | WpRqRs:
        forall pmsg,
          msg_rqrs (midOf pmsg) = Rq ->
          (forall st,
              exists msg_out,
                outsOf pmsg st = msg_out :: nil /\
                msg_rqrs msg_out = Rs /\
                msg_rq (midOf pmsg) = msg_rq msg_out /\
                msg_rs (midOf pmsg) = msg_rs msg_out) ->
          WfPMsg pmsg
    | WpRs:
        forall pmsg,
          msg_rqrs (midOf pmsg) = Rs ->
          WfPMsg pmsg.

    Definition WfObj (obj: Object MsgT StateT) :=
      (forall pmsg, obj_pmsg_ints obj pmsg -> WfPMsg pmsg) /\
      (forall pmsg, obj_pmsg_exts obj pmsg -> WfPMsg pmsg).

  End PerObject.

  Variable makeComplete: list (MsgId MsgT) -> list (MsgId MsgT).

  Theorem locally_disjoint_linear:
    forall obs,
      Forall (fun obj => WfObj obj) obs ->
      Forall (fun obj => LocallyDisjoint obj) obs ->
      Linear obs.
  Proof.
    unfold Linear, Linearizable; intros.
    eexists; repeat split.
  Admitted.
  
End System.

