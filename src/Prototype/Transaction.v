Require Import Bool List String Peano_dec.
Require Import FnMap Language.

Section System.
  Context {MsgT StateT: Type}.

  Definition CondT := StateT -> Prop.
  Definition condImp (c1 c2: CondT) := forall st, c1 st -> c2 st.
  Infix "-->" := condImp (at level 30).
  Definition postOf (postcond: StateT -> StateT -> Prop): CondT :=
    fun post => forall pre, postcond pre post.

  Definition Disjoint (c1 c2: CondT) := forall st, c1 st -> c2 st -> False.
  Infix "-*-" := Disjoint (at level 30).

  Section PerObject.
    Variable obj: Object MsgT StateT.

    Definition Transaction (rq rsr: PMsg MsgT StateT) (rs: MsgId MsgT) :=
      obj_pmsgs obj rq /\ obj_pmsgs obj rsr /\
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
        (forall pmsg, obj_pmsgs obj pmsg ->
                      pmsg <> rsr ->
                      (precondOf pmsg) -*- trsinv) ->
        TransactionInv rq trsinv rsr.

    Definition LocallyDisjoint :=
      forall rq rsr rs,
        Transaction rq rsr rs ->
        exists trsinv,
          TransactionInv rq trsinv rsr.

    (* Inductive MonotonePMsgs: list (PMsg MsgT StateT) -> Prop := *)
    (* | MpImm: *)
    (*     forall rq, *)
    (*       msg_rqrs (midOf rq) = Rq -> *)
    (*       (forall st, exists rs, *)
    (*             outsOf rq st = rs :: nil /\ *)
    (*             isTrsPair (midOf rq) rs = true) -> *)
    (*       MonotonePMsgs (rq :: nil) *)
    (* | MpRqRs: *)
    (*     forall rq1 rs2, *)
    (*       msg_rqrs (midOf rq1) = Rq -> *)
    (*       msg_rqrs (midOf rs2) = Rs -> *)
    (*       (forall st, exists rq2, *)
    (*             outsOf rq1 st = rq2 :: nil /\ *)
    (*             isTrsPair rq2 (midOf rs2) = true) -> *)
    (*       (forall st, exists rs1, *)
    (*             outsOf rs2 st = rs1 :: nil /\ *)
    (*             isTrsPair (midOf rq1) rs1 = true) -> *)
    (*       MonotonePMsgs (rq1 :: rs2 :: nil). *)

    Definition MonotonePMsg (pmsg: PMsg MsgT StateT) :=
      match pmsg with
      | Pmsg msg _ outs _ =>
        msg_rqrs msg = Rs ->
        forall st, Forall (fun m => msg_rqrs m = Rs) (outs st) (* shouldn't be [Rq] *)
      end.

    Definition Monotone :=
      forall pmsg, obj_pmsgs obj pmsg -> MonotonePMsg pmsg.

  End PerObject.

  Section PerSystem.
    Variable sys: System MsgT StateT.

    Theorem sequential_linear: SequentialSys sys -> Linear sys.
    Proof.
    Admitted.
    
  End PerSystem.

  Theorem locally_disjoint_sequential:
    forall obj, LocallyDisjoint obj -> SequentialSys (obj :: nil).
  Proof.
  Admitted.

  Corollary locally_disjoint_linear:
    forall obj, LocallyDisjoint obj -> Linear (obj :: nil).
  Proof.
    intros; apply sequential_linear, locally_disjoint_sequential; auto.
  Qed.

End System.

Section Compositional.

  Theorem linear_sequential_compositional:
    forall {MsgT StateT} (sys: System MsgT StateT),
      Forall Monotone sys ->
      Forall (fun obj => SequentialSys (obj :: nil)) sys ->
      Linear sys.
  Proof.
  Admitted.

  Corollary disjoint_linear:
    forall {MsgT StateT} (sys: System MsgT StateT),
      Forall Monotone sys ->
      Forall LocallyDisjoint sys ->
      Linear sys.
  Proof.
    intros; apply linear_sequential_compositional; auto.
    apply Forall_impl with (P:= LocallyDisjoint); auto.
    intros; apply locally_disjoint_sequential; auto.
  Qed.

End Compositional.

