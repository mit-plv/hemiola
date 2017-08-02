Require Import Bool List String Peano_dec.
Require Import FnMap Language.

Section System.
  Context {MsgT StateT: Type}.

  Definition CondT := StateT -> Prop.
  Definition condImp (c1 c2: CondT) := forall st, c1 st -> c2 st.
  Infix "-->" := condImp (at level 30).
  Definition postOf (postcond: StateT -> MsgT -> StateT -> Prop): CondT :=
    fun post => forall pre mt, postcond pre mt post.

  Definition Disjoint (c1 c2: CondT) := forall st, c1 st -> c2 st -> False.
  Infix "-*-" := Disjoint (at level 30).

  Section PerObject.
    Variable obj: Object MsgT StateT.

    Definition Transaction (rq rsr: PMsg MsgT StateT) (rs: Msg MsgT) :=
      In rq (obj_pmsgs obj) /\ In rsr (obj_pmsgs obj) /\
      (exists st mt, In rs (outsOf rsr st mt)) /\
      isTrsPair (midOf rq) (msg_id rs) = true.

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
        (forall pmsg, In pmsg (obj_pmsgs obj) ->
                      pmsg <> rsr ->
                      (precondOf pmsg) -*- trsinv) ->
        TransactionInv rq trsinv rsr.

    Definition LocallyDisjoint :=
      forall rq rsr rs,
        Transaction rq rsr rs ->
        exists trsinv,
          TransactionInv rq trsinv rsr.

    Definition Immediate (rq: PMsg MsgT StateT) :=
      msg_rqrs (midOf rq) = Rq /\
      forall st mt, exists rs,
          outsOf rq st mt = rs :: nil /\
          isTrsPair (midOf rq) (msg_id rs) = true.

    Definition Forwarding (rq1 rs2: PMsg MsgT StateT) :=
      msg_rqrs (midOf rq1) = Rq /\
      msg_rqrs (midOf rs2) = Rs /\
      (forall st mt, exists rq2,
            outsOf rq1 st mt = rq2 :: nil /\
            isTrsPair (msg_id rq2) (midOf rs2) = true) /\
      (forall st mt, exists rs1,
            outsOf rs2 st mt = rs1 :: nil /\
            isTrsPair (midOf rq1) (msg_id rs1) = true).

    Definition UniqueHandler (pmsgs: list (PMsg MsgT StateT))
               (pmsg: PMsg MsgT StateT) :=
      In pmsg pmsgs /\
      forall pmsg', In pmsg' pmsgs -> midOf pmsg <> midOf pmsg'.
    
    (* Monotonicity is one of key factors whether a given protocol in a 
     * message-passing system is linearizable or not. It basically requires the
     * whole system always performs a "monotone" transaction; informally, an 
     * object is monotone if there is no predicated message that
     * receives a response and sends some requests.
     *)
    Definition MonotonePMsgs (pmsgs: list (PMsg MsgT StateT)): Prop :=
      forall pmsg,
        In pmsg pmsgs ->
        (Immediate pmsg \/
         (exists rs, Forwarding pmsg rs /\ UniqueHandler pmsgs rs) \/
         (exists rq, Forwarding rq pmsg /\ UniqueHandler pmsgs pmsg)).

    Definition Monotone := MonotonePMsgs (obj_pmsgs obj).

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

