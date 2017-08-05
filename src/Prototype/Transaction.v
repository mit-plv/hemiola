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

    (* A VERY SUBTLE POINT:
     * [rsr] is not a [PMsg] that handles the response,
     * but a [PMsg] that _sends_ the response.
     *)
    Definition Transaction (rq rsr: PMsg MvalT StateT) (rs: Msg MvalT) :=
      In rq (obj_pmsgs obj) /\ In rsr (obj_pmsgs obj) /\
      (exists st mt, In rs (pmsg_outs rsr st mt)) /\
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

    (*! Restricted interference *)

    (* Interferences are allowed only by prioritizers. Specifically, during a 
     * given transaction handling a request from a process (object) with index "i":
     * 1) Any other transactions with indices >= i should be disjoint.
     * 2) Transactions with indices < i are allowed to interleave, but they should
     *    be locally linearizable.
     *)

    (* TODO: formalize *)

    (*! Monotonicity *)
    
    Definition Immediate (rq: PMsg MvalT StateT) :=
      msg_rqrs (pmsg_mid rq) = Rq /\
      forall st mt, exists rs,
          pmsg_outs rq st mt = rs :: nil /\
          isTrsPair (pmsg_mid rq) (msg_id rs) = true.

    Definition Forwarding (rq1 rs2: PMsg MvalT StateT) :=
      msg_rqrs (pmsg_mid rq1) = Rq /\
      msg_rqrs (pmsg_mid rs2) = Rs /\
      (forall st mt, exists rq2,
            pmsg_outs rq1 st mt = rq2 :: nil /\
            isTrsPair (msg_id rq2) (pmsg_mid rs2) = true) /\
      (forall st mt, exists rs1,
            pmsg_outs rs2 st mt = rs1 :: nil /\
            isTrsPair (pmsg_mid rq1) (msg_id rs1) = true).

    Definition UniqueHandler (pmsgs: list (PMsg MvalT StateT))
               (pmsg: PMsg MvalT StateT) :=
      In pmsg pmsgs /\
      forall pmsg', In pmsg' pmsgs -> (pmsg_mid pmsg) <> (pmsg_mid pmsg').
    
    (* Monotonicity is one of key factors whether a given protocol in a 
     * message-passing system is linearizable or not. It basically requires the
     * whole system always performs a "monotone" transaction; informally, an 
     * object is monotone if there is no predicated message that
     * receives a response and sends some requests.
     *)
    Definition MonotonePMsgs (pmsgs: list (PMsg MvalT StateT)): Prop :=
      forall (pmsg: PMsg MvalT StateT),
        In pmsg pmsgs ->
        (Immediate pmsg \/
         (exists (rs: PMsg MvalT StateT),
             Forwarding pmsg rs /\ UniqueHandler pmsgs rs) \/
         (exists (rq: PMsg MvalT StateT),
             Forwarding rq pmsg /\ UniqueHandler pmsgs pmsg)).

    Definition Monotone := MonotonePMsgs (obj_pmsgs obj).

  End PerObject.

  Section PerSystem.
    Variable sys: System MvalT StateT.

    Theorem sequential_linear: SequentialSys msgT_dec sys -> Linear msgT_dec sys.
    Proof.
    Admitted.
    
  End PerSystem.

  Theorem locally_disjoint_sequential:
    forall obj, LocallyDisjoint obj -> SequentialSys msgT_dec (obj :: nil).
  Proof.
  Admitted.

  Corollary locally_disjoint_linear:
    forall obj, LocallyDisjoint obj -> Linear msgT_dec (obj :: nil).
  Proof.
    intros; apply sequential_linear, locally_disjoint_sequential; auto.
  Qed.

End System.

Section Compositional.
  Context {MsgT StateT: Type}.
  Context {MvalT: MsgT -> RqRs -> Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).

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

End Compositional.

