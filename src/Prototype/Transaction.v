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

  End PerObject.

  Theorem locally_disjoint_linear:
    forall obs,
      Forall (fun obj => LocallyDisjoint obj) obs ->
      Linear obs.
  Proof.
  Admitted.
  
End System.

