Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Definition lastOIdxOf (hst: MHistory): option IdxT :=
  match hst with
  | RlblInt oidx _ _ _ :: _ => Some oidx
  | _ => None
  end.

Definition oidxOf (lbl: MLabel) :=
  match lbl with
  | RlblInt oidx _ _ _ => Some oidx
  | _ => None
  end.

Fixpoint oindsOf (hst: MHistory) :=
  match hst with
  | nil => nil
  | lbl :: hst' => (oidxOf lbl) ::> (oindsOf hst')
  end.

Lemma atomic_lastOIdxOf:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    exists loidx,
      lastOIdxOf hst = Some loidx.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Section Covers.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Definition RqUpCoverInv (oinds: list IdxT) (rqUp: Id Msg) :=
    forall ruFrom ruTo,
      msg_type (valOf rqUp) = MRq ->
      parentIdxOf dtr ruFrom = Some ruTo ->
      rqEdgeUpFrom dtr ruFrom = Some (idOf rqUp) ->
      SubList oinds (subtreeIndsOf dtr ruFrom).

  Definition RqDownCoverInv (oinds: list IdxT) (rqDown: Id Msg) :=
    forall rdFrom rdTo,
      msg_type (valOf rqDown) = MRq ->
      parentIdxOf dtr rdTo = Some rdFrom ->
      edgeDownTo dtr rdTo = Some (idOf rqDown) ->
      DisjList oinds (subtreeIndsOf dtr rdTo).

  Definition RsUpCoverInv (oinds: list IdxT) (rsUp: Id Msg) :=
    True.

  Definition RsDownCoverInv (oinds: list IdxT) (rsDown: Id Msg) :=
    forall rdFrom rdTo,
      msg_type (valOf rsDown) = MRs ->
      parentIdxOf dtr rdTo = Some rdFrom ->
      edgeDownTo dtr rdTo = Some (idOf rsDown) ->
      DisjList oinds (subtreeIndsOf dtr rdTo).

  Definition CoverInvMsg (oinds: list IdxT) (eout: Id Msg) :=
    RqUpCoverInv oinds eout /\
    RqDownCoverInv oinds eout /\
    RsUpCoverInv oinds eout.

  Definition CoverInv (oinds: list IdxT) (eouts: list (Id Msg)) :=
    Forall (CoverInvMsg oinds) eouts.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok.
  
  (* Lemma cover_inv: *)
  (*   forall inits ins hst outs eouts, *)
  (*     Atomic msg_dec inits ins hst outs eouts -> *)
  (*     forall s1 s2, *)
  (*       Reachable (steps step_m) sys s1 -> *)
  (*       steps step_m sys s1 hst s2 -> *)
  (*       CoverInv (oindsOf hst) eouts. *)
  (* Proof. *)
  (*   destruct Hrrs as [? [? ?]]. *)
  (*   induction 1; simpl; intros. *)

  (*   - inv_steps; inv_step. *)
  (*     admit. *)
  (*     (* good_rqrs_rule_get rule. *) *)
  (*     (* good_rqrs_rule_cases rule. *) *)


  (*   - inv_steps; inv_step. *)

End Covers.

Close Scope list.
Close Scope fmap.

