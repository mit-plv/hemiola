Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutable QuasiSeq Topology.
Require Import RqRsTopo RqRsInv.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(* TODOs:
 * 0. Have a notion of transaction paths ([TrsPath]) that includes a 
 *    "transaction type" of each object (e.g., upward-request, downward-request,
 *    etc.).
 * 1. An [Atomic] step --> exists a corresponding [TrsPath]
 * 2. For each history [hst] between continuous histories [h1] and [h2]:
 *    we need to have a way to check whether [hst] is right- or left-pushable.
 * 3. 1) Theorem (disjointness between [h1] and [h2]):
 *    [h1 -*- h2], where 
 *    [h1 -*- h2 ≜ rqsOf(h1) -*- rqsOf(h2) /\ rssOf(h1) -*- rssOf(h2)].
 *    Note that [-*-] is not commutative.
 *    2) Theorem (disjointness of [hst]): [∀hst. h1 -*- hst \/ hst -*- h2]
 * 4. Theorem: [∀h1 h2. h1 -*- h2 -> MDisjoint h1 h2 -> Commutable h1 h2]
 *)

Section Pushable.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Variables (phst: MHistory)
            (oidx ridx: IdxT)
            (rins routs: list (Id Msg)).
  Hypothesis (Hcont: ValidExtContinuousL
                       sys phst (RlblInt oidx ridx rins routs)).

  Local Definition nlbl := (RlblInt oidx ridx rins routs).
  
  (*   RqUpMsgs dtr oidx rins \/ *)
  (*   (RqDownMsgs dtr oidx rins /\ *)
  (*    SubList (rssOf hst) (subtreeInds dtr (parentOf dtr oidx))). *)
  Definition RqRsLPush (hst: MHistory): Prop :=
    DisjList (rssOf phst) (rssOf hst).

  (*   RsUpMsgs dtr oidx rins \/ *)
  (*   RsDownMsgs dtr oidx rins \/ *)
  (*   (RqDownMsgs dtr oidx rins /\ *)
  (*    DisjList (rssOf hst) (subtreeInds dtr (parentOf dtr oidx))). *)
  Definition RqRsRPush (hst: MHistory): Prop :=
    ~ In oidx (rssOf hst).

  Lemma rqrs_previous_rpush: RqRsRPush phst.
  Proof.
    (** requires the [GoodIteration] invariant *)
  Admitted.

  Lemma rqrs_next_lpush: RqRsLPush [RlblInt oidx ridx rins routs].
  Proof.
    (** requires the [GoodIteration] invariant *)
  Admitted.

  Lemma rqrs_lpush_or_rpush:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
        Forall (fun hst => Discontinuous phst hst) hsts ->
        Forall (fun hst => RqRsLPush hst \/ RqRsRPush hst) hsts.
  Proof.
  Admitted.

  Lemma rqrs_left_right_pushable_phst:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
        Forall (fun hst => Discontinuous phst hst) hsts ->
        LRPushable sys RqRsLPush RqRsRPush (hsts ++ [phst]).
  Proof.
  Admitted.

  Lemma rqrs_left_right_pushable_nlbl:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall hsts st2,
        Forall (AtomicEx msg_dec) hsts ->
        steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
        Forall (fun hst => Discontinuous phst hst) hsts ->
        LRPushable sys RqRsLPush RqRsRPush ([nlbl] :: hsts).
  Proof.
  Admitted.

End Pushable.

Theorem rqrs_pushable:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    Pushable sys.
Proof.
  intros; red; intros.

  assert (exists oidx ridx rins routs,
             l2 = RlblInt oidx ridx rins routs) as Hnlbl.
  { inv H0; inv H1.
    destruct H0 as [oidx [ridx [rins [routs ?]]]]; dest; subst.
    do 4 eexists; reflexivity.
  }
  destruct Hnlbl as [oidx [ridx [rins [routs ?]]]]; subst.
  
  exists (RqRsLPush hst1), (RqRsRPush oidx).
  repeat split.
  - eauto using rqrs_previous_rpush.
  - eauto using rqrs_next_lpush.
  - eauto using rqrs_lpush_or_rpush.
  - eauto using rqrs_left_right_pushable_phst.
  - eauto using rqrs_left_right_pushable_nlbl.
Qed.

Corollary rqrs_serializable:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    SerializableSys sys.
Proof.
  intros.
  apply well_interleaved_serializable.
  apply well_interleaved_push_ok.
  eapply rqrs_pushable; eauto.
Qed.

Close Scope list.
Close Scope fmap.
