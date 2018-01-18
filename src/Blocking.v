Require Import Common.
Require Import Syntax Semantics StepDet.

(* Below we describe a semantic interpretation of a system which has a
 * blocking property.
 *
 * There can be some static conditions for a target [System] to be [Blocking], 
 * for instance, each rule handling messages from a specific external channel 
 * has its own flag to block additional messages from the channel when it is
 * currently handling a certain message from that channel.
 *)

(* A message pool [msgs] is [Blocked] if any two messages in [msgs] whose 
 * original requests [tinfo_rqin] are equivalent (≡m), i.e., from the same
 * external channel, have the same [TInfo].
 *
 * Note that [TInfo] contains both static transaction id ([mid_tid] of
 * [tinfo_rqin]) and dynamic transaction id ([tinfo_tid]).
 *)
Definition Blocked (msgs: Messages TMsg) :=
  forall m1 m2 ti1 ti2,
    InM m1 msgs -> InM m2 msgs ->
    tmsg_info m1 = Some ti1 ->
    tmsg_info m2 = Some ti2 ->
    mid_addr (msg_id (tinfo_rqin ti1)) = mid_addr (msg_id (tinfo_rqin ti2)) ->
    ti1 = ti2.

Definition BlockedInv (tst: TState) :=
  Blocked (tst_msgs tst).

(* When two messages in the same channel are handled, [steps_det] ensures that 
 * the two messages have different [tinfo_tid]s. Thus, if a target [System] has 
 * a blocking property, then any reachable states should be [Blocked].
 *)
Definition Blocking (sys: System) :=
  forall st: TState,
    Reachable steps_det sys st ->
    Blocked (tst_msgs st).

Require Import TrsSim.

Section Facts.

  Lemma BlockedInv_in:
    forall sys, TrsSimSepGInvIn BlockedInv sys.
  Proof.
    unfold TrsSimSepGInvIn; intros.
    inv H0.
    unfold BlockedInv, Blocked in *; simpl in *; intros.
  Admitted.

  (* TODO: define a simulation for {impl, spec} messages;
   * prove [Blocked .. -> Simulation .. -> (relation between [firstM])
   *)

End Facts.

