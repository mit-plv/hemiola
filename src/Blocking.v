Require Import List.

Require Import Common.
Require Import Syntax Semantics StepT Invariant Simulation.

Set Implicit Arguments.

(* Below we describe a semantic interpretation of a system which has a
 * blocking property.
 *
 * There can be some static conditions for a target [System] to be [Blocking].
 * For instance, each rule handling messages from a specific external channel 
 * has its own flag to block additional messages from the channel when it is
 * currently handling a certain message from that channel.
 *)

(* A possible semantic interpretation of a blocking system is:
 * A message pool [msgs] is [Blocked] if any two messages in [msgs] whose 
 * original requests [tinfo_rqin] are equivalent (≡m), i.e., from the same
 * external channel, have the same [TInfo].
 *
 * Note that [TInfo] contains both static transaction id ([mid_tid] of
 * [tinfo_rqin]) and dynamic transaction id ([tinfo_tid]).
 *)
Definition Blocked (msgs: MessagePool TMsg) :=
  forall i1 m1 i2 m2 ti1 ti2,
    InMP i1 m1 msgs -> InMP i2 m2 msgs ->
    tmsg_info m1 = Some ti1 ->
    tmsg_info m2 = Some ti2 ->
    tinfo_rqin ti1 = tinfo_rqin ti2 ->
    ti1 = ti2.

(** An informal high-level goal statement:
 * Certain shape of [Rule]s ->
 * [BlockedInv] ->
 * [ValidTrss] /\ [SimMP]
 *)
Definition BlockedInv (tst: TState) :=
  Blocked (tst_msgs tst).

Lemma BlockedInv_MsgsInv:
  MsgsInv BlockedInv.
Proof.
  split.
  - hnf; intros.
    hnf; hnf in H; intros.
    cbn in *.
    apply InMP_enqMsgs_or in H0; destruct H0.
    + exfalso; clear -H0 H2.
      induction eins; simpl; auto.
      inv H0; auto.
      inv H; discriminate.
    + apply InMP_enqMsgs_or in H1; destruct H1.
      * exfalso; clear -H1 H3.
        induction eins; simpl; auto.
        inv H1; auto.
        inv H; discriminate.
      * eauto.
  - hnf; intros.
    hnf; hnf in H; intros.
    cbn in *.
    apply InMP_deqMsgs in H0.
    apply InMP_deqMsgs in H1.
    eauto.
Qed.

