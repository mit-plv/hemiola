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
  forall m1 m2 ti1 ti2,
    InMP m1 msgs -> InMP m2 msgs ->
    tmsg_info m1 = Some ti1 ->
    tmsg_info m2 = Some ti2 ->
    map (fun msg => mid_addr (msg_id msg)) (tinfo_rqin ti1) =
    map (fun msg => mid_addr (msg_id msg)) (tinfo_rqin ti2) ->
    ti1 = ti2.

Definition BlockedInv (tst: TState) :=
  Blocked (tst_msgs tst).

(* This statement looks a bit weird at first glance, since the "first-to-first"
 * property is applied for all internal messages for which [FirstMP] holds.
 * However, it's true since [Blocked] guarantees that given a certain channel 
 * only a single set of messages (originated from the channel) are in
 * [MessagePool]. And those messages are the oldest ones for each channel,
 * which are mapped to the "first" message in spec.
 *)
Theorem blocked_int_SimMP_FirstMP:
  forall ist,
    Blocked ist ->
    forall (impl: System) msgP sst,
      SimMP msgP impl ist sst ->
      forall imsg,
        toInternal impl imsg = true ->
        FirstMP ist imsg ->
        forall smsg,
          smsg = deinitialize msgP imsg ->
          FirstMP sst smsg.
Proof.
Admitted.

Corollary blocked_SimMP_FirstMP_map:
  forall ist,
    Blocked ist ->
    forall (impl: System) msgP sst,
      SimMP msgP impl ist sst ->
      forall imsgs,
        Forall (fun msg => toInternal impl msg = true) imsgs ->
        Forall (FirstMP ist) imsgs ->
        forall smsgs,
          smsgs = deinitializeMP msgP imsgs ->
          Forall (FirstMP sst) smsgs.
Proof.
  induction imsgs; intros; subst; [constructor|].
  inv H1; inv H2; constructor; eauto.
  eapply blocked_int_SimMP_FirstMP; eauto.
Qed.

Lemma BlockedInv_MsgsInv:
  MsgsInv BlockedInv.
Proof.
  split.
  - hnf; intros.
    hnf; hnf in H; intros.
    cbn in *.
    apply in_app_or in H0; destruct H0.
    + apply in_app_or in H1; destruct H1.
      * eauto.
      * exfalso; clear -H1 H3.
        induction eins; simpl; auto.
        inv H1; auto.
        discriminate.
    + exfalso; clear -H0 H2.
      induction eins; simpl; auto.
      inv H0; auto.
      discriminate.
  - hnf; intros.
    hnf; hnf in H; intros.
    cbn in *.
    apply InMP_removeMsgs in H0.
    apply InMP_removeMsgs in H1.
    eauto.
Qed.

