Require Import List.

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

