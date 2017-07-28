Require Import List String Peano_dec.
Require Import FnMap Language.

Section Reduction.
  (* Variable MsgT StateT: Type. *)

  (* Local Notation MsgId := (MsgId MsgT). *)

  (* Definition Reduced (from to: list MsgId) (msg1 msg2: MsgId) := *)
  (*   exists hst1 hst2, *)
  (*     from = hst1 ++ msg1 :: msg2 :: hst2 /\ *)
  (*     to = hst1 ++ msg2 :: msg1 :: hst2. *)

  (* Lemma reduction_preserves_steps': *)
  (*   forall {StateT} (msg1 msg2: MsgId), *)
  (*     (* msgFrom (msgOf msg1) <> msgFrom (msgOf msg2) -> *) *)
  (*     forall (obs: Objects MsgT StateT) oss1 oims1 oss2 oims2 hst2 hst1, *)
  (*       steps obs oss1 oims1 (hst1 ++ msg1 :: msg2 :: hst2) oss2 oims2 -> *)
  (*       steps obs oss1 oims1 (hst1 ++ msg2 :: msg1 :: hst2) oss2 oims2. *)
  (* Admitted. *)

  (* Theorem reduction_preserves_steps: *)
  (*   forall obs oss1 oims1 hst oss2 oims2, *)
  (*     steps obs oss1 oims1 hst oss2 oims2 -> *)
  (*     forall msg1 msg2 hst', *)
  (*       Reduced hst hst' msg1 msg2 -> *)
  (*       (* Different sources ->  *) *)
  (* (*        * Messages were handled by different objects ->  *) *)
  (* (*        * Disjoint state transitions! *) *)
  (* (*        *) *)
  (*       msgFrom (msgOf msg1) <> msgFrom (msgOf msg2) -> *)
  (*       steps obs oss1 oims1 hst' oss2 oims2. *)
  (* Proof. *)
  (*   unfold Reduced; intros. *)
  (*   destruct H0 as [hst1 [hst2 [? ?]]]; subst. *)
  (*   apply reduction_preserves_steps'; auto. *)
  (* Qed. *)

  (* Definition ReducedM (from to msgs: list Msg) (tmsg: Msg) := *)
  (*   exists hst1 hst2, *)
  (*     from = hst1 ++ msgs ++ tmsg :: hst2 /\ *)
  (*     to = hst1 ++ tmsg :: msgs ++ hst2. *)

  (* Lemma reductions_preserve_steps': *)
  (*   forall (tmsg: Msg) msgs, *)
  (*     Forall (fun m => msg_from m <> msg_from tmsg) msgs -> *)
  (*     forall obs oss1 oims1 oss2 oims2 hst2 hst1, *)
  (*       steps obs oss1 oims1 (hst1 ++ msgs ++ tmsg :: hst2) oss2 oims2 -> *)
  (*       steps obs oss1 oims1 (hst1 ++ tmsg :: msgs ++ hst2) oss2 oims2. *)
  (* Proof. *)
  (*   induction msgs; simpl; intros; auto. *)

  (*   replace (hst1 ++ a :: msgs ++ tmsg :: hst2) *)
  (*   with ((hst1 ++ a :: nil) ++ msgs ++ tmsg :: hst2) in H0 *)
  (*     by (repeat rewrite <-app_assoc; reflexivity). *)
  (*   inversion_clear H; apply IHmsgs in H0; auto. *)

  (*   rewrite <-app_assoc in H0; simpl in H0. *)
  (*   apply reduction_preserves_steps'; auto. *)
  (* Qed. *)

  (* Theorem reductions_preserve_steps: *)
  (*   forall obs oss1 oims1 hst oss2 oims2, *)
  (*     steps obs oss1 oims1 hst oss2 oims2 -> *)
  (*     forall msgs tmsg hst', *)
  (*       ReducedM hst hst' msgs tmsg -> *)
  (*       Forall (fun m => msg_from m <> msg_from tmsg) msgs -> *)
  (*       steps obs oss1 oims1 hst' oss2 oims2. *)
  (* Proof. *)
  (*   unfold ReducedM; intros. *)
  (*   destruct H0 as [hst1 [hst2 [? ?]]]; subst. *)
  (*   apply reductions_preserve_steps'; auto. *)
  (* Qed. *)

End Reduction.
        
