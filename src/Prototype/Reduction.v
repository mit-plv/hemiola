Require Import List String Peano_dec.
Require Import FnMap Language.

Section Reduction.
  Variable MsgT: Type.
  Definition Msg := Msg MsgT.

  Definition Reduced (from to: list Msg) (msg1 msg2: Msg) :=
    exists hst1 hst2,
      from = hst1 ++ (msg1 :: msg2 :: hst2) /\
      to = hst1 ++ (msg2 :: msg1 :: hst2).

  Lemma reduction_preserved_steps':
    forall msg1 msg2: Msg,
      msg_from msg1 <> msg_from msg2 ->
      forall oss1 oims1 oss2 oims2 hst2 hst1,
        steps oss1 oims1 (hst1 ++ msg1 :: msg2 :: hst2) oss2 oims2 ->
        steps oss1 oims1 (hst1 ++ msg2 :: msg1 :: hst2) oss2 oims2.
  Proof.
    induction hst1; simpl; intros.
    - admit.
    - admit.
  Admitted.

  Theorem reduction_preserved_steps:
    forall oss1 oims1 hst oss2 oims2,
      steps oss1 oims1 hst oss2 oims2 ->
      forall msg1 msg2 hst',
        Reduced hst hst' msg1 msg2 ->
        msg_from msg1 <> msg_from msg2 -> (* Different sources -> 
                                           * Messages were handled by different objects -> 
                                           * Disjoint state transitions!
                                           *)
        steps oss1 oims1 hst' oss2 oims2.
  Proof.
    intros.
    unfold Reduced; intros.
    destruct H0 as [hst1 [hst2 [? ?]]]; subst.
    apply reduction_preserved_steps'; auto.
  Qed.

End Reduction.
        
