Require Import List String Peano_dec.
Require Import FnMap Language.

Section Reduction.
  Variable MsgT StateT: Type.

  Local Notation MsgId := (MsgId MsgT).
  Local Notation Label := (Label MsgT).

  Definition Reduced (from to: list Label) (lbl1 lbl2: Label) :=
    exists hst1 hst2,
      from = hst1 ++ lbl1 :: lbl2 :: hst2 /\
      to = hst1 ++ lbl2 :: lbl1 :: hst2.

  Lemma reduction_preserves_steps'':
    forall {StateT} (lbl1 lbl2: Label),
      msgTo (lbl_in lbl1) <> msgFrom (lbl_in lbl2) ->
      msgTo (lbl_in lbl1) <> msgTo (lbl_in lbl2) ->
      forall (obs: Objects MsgT StateT) oss1 oims1 oss2 oims2 hst,
        steps obs oss1 oims1 (lbl1 :: lbl2 :: hst) oss2 oims2 ->
        steps obs oss1 oims1 (lbl2 :: lbl1 :: hst) oss2 oims2.
  Proof.
    intros.
    inversion_clear H1; inversion_clear H2.

    repeat econstructor; try eassumption; clear H1.
  Admitted.
  
  Lemma reduction_preserves_steps':
    forall {StateT} (lbl1 lbl2: Label),
      msgTo (lbl_in lbl1) <> msgFrom (lbl_in lbl2) ->
      msgTo (lbl_in lbl1) <> msgTo (lbl_in lbl2) ->
      forall (obs: Objects MsgT StateT) hst1 oss1 oims1 oss2 oims2 hst2,
        steps obs oss1 oims1 (hst1 ++ lbl1 :: lbl2 :: hst2) oss2 oims2 ->
        steps obs oss1 oims1 (hst1 ++ lbl2 :: lbl1 :: hst2) oss2 oims2.
  Proof.
    induction hst1; simpl; intros.
    - apply reduction_preserves_steps''; auto.
    - inversion_clear H1.
      econstructor; eauto.
  Qed.

  Theorem reduction_preserves_steps:
    forall (obs: Objects MsgT StateT) oss1 oims1 hst oss2 oims2,
      steps obs oss1 oims1 hst oss2 oims2 ->
      forall lbl1 lbl2 hst',
        Reduced hst hst' lbl1 lbl2 ->
        msgTo (lbl_in lbl1) <> msgFrom (lbl_in lbl2) ->
        msgTo (lbl_in lbl1) <> msgTo (lbl_in lbl2) ->
        steps obs oss1 oims1 hst' oss2 oims2.
  Proof.
    unfold Reduced; intros.
    destruct H0 as [hst1 [hst2 [? ?]]]; subst.
    apply reduction_preserves_steps'; auto.
  Qed.

End Reduction.
        
