Require Import List String Peano_dec.
Require Import FnMap Language.

Set Implicit Arguments.

Section Reduction.
  Variable MsgT StateT: Type.

  Local Notation MsgId := (MsgId MsgT).
  Local Notation Label := (Label MsgT).

  (** Utilities end *)

  Definition Reduced (from to: list Label) (lbl1 lbl2: Label) :=
    exists hst1 hst2,
      from = hst1 ++ lbl1 :: lbl2 :: hst2 /\
      to = hst1 ++ lbl2 :: lbl1 :: hst2.

  Lemma reduction_preserves_steps'':
    forall lbl1 lbl2: Label,
      msgTo (lbl_in lbl1) <> msgFrom (lbl_in lbl2) ->
      msgTo (lbl_in lbl1) <> msgTo (lbl_in lbl2) ->
      forall (obs: Objects MsgT StateT) oss1 oims1 oss2 oims2 hst,
        steps obs oss1 oims1 (lbl1 :: lbl2 :: hst) oss2 oims2 ->
        steps obs oss1 oims1 (lbl2 :: lbl1 :: hst) oss2 oims2.
  Proof.
    intros.
    inv H1; inv H6.
    inv H9; inv H10.

    simpl in *.
    pose proof (step_obj_idx H6).
    pose proof (step_obj_idx H11).
    rewrite H7, H10 in H0.

    rewrite idx_add_comm by assumption.
    rewrite <-distributeMsgs_idx_add_comm; [|exact StateT|auto].
    rewrite distributeMsgs_comm by assumption.
    rewrite idx_add_comm with (k1 := obj_idx obj) by assumption.
    rewrite distributeMsgs_idx_add_comm; [|exact StateT|assumption].

    econstructor; [econstructor|]; try eassumption; clear H5.
    - econstructor.
      + exact H1.
      + reflexivity.
      + rewrite find_idx_add_neq in H3 by assumption.
        eassumption.
      + rewrite find_distributeMsgs_neq in H4 by assumption.
        rewrite find_idx_add_neq in H4 by assumption.
        eassumption.
      + eassumption.
      + reflexivity.
    - econstructor.
      + exact H2.
      + reflexivity.
      + rewrite find_idx_add_neq by auto.
        eassumption.
      + rewrite find_distributeMsgs_neq by auto.
        rewrite find_idx_add_neq by auto.
        eassumption.
      + eassumption.
      + reflexivity.
  Qed.
  
  Lemma reduction_preserves_steps':
    forall lbl1 lbl2: Label,
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
        
