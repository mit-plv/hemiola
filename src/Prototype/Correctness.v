Require Import Bool List String Peano_dec Eqdep.
Require Import FnMap Language SingleValue.

Ltac inv H := inversion H; subst; clear H.
Ltac dest_in :=
  repeat
    match goal with
    | [H: In _ _ |- _] => inv H
    end.
Ltac dest_existT :=
  repeat match goal with
         | [H: existT _ _ _ = existT _ _ _ |- _] =>
           try (pose proof (eq_sigT_fst H); subst);
           apply EqdepTheory.inj_pair2 in H; subst
         end.

Section ParentSequential.

  Definition parentObj :=
    existT (fun st => Object SingleValueMsg st) ParentState parent :: nil.

  Definition parentRequestFrom (os: ObjectState ParentState) :=
    match ps_request_from (os_state os) with
    | Some (from, _) => Some (from, parentIdx)
    | None => None
    end.

  Ltac invert_step :=
    repeat
      match goal with
      | [H: step _ _ _ _ _ _ _ |- _ ] => inv H
      | [H: step_obj _ _ _ _ _ _ _ _ |- _ ] => inv H
      end.

  Ltac invert_step_rule :=
    repeat
      match goal with
      | [H: step_rule _ _ _ = Some _ |- _] =>
        simpl in H;
        repeat
          match goal with
          | [H: match ?t with
                | Some _ => Some _
                | None => _
                end = Some _ |- _] =>
            let trs := fresh "trs" in
            remember t as trs; destruct trs
          end; try discriminate
      | [H: Some _ = Some _ |- _] => inv H
      end.

  Lemma parent_sequential':
    forall hst oss1 msgs1 oss2 msgs2,
      steps parentObj oss1 msgs1 hst oss2 msgs2 ->
      forall pos1 pos2,
        find parentIdx oss1 = Some (existT _ (ParentState: Type) pos1) ->
        find parentIdx oss2 = Some (existT _ (ParentState: Type) pos2) ->
        Sequential' (intHistory (getIndices parentObj) hst)
                    (parentRequestFrom pos1) (parentRequestFrom pos2).
  Proof.
    induction 1; simpl; intros; subst;
      [rewrite H in H0; inv H0; dest_existT; reflexivity|].

    invert_step.

    - (* internal *)
      dest_in; dest_existT.
      cbv in H2; inv H2; dest_existT.
      specialize (IHsteps _ _ H1 H6).
      invert_step_rule.

      + (* getReq *)
        destruct msg_in as [msg_in_type msg_in_from msg_in_to msg_in_content]; simpl in *.
        unfold ParentGetReq in Heqtrs; simpl in Heqtrs.
        remember (from_external msg_in_from) as msg_in_from_ext.
        destruct msg_in_from_ext; try discriminate.
        destruct msg_in_content; try discriminate.
        destruct msg_in_type; try discriminate.
        remember (os_state os) as oss.
        destruct oss as [oss_is_valid oss_value oss_request_from]; simpl in *.
        destruct oss_request_from; try discriminate.
        destruct oss_is_valid; inv Heqtrs; simpl in *.
        * rewrite intHistory_app; simpl.
          eapply sequential_app; eauto.
          simpl; unfold parentRequestFrom; rewrite <-Heqoss; simpl.
          split; auto.
          unfold isObjectsMsg, buildMsg; simpl.
          rewrite orb_true_r; simpl.
          repeat split.
        * rewrite intHistory_app; simpl.
          eapply sequential_app; eauto.
          simpl; unfold parentRequestFrom; rewrite <-Heqoss; simpl.
          split; auto.
          replace (isObjectsMsg
                     (parentIdx :: nil)
                     (buildMsg Req parentIdx (theOtherChild msg_in_from) SvmInvReq)) with false.
          { reflexivity. }
          { unfold isObjectsMsg, buildMsg.
            unfold msg_to, msg_type.
            apply eq_sym, orb_false_iff; split; auto.
            destruct (in_dec _ _ _); auto.
            simpl in i; destruct i; inv H4.
            unfold theOtherChild in H9.
            destruct (eq_nat_dec _ _) in H9; discriminate.
          }
        
      + (* setReq *)
        admit.

      + (* invResp *)
        admit.

    - (* external: contradiction *)
      exfalso; admit.
    
  Admitted.
  
  Lemma parent_intHistory_sequential:
    forall hst,
      HistoryOf parentObj hst ->
      Sequential (intHistory (getIndices parentObj) hst).
  Proof.
    unfold HistoryOf, Sequential; intros.
    destruct H as [oss [oims ?]].
    pose proof H; apply steps_poststate_valid in H0.
    - destruct H0; destruct H0 as [os ?].
      eapply parent_sequential' in H; try reflexivity; eauto.
    - repeat split.
      eexists; reflexivity.
  Qed.

End ParentSequential.
  
Lemma parent_intLinear:
  IntLinear (existT (fun st => Object SingleValueMsg st) ParentState parent :: nil).
Proof.
  unfold IntLinear, AbsLinear; intros.
  exists (complete hst); split; auto.
  - admit. (* HistoryOf hst -> HistoryOf (complete hst) *)
  - rewrite intHistory_complete_comm.
    unfold Linearlizable'; split; auto.
    apply sequential_complete.
    apply parent_intHistory_sequential; auto.
Admitted.

Lemma child_intLinear:
  forall i, IntLinear (existT (fun st => Object SingleValueMsg st) ChildState (child i) :: nil).
Proof.
Admitted.

Theorem impl_linear: ExtLinear impl.
Proof.
  apply extLinear_local.
  intros; dest_in.
  - apply parent_intLinear.
  - apply child_intLinear.
  - apply child_intLinear.
Qed.  

