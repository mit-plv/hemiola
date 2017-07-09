Require Import List String Peano_dec Eqdep.
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
           (apply EqdepTheory.inj_pair2 in H; subst)
         end.

Section ParentSequential.

  Definition parentObj :=
    existT (fun st => Object SingleValueMsg st) ParentState parent :: nil.

  Lemma parent_sequential':
    forall hst oss1 msgs1 oss2 msgs2,
      steps parentObj oss1 msgs1 hst oss2 msgs2 ->
      forall pos ss,
        find parentIdx oss1 = Some (existT _ (ParentState: Type) pos) ->
        ss = match ps_request_from (os_state pos) with
             | Some (from, _) => Some (from, parentIdx)
             | None => None
             end ->
        Sequential' (intHistory (getIndices parentObj) hst) ss.
  Proof.
    induction 1; simpl; intros; auto; subst.

    inv H0; inv H6.
    - (* internal *)
      inv H2; [|inv H6].
      pose proof (eq_sigT_fst H6); subst; dest_existT.

      specialize (IHsteps _ _ H1 eq_refl).

      simpl in H3.
      remember (ParentGetReq msg_in (os_state os)) as getReqV; destruct getReqV.
      + (* getReq *)
        inv H3.
        destruct msg_in as [msg_in_type msg_in_from msg_in_to msg_in_content]; simpl in *.
        unfold ParentGetReq in HeqgetReqV; simpl in HeqgetReqV.
        remember (from_external msg_in_from) as msg_in_from_ext.
        destruct msg_in_from_ext; try discriminate.
        destruct msg_in_content; try discriminate.
        remember (os_state os) as oss.
        destruct oss as [oss_is_valid oss_value oss_request_from]; simpl in *.
        destruct oss_request_from; try discriminate.
        destruct oss_is_valid; inv HeqgetReqV; simpl in *.
        * admit.
        * admit.
        
      + remember (ParentSetReq msg_in (os_state os)) as setReqV; destruct setReqV.
        * (* setReq *)
          admit.
        * remember (ParentInvResp msg_in (os_state os)) as invRespV;
            destruct invRespV; [|discriminate].
          (* invResp *)
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
    eapply parent_sequential' in H; eauto; reflexivity.
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

