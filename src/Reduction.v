Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT SemFacts.

(*! TODO: move the below section to MessagePool.v *)

(* Section Facts. *)
(*   Variable (MsgT: Type). *)
(*   Context `{HasMsg MsgT}. *)

(*   Lemma findMP_Some_app: *)
(*     forall from to chn mp1 q1, *)
(*       findMP from to chn mp1 = q1 -> *)
(*       forall mp2, *)
(*         exists q2, *)
(*           findMP from to chn (mp1 ++ mp2) = q1 ++ q2. *)
(*   Proof. *)
(*     unfold findMP; intros. *)

(*   Lemma FirstMP_enqMP: *)
(*     forall mp msg, *)
(*       FirstMP mp msg -> *)
(*       forall emsg, *)
(*         FirstMP (enqMP emsg mp) msg. *)
(*   Proof. *)
(*     unfold FirstMP, firstMP, enqMP; intros. *)

(* End Facts. *)

Section EquivMPFacts.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Lemma EquivMP_enqMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msg,
        EquivMP (enqMP msg mp1) (enqMP msg mp2).
  Proof.
  Admitted.

End EquivMPFacts.

Definition EquivTState (tst1 tst2: TState) :=
  tst_oss tst1 = tst_oss tst2 /\
  tst_orqs tst1 = tst_orqs tst2 /\
  EquivMP (tst_msgs tst1) (tst_msgs tst2) /\
  tst_tid tst1 = tst_tid tst2.

Ltac dest_equivT :=
  repeat
    match goal with
    | [H: EquivTState _ _ |- _] => red in H; dest; simpl in *; subst
    | [H: ?t = ?t |- _] => clear H
    end.

Definition NonSilentHistory (hst: THistory) :=
  Forall (fun tlbl => tlbl <> emptyRLabel) hst.

Definition NotMsgIn {MsgT} (lbl: RLabel MsgT) :=
  match lbl with
  | RlblIn _ => False
  | _ => True
  end.

Definition NonMsgInHistory (hst: THistory) :=
  Forall (fun tlbl => NotMsgIn tlbl) hst.

Lemma msg_in_commutes:
  forall sys st1 emsg tlbl st2,
    NotMsgIn tlbl ->
    steps step_t sys st1 [RlblIn emsg; tlbl] st2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        steps step_t sys cst1 [tlbl; RlblIn emsg] cst2 /\
        EquivTState st2 cst2.
Proof.
  intros.
  destruct tlbl as [|hdl mins mouts]; [elim H|].
  destruct cst1 as [coss1 corqs1 cmsgs1 cts1].
  repeat match goal with
         | [H: steps step_t sys _ _ _ |- _] => inv H
         | [H: step_t sys _ _ _ |- _] => inv H
         end; simpl in *.
  - eexists; split.
    + repeat econstructor; eauto.
    + dest_equivT.
      repeat split.
      apply EquivMP_enqMP; auto.
  - inv H8.
    dest_equivT.
    eexists; split.
    + econstructor.
      * repeat econstructor; eauto.
      * econstructor; try reflexivity; try eassumption.
        admit.
    + repeat split; simpl.
      admit.
Admitted.

Lemma msg_in_reduced:
  forall sys st1 emsg hst2 st2,
    steps step_t sys st1 (RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        steps step_t sys st1 (hst2 ++ [RlblIn emsg]) st2 /\
        EquivTState st2 cst2.
Proof.
  (* inv H0. *)
  (* change (RlblIn emsg :: tlbl :: hst2) with ([RlblIn emsg; tlbl] ++ hst2) in H. *)
  (* eapply steps_split in H; [|reflexivity]. *)
  (* destruct H as [sti [? ?]]. *)
  (* apply msg_in_commutes in H0; auto. *)
  (* pose proof (steps_append H H0); clear H H0. *)
  (* simpl in H1; inv H1. *)
  (* specialize (IHhst2 _ H5 H4). *)
  (* simpl; econstructor; eassumption. *)
Admitted.

Lemma msg_in_reduced_app:
  forall sys st1 hst1 emsg hst2 st2,
    steps step_t sys st1 (hst1 ++ RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        steps step_t sys st1 (hst1 ++ hst2 ++ [RlblIn emsg]) st2 /\
        EquivTState st2 cst2.
Proof.
  (* intros. *)
  (* eapply steps_split in H; [|reflexivity]. *)
  (* destruct H as [sti [? ?]]. *)
  (* eapply msg_in_reduced in H; eauto; dest. *)
  
  (* eapply steps_append; eauto. *)
Admitted.

