Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepDet Serial TrsInv.

Require Import Omega.
Require Import Program.Equality.

Set Implicit Arguments.

Lemma atomic_emptyILabel_not_in:
  forall sys ti hst mouts orsout,
    Atomic sys ti hst mouts orsout ->
    ~ In emptyILabel hst.
Proof.
  induction 1; simpl; intros.
  - intro Hx; destruct Hx; [discriminate|auto].
  - intro Hx; elim IHAtomic; destruct Hx; [discriminate|assumption].
  - intro Hx; elim IHAtomic; destruct Hx; [discriminate|assumption].
Qed.

Lemma atomic_iLblIn_not_in:
  forall sys ti hst mouts orsout,
    Atomic sys ti hst mouts orsout ->
    forall msg,
      ~ In (IlblIn msg) hst.
Proof.
  induction 1; simpl; intros; [auto| |];
    try (intro Hx; destruct Hx;
         [discriminate|firstorder]).
Qed.

Lemma atomic_preserved:
  forall impl1 ti hst mouts orsout,
    Atomic impl1 ti hst mouts orsout ->
    forall impl2,
      indicesOf impl1 = indicesOf impl2 ->
      Atomic impl2 ti hst mouts orsout.
Proof.
  induction 1; simpl; intros.
  - econstructor; eauto.
    + unfold isExternal in *.
      rewrite H1 in H; assumption.
    + unfold isExternal in *.
      rewrite H1 in H0; assumption.
  - econstructor; eauto.
    unfold isInternal in *.
    rewrite H2 in H1; assumption.
  - econstructor; eauto.
    unfold isExternal in *.
    rewrite H1 in H0; assumption.
Qed.

Lemma atomic_rs_out_1:
  forall sys ti hdl rsout hst mouts orsout,
    Atomic sys ti (IlblOuts (Some hdl) (rsout :: nil) :: hst) mouts orsout ->
    isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true ->
    mouts = nil /\ orsout = Some rsout.
Proof.
  intros; inv H; auto.
  exfalso.
  inv H9.
  eapply internal_external_false; eauto.
Qed.

Lemma atomic_rs_out_2:
  forall sys ti hst mouts rsout,
    Atomic sys ti hst mouts (Some rsout) ->
    hst <> nil /\
    isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true /\
    mouts = nil /\
    exists hdl hst', hst = (IlblOuts (Some hdl) (rsout :: nil) :: hst').
Proof.
  intros; inv H;
    try (repeat split; eauto; discriminate).
Qed.

(* Lemma atomic_tinfo: *)
(*   forall sys ti hst mouts orsout, *)
(*     Atomic sys ti hst mouts orsout -> *)
(*     forall st1 st2, *)
(*       steps_det sys st1 hst st2 -> *)
(*       Forall (fun lbl => match lbl with *)
(*                          | IlblOuts (Some hdl) _ => *)
(*                            tmsg_info hdl = Some ti *)
(*                          | _ => False *)
(*                          end) hst /\ *)
(*       ForallMP (fun tmsg => tmsg_info tmsg = Some ti) mouts. *)
(* Proof. *)
(*   induction 1; simpl; intros. *)
(*   - discriminate. *)
(*   - inv H3; inv H4. *)
(*     destruct otid as [tid|]. *)
(*     + destruct H0; [discriminate|inv H0]. *)
(*       specialize (IHAtomic _ eq_refl _ _ H7); destruct IHAtomic. *)
(*       inv H9. *)
(*       split. *)
(*       * eapply ForallMP_forall in H3; [|exact H1]. *)
(*         eauto. *)
(*       * apply ForallMP_distributeMsgs. *)
(*         { eapply ForallMP_removeOnce; eauto. } *)
(*         { clear; induction (rule_outs _ _ _); [constructor|]. *)
(*           constructor; auto. *)
(*         } *)
(*     + inv H. *)
(*       Common.dest_in. *)
(*       split; auto. *)
(*       unfold enqMP; rewrite app_nil_l. *)
(*       unfold removeOnce. *)
(*       destruct (tmsg_dec _ _); [|elim n; reflexivity]. *)
(*       simpl. *)
(*       inv H9. *)
(*       clear; induction (rule_outs _ _ _); [constructor|]. *)
(*       constructor; auto. *)

(*   - split; [|constructor]. *)
(*     inv H2; inv H3. *)
(*     destruct otid as [tid|]. *)
(*     + destruct H0; [discriminate|inv H0]. *)
(*       specialize (IHAtomic _ eq_refl _ _ H6); destruct IHAtomic. *)
(*       constructor; auto. *)
(*     + inv H. *)
(*       constructor; auto. *)
(* Qed. *)

(* Corollary atomic_hst_tinfo: *)
(*   forall sys tid rqin hst mouts orsout, *)
(*     Atomic sys (Some tid) rqin hst mouts orsout -> *)
(*     forall st1 st2, *)
(*       steps_det sys st1 hst st2 -> *)
(*       Forall (fun lbl => match lbl with *)
(*                          | IlblOuts (Some hdl) _ => *)
(*                            tmsg_info hdl = Some (buildTInfo tid rqin) *)
(*                          | _ => False *)
(*                          end) hst. *)
(* Proof. *)
(*   intros. *)
(*   eapply atomic_tinfo in H; eauto. *)
(*   destruct H; auto. *)
(* Qed. *)

(* Corollary atomic_mouts_tinfo: *)
(*   forall sys tid rqin hst mouts orsout, *)
(*     Atomic sys (Some tid) rqin hst mouts orsout -> *)
(*     forall st1 st2, *)
(*       steps_det sys st1 hst st2 -> *)
(*       ForallMP (fun tmsg => tmsg_info tmsg = Some (buildTInfo tid rqin)) mouts. *)
(* Proof. *)
(*   intros. *)
(*   eapply atomic_tinfo in H; eauto. *)
(*   destruct H; auto. *)
(* Qed. *)

Lemma trsMessages_app:
  forall ti mp1 mp2,
    trsMessages ti (mp1 ++ mp2) =
    trsMessages ti mp1 ++ trsMessages ti mp2.
Proof.
  intros; apply filter_app.
Qed.

Lemma trsMessages_In:
  forall tmsg ti mp,
    In tmsg mp ->
    tmsg_info tmsg = Some ti ->
    In tmsg (trsMessages ti mp).
Proof.
  induction mp; simpl; intros; auto.
  destruct H; subst.
  - rewrite H0.
    destruct (tinfo_dec ti ti); [|elim n; reflexivity].
    left; reflexivity.
  - find_if_inside; auto.
    right; auto.
Qed.

Lemma trsMessages_In_tinfo:
  forall tmsg ti mp,
    In tmsg (trsMessages ti mp) ->
    tmsg_info tmsg = Some ti.
Proof.
  induction mp; simpl; intros; [elim H|].
  remember (tmsg_info a) as oti; destruct oti as [ati|]; auto.
  destruct (tinfo_dec ati ti); subst; auto.
  inv H; auto.
Qed.
  
Lemma trsMessages_SubList:
  forall ti mp1 mp2,
    SubList mp1 mp2 ->
    SubList (trsMessages ti mp1) (trsMessages ti mp2).
Proof.
  induction mp1; simpl; intros; [apply SubList_nil|].
  apply SubList_cons_inv in H; dest.
  remember (tmsg_info a) as tinfo; destruct tinfo; auto.
  destruct (tinfo_dec t ti); subst; auto.
  apply SubList_cons; auto.
  apply trsMessages_In; auto.
Qed.

Lemma trsMessages_deqMP_SubList:
  forall ti from to chn mp,
    SubList (trsMessages ti (deqMP from to chn mp))
            (trsMessages ti mp).
Proof.
  intros.
  apply trsMessages_SubList.
  apply deqMP_SubList.
Qed.

Lemma trsMessages_toTMsg:
  forall ti msgs,
    trsMessages ti (toTMsgs ti msgs) = toTMsgs ti msgs.
Proof.
  induction msgs; simpl; intros; [reflexivity|].
  destruct (tinfo_dec ti ti); [|elim n; reflexivity].
  rewrite IHmsgs; reflexivity.
Qed.

Lemma trsMessages_deqMP_comm:
  forall rqin from to chn mp tmsg,
    firstMP from to chn mp = Some tmsg ->
    tmsg_info tmsg = Some rqin ->
    trsMessages rqin (deqMP from to chn mp) =
    deqMP from to chn (trsMessages rqin mp).
Proof.
  induction mp; simpl; intros; [reflexivity|].
  unfold firstMP in H; simpl in H.
  destruct (msgAddr_dec _ _).
  - inv H; rewrite H0.
    destruct (tinfo_dec _ _); [|elim n; reflexivity].
    simpl; destruct (msgAddr_dec _ _); [|elim n; assumption].
    reflexivity.
  - specialize (IHmp _ H H0).
    simpl; destruct (tmsg_info a); [|assumption].
    destruct (tinfo_dec _ _); subst; [|assumption].
    simpl; destruct (msgAddr_dec _ _); [elim n; assumption|].
    rewrite IHmp; reflexivity.
Qed.

Definition AtomicOutsAInv (ti: TInfo)
           (hst: History) (mouts: MessagePool TMsg) (ist: TState) :=
  trsMessages ti (tst_msgs ist) = mouts.

Lemma atomic_outs:
  forall sys, TrsAInv sys ValidTidState AtomicOutsAInv.
Proof.
Admitted.

Corollary atomic_outs_trsMessages_nil:
  forall sys ti hst mouts rsout,
    Atomic sys ti hst mouts (Some rsout) ->
    forall st1,
      ValidTidState st1 ->
      forall st2,
        steps_det sys st1 hst st2 ->
        trsMessages ti (tst_msgs st2) = nil.
Proof.
  intros.
  pose proof (atomic_rs_out_2 H); dest; subst.
  eapply atomic_outs; eauto.
Qed.

Theorem serializable_seqSteps_refines:
  forall sys,
    SerializableSys sys ->
    steps_det # seqSteps |-- sys ⊑[id] sys.
Proof.
  unfold SerializableSys, Refines; intros.
  inv H0; rename ll0 into ill.
  specialize (H _ _ H1).
  unfold Serializable in H.
  destruct H as [sll [sst [? ?]]].
  rewrite H0.
  econstructor; eauto.
  apply map_id.
Qed.

