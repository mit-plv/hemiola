Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax.

Set Implicit Arguments.

Section MessagePool.
  Variable (MsgT: Type).

  Definition Queue := list MsgT.
  Definition MessagePool := M.t (list MsgT).

  Definition emptyMP: MessagePool := M.empty _.

  Definition findQ (midx: IdxT) (mp: MessagePool): Queue :=
    mp@[midx] >>=[nil] (fun q => q).

  Definition firstMP (mp: MessagePool) (midx: IdxT) :=
    hd_error (findQ midx mp).

  Definition FirstMP (mp: MessagePool) (midx: IdxT) (msg: MsgT) :=
    firstMP mp midx = Some msg.

  Definition FirstMPI (mp: MessagePool) (idm: Id MsgT)  :=
    FirstMP mp (idOf idm) (valOf idm).

  (* NOTE: the head is the oldest one. *)
  Definition deqMP (midx: IdxT) (mp: MessagePool): MessagePool :=
    match findQ midx mp with
    | nil => mp
    | _ :: q => mp+[midx <- q]
    end.

  (* NOTE: the head is the oldest one. *)
  Definition enqMP (midx: IdxT) (m: MsgT) (mp: MessagePool): MessagePool :=
    mp+[midx <- (findQ midx mp ++ [m])].

  Definition enqMPI (idm: Id MsgT) (mp: MessagePool): MessagePool :=
    enqMP (idOf idm) (valOf idm) mp.

  Definition EmptyMP (mp: MessagePool) := mp = M.empty _.
  Definition InMP (midx: IdxT) (msg: MsgT) (mp: MessagePool) :=
    In msg (findQ midx mp).

  Definition InMPI (idm: Id MsgT) (mp: MessagePool) :=
    InMP (idOf idm) (valOf idm) mp.

  Definition ForallMP (P: IdxT -> MsgT -> Prop) (mp: MessagePool) :=
    forall midx, Forall (P midx) (findQ midx mp).

  Fixpoint enqMsgs (nmsgs: list (Id MsgT)) (mp: MessagePool): MessagePool :=
    match nmsgs with
    | nil => mp
    | (midx, msg) :: nmsgs' =>
      enqMsgs nmsgs' (enqMP midx msg mp)
    end.

  Fixpoint deqMsgs (minds: list IdxT) (mp: MessagePool): MessagePool :=
    match minds with
    | nil => mp
    | mind :: minds' =>
      deqMsgs minds' (deqMP mind mp)
    end.

  Definition qsOf (minds: list IdxT) (mp: MessagePool): MessagePool :=
    M.restrict mp minds.

End MessagePool.

Section Facts.
  Variable (MsgT: Type).

  Lemma ForallMP_emptyMP:
    forall (P: IdxT -> MsgT -> Prop),
      ForallMP P (emptyMP _).
  Proof.
    intros; constructor.
  Qed.

  Lemma ForallMP_enqMP:
    forall P (mp: MessagePool MsgT),
      ForallMP P mp ->
      forall i m,
        P i m ->
        ForallMP P (enqMP i m mp).
  Proof.
    unfold ForallMP, enqMP, findQ; intros.
    remember (mp@[i]) as iq; destruct iq; simpl.
    - findeq; auto.
      specialize (H i).
      mred_find.
      destruct l; simpl; auto.
      inv H.
      constructor; auto.
      apply Forall_app; auto.
    - findeq; simpl; auto.
  Qed.

  Lemma ForallMP_enqMsgs:
    forall P nmsgs (mp: MessagePool MsgT),
      ForallMP P mp ->
      Forall (fun im => P (idOf im) (valOf im)) nmsgs ->
      ForallMP P (enqMsgs nmsgs mp).
  Proof.
    induction nmsgs; simpl; intros; auto.
    destruct a as [i m]; cbn in *.
    inv H0.
    apply IHnmsgs; auto.
    apply ForallMP_enqMP; auto.
  Qed.

  Lemma ForallMP_deqMP:
    forall P (mp: MessagePool MsgT),
      ForallMP P mp ->
      forall i,
        ForallMP P (deqMP i mp).
  Proof.
    unfold ForallMP, deqMP, findQ; intros.
    remember (mp@[i]) as iq; destruct iq; simpl.
    - destruct l; auto.
      findeq; auto; simpl.
      specialize (H i); mred_find.
      inv H; auto.
    - findeq; simpl; auto.
  Qed.

  Lemma ForallMP_deqMsgs:
    forall P minds (mp: MessagePool MsgT),
      ForallMP P mp ->
      ForallMP P (deqMsgs minds mp).
  Proof.
    induction minds; simpl; intros; auto.
    apply IHminds; auto.
    apply ForallMP_deqMP; auto.
  Qed.

  Lemma ForallMP_impl:
    forall (P1: IdxT -> MsgT -> Prop) mp,
      ForallMP P1 mp ->
      forall (P2: IdxT -> MsgT -> Prop),
        (forall i m, P1 i m -> P2 i m) ->
        ForallMP P2 mp.
  Proof.
    unfold ForallMP; intros.
    specialize (H midx).
    eapply Forall_impl; [|exact H].
    auto.
  Qed.

  Lemma ForallMP_InMP:
    forall (P: IdxT -> MsgT -> Prop) mp,
      ForallMP P mp ->
      forall i m,
        InMP i m mp ->
        P i m.
  Proof.
    unfold ForallMP, InMP; intros.
    specialize (H i).
    eapply Forall_forall in H; eauto.
  Qed.

  Corollary ForallMP_Forall_InMP:
    forall (P: IdxT -> MsgT -> Prop) mp,
      ForallMP P mp ->
      forall ims,
        Forall (fun im => InMP (idOf im) (valOf im) mp) ims ->
        Forall (fun im => P (idOf im) (valOf im)) ims.
  Proof.
    induction ims; simpl; intros; auto.
    inv H0.
    constructor; auto.
    eapply ForallMP_InMP; eauto.
  Qed.

  Lemma FirstMP_InMP:
    forall (mp: MessagePool MsgT) i m,
      FirstMP mp i m ->
      InMP i m mp.
  Proof.
    unfold FirstMP, firstMP, InMP; intros.
    apply hd_error_In; auto.
  Qed.

  Lemma FirstMP_enqMP:
    forall (mp: MessagePool MsgT) i m,
      FirstMP mp i m ->
      forall ni nm,
        FirstMP (enqMP ni nm mp) i m.
  Proof.
    unfold FirstMP, firstMP, enqMP, findQ; intros.
    mred; cbn.
    destruct (mp@[ni]); cbn in *.
    - apply hd_error_Some_app; auto.
    - discriminate.
  Qed.

  Lemma FirstMP_enqMsgs:
    forall msgs (mp: MessagePool MsgT) i m,
      FirstMP mp i m ->
      FirstMP (enqMsgs msgs mp) i m.
  Proof.
    induction msgs; simpl; intros; auto.
    destruct a as [midx msg].
    apply IHmsgs.
    apply FirstMP_enqMP; auto.
  Qed.

  Corollary FirstMPI_Forall_enqMsgs:
    forall emsgs msgs (mp: MessagePool MsgT),
      Forall (FirstMPI mp) msgs ->
      Forall (FirstMPI (enqMsgs emsgs mp)) msgs.
  Proof.
    induction msgs; simpl; intros; auto.
    inv H; constructor; auto.
    apply FirstMP_enqMsgs; auto.
  Qed.

  Lemma FirstMP_deqMP:
    forall midx1 midx2 msg2 (mp: MessagePool MsgT),
      midx1 <> midx2 ->
      FirstMP mp midx2 msg2 <->
      FirstMP (deqMP midx1 mp) midx2 msg2.
  Proof.
    split.
    - unfold FirstMP, firstMP, deqMP; intros.
      remember (findQ midx2 mp) as q2; destruct q2; [discriminate|].
      cbn in *.
      remember (findQ midx1 mp) as q1; destruct q1.
      + rewrite <-Heqq2; auto.
      + unfold findQ in *; mred.
        destruct (mp@[midx2]); simpl in *; subst; auto.
        discriminate.
    - unfold FirstMP, firstMP, deqMP; intros.
      unfold findQ in *; mred.
      remember (mp@[midx1]) as q1; destruct q1; auto.
      simpl in *.
      destruct l; auto.
      remember (mp@[midx2]) as q2; destruct q2; auto; mred.
  Qed.

  Lemma FirstMP_deqMsgs:
    forall minds1 midx2 msg2 (mp: MessagePool MsgT),
      ~ In midx2 minds1 ->
      FirstMP mp midx2 msg2 <->
      FirstMP (deqMsgs minds1 mp) midx2 msg2.
  Proof.
    induction minds1; simpl; intros; [split; auto|].
    split; intros.
    - rewrite <-IHminds1.
      + apply FirstMP_deqMP; auto.
      + intro Hx; elim H; auto.
    - eapply FirstMP_deqMP with (midx1:= a); auto.
      rewrite IHminds1; auto.
  Qed.

  Corollary FirstMPI_Forall_deqMsgs:
    forall minds1 msgs2 (mp: MessagePool MsgT),
      DisjList (idsOf msgs2) minds1 ->
      Forall (FirstMPI mp) msgs2 <->
      Forall (FirstMPI (deqMsgs minds1 mp)) msgs2.
  Proof.
    induction msgs2; simpl; intros; [split; constructor|].
    split; intros.
    - apply DisjList_cons in H; dest.
      inv H0; constructor.
      + apply FirstMP_deqMsgs; auto.
      + rewrite <-IHmsgs2; eauto.
    - apply DisjList_cons in H; dest.
      inv H0; constructor.
      + eapply FirstMP_deqMsgs; eauto.
      + rewrite IHmsgs2; eauto.
  Qed.

  Lemma InMP_enqMP_or:
    forall midx (msg: MsgT) nidx nmsg mp,
      InMP midx msg (enqMP nidx nmsg mp) ->
      (midx = nidx /\ msg = nmsg) \/
      InMP midx msg mp.
  Proof.
    unfold InMP, enqMP, findQ; intros.
    destruct (midx ==n nidx); subst.
    - mred; unfold findQ in H; simpl in H.
      destruct (mp@[nidx]); simpl in *.
      + apply in_app_or in H; destruct H; auto.
        Common.dest_in; auto.
      + destruct H; auto.
    - mred.
  Qed.

  Lemma InMP_enqMsgs_or:
    forall midx (msg: MsgT) nmsgs mp,
      InMP midx msg (enqMsgs nmsgs mp) ->
      In (midx, msg) nmsgs \/
      InMP midx msg mp.
  Proof.
    induction nmsgs; simpl; intros; auto.
    destruct a as [nidx nmsg].
    specialize (IHnmsgs _ H); destruct IHnmsgs; auto.
    apply InMP_enqMP_or in H0; destruct H0; auto.
    dest; subst; auto.
  Qed.

  Lemma InMP_deqMP:
    forall midx (msg: MsgT) ridx mp,
      InMP midx msg (deqMP ridx mp) ->
      InMP midx msg mp.
  Proof.
    unfold InMP, deqMP, findQ; intros.
    remember (mp@[ridx]) as rq; destruct rq; simpl in *; auto.
    destruct l; auto.
    destruct (midx ==n ridx); subst.
    - mred; simpl in *; auto.
    - mred.
  Qed.

  Lemma InMP_deqMsgs:
    forall midx (msg: MsgT) rmsgs mp,
      InMP midx msg (deqMsgs rmsgs mp) ->
      InMP midx msg mp.
  Proof.
    induction rmsgs; simpl; intros; auto.
    specialize (IHrmsgs _ H).
    eapply InMP_deqMP; eauto.
  Qed.

  Lemma qsOf_In_findQ_eq:
    forall (mp1 mp2: MessagePool MsgT) minds,
      qsOf minds mp1 = qsOf minds mp2 ->
      forall midx,
        In midx minds ->
        findQ midx mp1 = findQ midx mp2.
  Proof.
    unfold qsOf, findQ; intros.
    rewrite <-M.restrict_in_find
      with (m:= mp1) (d:= minds) by assumption.
    rewrite <-M.restrict_in_find
      with (m:= mp2) (d:= minds) by assumption.
    rewrite H; reflexivity.
  Qed.

  Corollary qsOf_In_FirstMP:
    forall (mp1 mp2: MessagePool MsgT) minds,
      qsOf minds mp1 = qsOf minds mp2 ->
      forall i m,
        In i minds ->
        FirstMP mp1 i m ->
        FirstMP mp2 i m.
  Proof.
    unfold FirstMP, firstMP; intros.
    erewrite qsOf_In_findQ_eq; eauto.
  Qed.

  Lemma enqMP_enqMP_comm:
    forall midx1 msg1 midx2 msg2 (mp: MessagePool MsgT),
      midx1 <> midx2 ->
      enqMP midx1 msg1 (enqMP midx2 msg2 mp) = enqMP midx2 msg2 (enqMP midx1 msg1 mp).
  Proof.
    unfold enqMP, findQ; intros.
    mred.
    destruct (mp@[midx1]); destruct (mp@[midx2]); meq.
  Qed.
      
  Lemma enqMP_enqMsgs_comm:
    forall midx msg msgs (mp: MessagePool MsgT),
      ~ In midx (idsOf msgs) ->
      enqMP midx msg (enqMsgs msgs mp) = enqMsgs msgs (enqMP midx msg mp).
  Proof.
    induction msgs; simpl; intros; auto.
    destruct a as [midx2 msg2]; cbn in *.
    rewrite IHmsgs by auto.
    f_equal.
    apply enqMP_enqMP_comm; auto.
  Qed.

  Lemma enqMsgs_enqMsgs_comm:
    forall (msgs1 msgs2: list (Id MsgT)) (mp: MessagePool MsgT),
      DisjList (idsOf msgs1) (idsOf msgs2) ->
      enqMsgs msgs1 (enqMsgs msgs2 mp) = enqMsgs msgs2 (enqMsgs msgs1 mp).
  Proof.
    induction msgs1; simpl; intros; auto.
    destruct a as [midx msg]; cbn in *.
    apply DisjList_cons in H; dest.
    rewrite <-IHmsgs1 by assumption.
    f_equal.
    apply enqMP_enqMsgs_comm; auto.
  Qed.

  Lemma enqMP_deqMP_comm:
    forall midx1 msg1 (msg2: Id MsgT) (mp: MessagePool MsgT),
      midx1 <> idOf msg2 ->
      enqMP midx1 msg1 (deqMP (idOf msg2) mp) =
      deqMP (idOf msg2) (enqMP midx1 msg1 mp).
  Proof.
    unfold enqMP, deqMP, findQ; intros.
    destruct msg2 as [midx2 msg2]; simpl.
    remember (mp@[midx2]) as q2; destruct q2; simpl in *.
    - destruct l; simpl.
      + mred.
      + mred; simpl; meq.
    - mred.
  Qed.

  Lemma deqMP_deqMP_comm:
    forall midx1 midx2 (mp: MessagePool MsgT),
      midx1 <> midx2 ->
      deqMP midx1 (deqMP midx2 mp) = deqMP midx2 (deqMP midx1 mp).
  Proof.
    unfold deqMP, findQ; intros.
    remember (mp@[midx1]) as q1; destruct q1.
    - destruct l; simpl.
      + destruct (mp@[midx2]); simpl; mred.
        destruct l; simpl; mred.
      + remember (mp@[midx2]) as q2; destruct q2; simpl; mred.
        destruct l0; simpl; mred.
        simpl; meq.
    - remember (mp@[midx2]) as q2; destruct q2; simpl; mred.
      destruct l; simpl; mred.
  Qed.
      
  Lemma deqMP_deqMsgs_comm:
    forall midx minds (mp: MessagePool MsgT),
      ~ In midx minds ->
      deqMP midx (deqMsgs minds mp) = deqMsgs minds (deqMP midx mp).
  Proof.
    induction minds; simpl; intros; auto.
    rewrite IHminds by auto.
    f_equal.
    apply deqMP_deqMP_comm; auto.
  Qed.

  Lemma deqMsgs_deqMsgs_comm:
    forall (minds1 minds2: list IdxT) (mp: MessagePool MsgT),
      DisjList minds1 minds2 ->
      deqMsgs minds1 (deqMsgs minds2 mp) = deqMsgs minds2 (deqMsgs minds1 mp).
  Proof.
    induction minds1; simpl; intros; auto.
    apply DisjList_cons in H; dest.
    rewrite <-IHminds1 by assumption.
    f_equal.
    apply deqMP_deqMsgs_comm; auto.
  Qed.
  
  Lemma enqMP_deqMP_FirstMPI_comm:
    forall midx1 msg1 msg2 (mp: MessagePool MsgT),
      FirstMPI mp msg2 ->
      enqMP midx1 msg1 (deqMP (idOf msg2) mp) =
      deqMP (idOf msg2) (enqMP midx1 msg1 mp).
  Proof.
    unfold enqMP, deqMP, findQ; intros.
    destruct msg2 as [midx2 msg2]; simpl.
    apply FirstMP_InMP in H; simpl in H.
    red in H; unfold findQ in H.
    remember (mp@[midx1]) as q1; destruct q1;
      remember (mp@[midx2]) as q2; destruct q2; simpl in *; try (elim H).
    - destruct l0.
      + mred; elim H.
      + mred; simpl; meq.
    - destruct l.
      + mred.
      + mred; simpl; meq.
  Qed.

  Lemma enqMsgs_deqMP_FirstMPI_comm:
    forall msgs msg (mp: MessagePool MsgT),
      FirstMPI mp msg ->
      enqMsgs msgs (deqMP (idOf msg) mp) = deqMP (idOf msg) (enqMsgs msgs mp).
  Proof.
    induction msgs; simpl; intros; auto.
    destruct a as [midx2 msg2]; cbn in *.
    rewrite <-IHmsgs.
    - rewrite enqMP_deqMP_FirstMPI_comm by assumption.
      reflexivity.
    - apply FirstMP_enqMP; auto.
  Qed.

  Lemma enqMsgs_deqMP_comm:
    forall msgs (msg: Id MsgT) (mp: MessagePool MsgT),
      ~ In (idOf msg) (idsOf msgs) ->
      enqMsgs msgs (deqMP (idOf msg) mp) = deqMP (idOf msg) (enqMsgs msgs mp).
  Proof.
    induction msgs; simpl; intros; auto.
    destruct a as [midx2 msg2]; cbn in *.
    rewrite <-IHmsgs.
    - rewrite enqMP_deqMP_comm.
      + reflexivity.
      + intro Hx; elim H; auto.
    - intro Hx; elim H; auto.
  Qed.

  Lemma enqMsgs_deqMsgs_FirstMPI_comm:
    forall (msgs1 msgs2: list (Id MsgT)) (mp: MessagePool MsgT),
      NoDup (idsOf msgs1) ->
      Forall (FirstMPI mp) msgs1 ->
      enqMsgs msgs2 (deqMsgs (idsOf msgs1) mp) =
      deqMsgs (idsOf msgs1) (enqMsgs msgs2 mp).
  Proof.
    induction msgs1; simpl; intros; auto.
    inv H; inv H0.
    rewrite IHmsgs1.
    - rewrite enqMsgs_deqMP_FirstMPI_comm by assumption.
      reflexivity.
    - assumption.
    - clear -H2 H3 H5.
      induction msgs1; simpl; intros; auto.
      inv H5; constructor.
      + apply FirstMP_deqMP; auto.
        intro Hx; elim H3.
        left; auto.
      + apply IHmsgs1; auto.
        intro Hx; elim H3; right; auto.
  Qed.

  Lemma enqMsgs_deqMsgs_comm:
    forall (msgs1 msgs2: list (Id MsgT)) (mp: MessagePool MsgT),
      DisjList (idsOf msgs1) (idsOf msgs2) ->
      enqMsgs msgs2 (deqMsgs (idsOf msgs1) mp) =
      deqMsgs (idsOf msgs1) (enqMsgs msgs2 mp).
  Proof.
    induction msgs1; simpl; intros; auto.
    apply DisjList_cons in H; dest.
    rewrite IHmsgs1 by assumption.
    rewrite enqMsgs_deqMP_comm by assumption.
    reflexivity.
  Qed.

End Facts.

Global Opaque ForallMP.


Section Map.
  Variables (MsgT1 MsgT2: Type).
  Context `{HasMsg MsgT1} `{HasMsg MsgT2}.

  Variable (mmap: MsgT1 -> MsgT2).
  Hypothesis (Hmmap: forall msg, getMsg (mmap msg) = getMsg msg).

  Definition mpmap (mp: MessagePool MsgT1): MessagePool MsgT2 :=
    M.map (map mmap) mp.

End Map.

