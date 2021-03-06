Require Import Bool List String PeanoNat Lia.
Require Import Common ListSupport FMap Syntax.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

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

  Definition FirstMPI (mp: MessagePool) (idm: Id MsgT) :=
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

  Definition InMPI (mp: MessagePool) (idm: Id MsgT) :=
    InMP (idOf idm) (valOf idm) mp.

  Definition ForallQ (P: IdxT -> Queue -> Prop) (mp: MessagePool) :=
    forall midx, P midx (findQ midx mp).

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

  Definition ValidDeq (mp: MessagePool) (midx: IdxT) :=
    findQ midx mp <> nil.

  Fixpoint ValidDeqs (mp: MessagePool) (minds: list IdxT) :=
    match minds with
    | nil => True
    | midx :: minds' =>
      ValidDeq mp midx /\ ValidDeqs (deqMP midx mp) minds'
    end.

  Definition qsOf (minds: list IdxT) (mp: MessagePool): MessagePool :=
    M.restrict mp minds.

  (* [q1] is older. *)
  Definition unionQ (q1 q2: Queue): Queue :=
    q1 ++ q2.

  (* [mp1] is older. *)
  Definition unionMP (mp1 mp2: MessagePool): MessagePool :=
    M.merge (fun q1 q2 => unionQ q1 q2) mp1 mp2.

  Section OnDec.
    Variable (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).

    Definition countMsg (idm: Id MsgT) (mp: MessagePool) :=
      List.count_occ msgT_dec (findQ (idOf idm) mp) (valOf idm).

  End OnDec.

End MessagePool.

Section Facts.
  Variable (MsgT: Type).

  Lemma findQ_ext:
    forall (mp1 mp2: MessagePool MsgT),
      (forall midx, mp1@[midx] = None <-> mp2@[midx] = None) ->
      (forall midx, findQ midx mp1 = findQ midx mp2) ->
      mp1 = mp2.
  Proof.
    unfold findQ; intros.
    M.ext midx.
    specialize (H midx).
    specialize (H0 midx).
    destruct (mp1@[midx]) as [q1|], (mp2@[midx]) as [q2|];
      simpl in *; subst; auto; intuition auto.
  Qed.

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
      mred.
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
      specialize (H i); mred.
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

  Lemma FirstMP_eq:
    forall (mp: MessagePool MsgT) i m1 m2,
      FirstMP mp i m1 -> FirstMP mp i m2 ->
      m1 = m2.
  Proof.
    unfold FirstMP, firstMP; intros.
    congruence.
  Qed.

  Lemma FirstMP_InMP:
    forall (mp: MessagePool MsgT) i m,
      FirstMP mp i m ->
      InMP i m mp.
  Proof.
    unfold FirstMP, firstMP, InMP; intros.
    apply hd_error_In; auto.
  Qed.

  Lemma FirstMPI_Forall_InMP:
    forall (mp: MessagePool MsgT) msgs,
      Forall (FirstMPI mp) msgs ->
      Forall (InMPI mp) msgs.
  Proof.
    induction msgs; simpl; intros; [constructor|].
    inv H.
    constructor; auto.
    apply FirstMP_InMP; auto.
  Qed.

  Lemma InMP_FirstMP:
    forall (mp: MessagePool MsgT) i m,
      InMP i m mp -> List.length (findQ i mp) <= 1 ->
      FirstMP mp i m.
  Proof.
    unfold InMP, FirstMP, firstMP; intros.
    destruct (findQ i mp); [elim H|].
    destruct q.
    - dest_in; reflexivity.
    - simpl in H0; inv H0; inv H2.
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

  Lemma FirstMP_enqMP_inv:
    forall (mp: MessagePool MsgT) i m ni nm,
      (i, m) <> (ni, nm) ->
      FirstMP (enqMP ni nm mp) i m ->
      FirstMP mp i m.
  Proof.
    unfold FirstMP, firstMP, enqMP, findQ; intros.
    destruct (idx_dec i ni); subst; [|mred].
    mred; simpl in H0.
    destruct (mp@[ni]).
    - simpl in *; destruct l; simpl in *; auto.
      inv H0; elim H; reflexivity.
    - simpl in *; inv H0; elim H; reflexivity.
  Qed.

  Lemma FirstMP_enqMsgs_inv:
    forall msgs (mp: MessagePool MsgT) i m,
      ~ In (i, m) msgs ->
      FirstMP (enqMsgs msgs mp) i m ->
      FirstMP mp i m.
  Proof.
    induction msgs; simpl; intros; auto.
    destruct a as [midx msg]; simpl in *.
    assert (~ In (i, m) msgs) by (intro Hx; elim H; auto).
    specialize (IHmsgs _ _ _ H1 H0).
    eapply FirstMP_enqMP_inv; [|eassumption].
    auto.
  Qed.

  Corollary FirstMPI_Forall_enqMsgs_inv:
    forall emsgs msgs (mp: MessagePool MsgT),
      DisjList msgs emsgs ->
      Forall (FirstMPI (enqMsgs emsgs mp)) msgs ->
      Forall (FirstMPI mp) msgs.
  Proof.
    induction msgs; simpl; intros; auto.
    apply DisjList_cons in H; dest.
    inv H0; constructor; auto.
    destruct a as [midx msg].
    eapply FirstMP_enqMsgs_inv; eauto.
  Qed.

  Lemma findQ_not_In_enqMP:
    forall (mp: MessagePool MsgT) msg midx1 midx2,
      midx1 <> midx2 ->
      findQ midx1 (enqMP midx2 msg mp) = findQ midx1 mp.
  Proof.
    unfold enqMP, findQ; intros; mred.
  Qed.

  Lemma findQ_not_In_enqMsgs:
    forall msgs (mp: MessagePool MsgT) midx,
      ~ In midx (idsOf msgs) ->
      findQ midx (enqMsgs msgs mp) = findQ midx mp.
  Proof.
    induction msgs; simpl; intros; auto.
    destruct a as [amidx amsg]; simpl in *.
    rewrite IHmsgs.
    - apply findQ_not_In_enqMP.
      intro Hx; elim H; auto.
    - intro Hx; elim H; auto.
  Qed.

  Lemma findQ_In_enqMP:
    forall (mp: MessagePool MsgT) midx msg,
        findQ midx (enqMP midx msg mp) =
        findQ midx mp ++ [msg].
  Proof.
    unfold enqMP, findQ; intros; mred.
  Qed.

  Lemma findQ_In_NoDup_enqMsgs:
    forall msgs (mp: MessagePool MsgT),
      NoDup (idsOf msgs) ->
      forall midx msg,
        In (midx, msg) msgs ->
        findQ midx (enqMsgs msgs mp) =
        findQ midx mp ++ [msg].
  Proof.
    induction msgs; simpl; intros; [exfalso; auto|].
    destruct H0; subst.
    - simpl in H; inv H.
      rewrite findQ_not_In_enqMsgs by assumption.
      apply findQ_In_enqMP.
    - destruct a as [amidx amsg]; simpl in *; inv H.
      erewrite IHmsgs by eassumption.
      rewrite findQ_not_In_enqMP; [reflexivity|].
      intro Hx; subst; elim H3.
      apply in_map with (f:= idOf) in H0; assumption.
  Qed.

  Lemma findQ_not_In_deqMP:
    forall (mp: MessagePool MsgT) midx1 midx2,
      midx1 <> midx2 ->
      findQ midx1 (deqMP midx2 mp) = findQ midx1 mp.
  Proof.
    unfold deqMP, findQ; intros.
    remember (mp@[midx2]) as q2; destruct q2; simpl; auto.
    destruct l; simpl; auto.
    mred.
  Qed.

  Lemma findQ_not_In_deqMsgs:
    forall minds (mp: MessagePool MsgT) midx,
      ~ In midx minds ->
      findQ midx (deqMsgs minds mp) = findQ midx mp.
  Proof.
    induction minds; simpl; intros; auto.
    rewrite IHminds.
    - apply findQ_not_In_deqMP.
      intro Hx; elim H; auto.
    - intro Hx; elim H; auto.
  Qed.

  Lemma findQ_In_deqMP:
    forall midx (mp: MessagePool MsgT),
      findQ midx mp <> nil ->
      exists msg,
        msg :: (findQ midx (deqMP midx mp)) =
        findQ midx mp.
  Proof.
    unfold deqMP, findQ; simpl; intros.
    remember (mp@[midx]) as q; destruct q; simpl in *.
    - destruct l; simpl; [exfalso; auto|].
      mred; simpl.
      eexists; reflexivity.
    - mred.
  Qed.

  Lemma findQ_In_deqMP_FirstMP:
    forall midx msg (mp: MessagePool MsgT),
      FirstMP mp midx msg ->
      msg :: (findQ midx (deqMP midx mp)) =
      findQ midx mp.
  Proof.
    unfold FirstMP, firstMP, deqMP, findQ; simpl; intros.
    remember (mp@[midx]) as q; destruct q; simpl in *.
    - destruct l; [discriminate|].
      inv H; mred.
    - mred.
  Qed.

  Lemma findQ_In_NoDup_deqMsgs:
    forall minds midx (mp: MessagePool MsgT),
      NoDup minds ->
      In midx minds ->
      findQ midx mp <> nil ->
      exists msg,
        msg :: (findQ midx (deqMsgs minds mp)) =
        findQ midx mp.
  Proof.
    induction minds; simpl; intros; [exfalso; auto|].
    destruct H0; subst.
    - inv H.
      rewrite findQ_not_In_deqMsgs by assumption.
      apply findQ_In_deqMP; assumption.
    - inv H.
      rewrite <-findQ_not_In_deqMP with (midx2:= a) in H1
        by (intro Hx; subst; elim H4; assumption).
      specialize (IHminds _ _ H5 H0 H1).
      destruct IHminds as [dmsg ?].
      exists dmsg; rewrite H.
      apply findQ_not_In_deqMP.
      intro Hx; subst; elim H4; assumption.
  Qed.

  Lemma findQ_deqMsgs_eq:
    forall minds midx (msgs1 msgs2: MessagePool MsgT),
      findQ midx msgs1 = findQ midx msgs2 ->
      findQ midx (deqMsgs minds msgs1) =
      findQ midx (deqMsgs minds msgs2).
  Proof.
    induction minds; simpl; intros; auto.
    apply IHminds.
    destruct (idx_dec midx a); subst.
    - unfold deqMP; rewrite H.
      destruct (findQ a msgs2) eqn:Hf; [congruence|].
      unfold findQ; mred.
    - do 2 (rewrite findQ_not_In_deqMP by assumption).
      assumption.
  Qed.

  Lemma findQ_eq_FirstMPI:
    forall midx (msg: MsgT) msgs1,
      FirstMPI msgs1 (midx, msg) ->
      forall msgs2,
        findQ midx msgs1 = findQ midx msgs2 ->
        FirstMPI msgs2 (midx, msg).
  Proof.
    unfold FirstMPI, FirstMP, firstMP; simpl; intros.
    congruence.
  Qed.

  Lemma FirstMP_findQ_False:
    forall midx msg (mp: MessagePool MsgT),
      findQ midx mp = nil ->
      FirstMP mp midx msg ->
      False.
  Proof.
    unfold FirstMP, firstMP; intros.
    rewrite H in H0; discriminate.
  Qed.

  Lemma findQ_length_zero:
    forall (msgs: MessagePool MsgT) midx msg,
      List.length (findQ midx msgs) <= 1 ->
      FirstMP msgs midx msg ->
      findQ midx (deqMP midx msgs) = nil.
  Proof.
    intros.
    apply findQ_In_deqMP_FirstMP in H0.
    unfold FirstMP, firstMP in *; simpl in *.
    destruct (findQ midx msgs); [discriminate|].
    inv H0.
    simpl in H.
    destruct (findQ _ _); [reflexivity|simpl in H; lia].
  Qed.

  Lemma findQ_length_ge_one:
    forall (msgs: MessagePool MsgT) midx msg,
      InMP midx msg msgs ->
      List.length (findQ midx msgs) >= 1.
  Proof.
    unfold InMP; intros.
    destruct (findQ midx msgs); simpl in *.
    - exfalso; auto.
    - lia.
  Qed.

  Lemma findQ_length_one:
    forall (msgs: MessagePool MsgT) midx msg,
      List.length (findQ midx msgs) <= 1 ->
      FirstMP msgs midx msg ->
      List.length (findQ midx msgs) = 1.
  Proof.
    intros.
    remember (findQ midx msgs) as q; destruct q.
    - exfalso; eapply FirstMP_findQ_False; eauto.
    - simpl in *; lia.
  Qed.

  Lemma findQ_length_two:
    forall (msgs: MessagePool MsgT) midx msg1 msg2,
      msg1 <> msg2 ->
      InMP midx msg1 msgs ->
      InMP midx msg2 msgs ->
      List.length (findQ midx msgs) >= 2.
  Proof.
    unfold InMP; intros.
    induction (findQ midx msgs); simpl; intros; [intuition|].
    inv H0.
    - inv H1; [exfalso; auto|].
      clear -H0.
      induction q; [intuition|].
      inv H0; simpl; lia.
    - inv H1.
      + clear -H2.
        induction q; [intuition|].
        inv H2; simpl; lia.
      + specialize (IHq H2 H0); lia.
  Qed.

  Lemma FirstMP_enqMsgs_order:
    forall midx msg1 outs1 minds2 msg2 (mp: MessagePool MsgT),
      NoDup (idsOf outs1) ->
      NoDup minds2 ->
      outs1 <> nil ->
      In midx (idsOf outs1) ->
      In midx minds2 ->
      FirstMP (enqMsgs outs1 mp) midx msg1 ->
      FirstMP (deqMsgs minds2 (enqMsgs outs1 mp)) midx msg2 ->
      FirstMP mp midx msg1.
  Proof.
    unfold FirstMP, firstMP; intros.
    unfold idsOf in H2; rewrite in_map_iff in H2.
    destruct H2 as [[amidx msg] [? ?]]; simpl in *; subst.
    erewrite findQ_In_NoDup_enqMsgs in H4 by eassumption.
    assert (findQ midx (enqMsgs outs1 mp) <> nil).
    { erewrite findQ_In_NoDup_enqMsgs by eassumption.
      destruct (findQ midx mp); discriminate.
    }
    pose proof (findQ_In_NoDup_deqMsgs _ (enqMsgs outs1 mp) H0 H3 H2).
    destruct H7 as [dmsg ?].
    erewrite findQ_In_NoDup_enqMsgs in H7 by eassumption.
    rewrite <-H7 in H4; simpl in H4; inv H4.
    destruct (findQ midx mp).
    - inv H7; rewrite H9 in H5; discriminate.
    - inv H7; reflexivity.
  Qed.

  Lemma FirstMPI_Forall_enqMsgs_order:
    forall outs1 ins2 ins3 (mp: MessagePool MsgT),
      NoDup (idsOf outs1) ->
      NoDup (idsOf ins2) ->
      (forall midx : IdxT,
          In midx (idsOf outs1) ->
          In midx (idsOf ins2) -> In midx (idsOf ins3)) ->
      Forall (FirstMPI (enqMsgs outs1 mp)) ins2 ->
      Forall (FirstMPI (deqMsgs (idsOf ins2) (enqMsgs outs1 mp))) ins3 ->
      Forall (FirstMPI mp) ins2.
  Proof.
    intros.
    apply Forall_forall; intros [midx msg] ?.
    specialize (H1 midx).
    rewrite Forall_forall in H2.
    specialize (H2 _ H4); red in H2; simpl in H2.
    destruct (in_dec idx_dec midx (idsOf outs1)).
    - red; simpl.
      assert (In midx (idsOf ins2))
        by (eapply in_map with (f:= idOf) in H4; assumption).
      specialize (H1 i H5); clear H4.
      unfold idsOf in H1; rewrite in_map_iff in H1.
      destruct H1 as [[midx3 msg3] [? ?]]; simpl in *; subst.
      rewrite Forall_forall in H3; specialize (H3 _ H4).
      red in H3; cbn in H3.
      destruct outs1; [assumption|].
      eapply FirstMP_enqMsgs_order;
        [exact H| | | | | |]; eauto.
      discriminate.
    - eapply FirstMP_enqMsgs_inv; eauto.
      intro Hx; elim n.
      eapply in_map with (f:= idOf) in Hx; eauto.
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

  Lemma FirstMPI_Forall_deqMP:
    forall midx1 msgs2 (mp: MessagePool MsgT),
      ~ In midx1 (idsOf msgs2) ->
      Forall (FirstMPI mp) msgs2 <->
      Forall (FirstMPI (deqMP midx1 mp)) msgs2.
  Proof.
    induction msgs2; simpl; intros;
      [split; intros; constructor|].
    split; intros.
    - inv H0.
      constructor.
      + apply FirstMP_deqMP; auto.
      + rewrite <-IHmsgs2; auto.
    - inv H0.
      constructor.
      + red; erewrite FirstMP_deqMP; [eassumption|auto].
      + rewrite IHmsgs2; auto.
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

  Lemma InMP_findQ_False:
    forall midx msg (mp: MessagePool MsgT),
      findQ midx mp = nil ->
      InMP midx msg mp ->
      False.
  Proof.
    unfold InMP, firstMP; intros.
    rewrite H in H0; elim H0.
  Qed.

  Lemma InMP_enqMP_or:
    forall midx (msg: MsgT) nidx nmsg mp,
      InMP midx msg (enqMP nidx nmsg mp) ->
      (midx = nidx /\ msg = nmsg) \/
      InMP midx msg mp.
  Proof.
    unfold InMP, enqMP, findQ; intros.
    destruct (idx_dec midx nidx); subst.
    - mred; unfold findQ in H; simpl in H.
      destruct (mp@[nidx]); simpl in *.
      + apply in_app_or in H; destruct H; auto.

        dest_in; auto.
      + destruct H; auto.
    - mred.
  Qed.

  Lemma InMP_or_enqMP:
    forall midx (msg: MsgT) nidx nmsg mp,
      ((midx = nidx /\ msg = nmsg) \/ InMP midx msg mp) ->
      InMP midx msg (enqMP nidx nmsg mp).
  Proof.
    unfold InMP, enqMP, findQ; intros.
    destruct H; dest; subst.
    - mred; simpl.
      apply in_or_app; right.
      simpl; tauto.
    - mred; simpl.
      apply in_or_app; left; auto.
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

  Lemma InMP_or_enqMsgs:
    forall midx (msg: MsgT) nmsgs mp,
      (In (midx, msg) nmsgs \/ InMP midx msg mp) ->
      InMP midx msg (enqMsgs nmsgs mp).
  Proof.
    induction nmsgs; simpl; intros.
    - destruct H; [elim H|auto].
    - destruct H.
      + destruct H; subst; auto.
        * eapply IHnmsgs.
          right; apply InMP_or_enqMP; auto.
        * destruct a; eapply IHnmsgs; auto.
      + destruct a.
        eapply IHnmsgs.
        right; apply InMP_or_enqMP; auto.
  Qed.

  Lemma InMP_deqMP:
    forall midx (msg: MsgT) ridx mp,
      InMP midx msg (deqMP ridx mp) ->
      InMP midx msg mp.
  Proof.
    unfold InMP, deqMP, findQ; intros.
    remember (mp@[ridx]) as rq; destruct rq; simpl in *; auto.
    destruct l; auto.
    destruct (idx_dec midx ridx); subst.
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

  Lemma deqMP_InMP:
    forall midx (msg: MsgT) rmidx rmsg mp,
      InMP midx msg mp ->
      (midx, msg) <> (rmidx, rmsg) ->
      FirstMP mp rmidx rmsg ->
      InMP midx msg (deqMP rmidx mp).
  Proof.
    unfold FirstMP, firstMP, InMP, deqMP, findQ; intros.
    destruct (mp@[rmidx]) eqn:Hrq; simpl in *; auto.
    destruct l; [discriminate|].
    simpl in H1; inv H1.
    mred; simpl.
    destruct H; subst.
    - exfalso; auto.
    - assumption.
  Qed.

  Lemma deqMsgs_InMP:
    forall midx (msg: MsgT) rmsgs mp,
      InMP midx msg mp ->
      ~ In (midx, msg) rmsgs ->
      Forall (FirstMPI mp) rmsgs ->
      NoDup (idsOf rmsgs) ->
      InMP midx msg (deqMsgs (idsOf rmsgs) mp).
  Proof.
    induction rmsgs as [|[rmidx rmsg] rmsgs]; simpl; intros; auto.
    inv H1; inv H2.
    eapply IHrmsgs; eauto.
    - eapply deqMP_InMP; eauto.
    - apply FirstMPI_Forall_deqMP; auto.
  Qed.

  Lemma deqMP_InMP_midx:
    forall midx (msg: MsgT) rmidx mp,
      InMP midx msg mp ->
      midx <> rmidx ->
      InMP midx msg (deqMP rmidx mp).
  Proof.
    unfold FirstMP, firstMP, InMP, deqMP, findQ; intros.
    destruct (mp@[rmidx]) eqn:Hrq; simpl in *; auto.
    destruct l; [assumption|].
    mred.
  Qed.

  Lemma deqMsgs_InMP_midx:
    forall midx (msg: MsgT) rminds mp,
      InMP midx msg mp ->
      ~ In midx rminds ->
      InMP midx msg (deqMsgs rminds mp).
  Proof.
    induction rminds as [|rmidx rminds]; simpl; intros; auto.
    eapply IHrminds; eauto.
    eapply deqMP_InMP_midx; auto.
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
    forall midx1 msg1 midx2 (mp: MessagePool MsgT),
      midx1 <> midx2 ->
      enqMP midx1 msg1 (deqMP midx2 mp) =
      deqMP midx2 (enqMP midx1 msg1 mp).
  Proof.
    unfold enqMP, deqMP, findQ; intros.
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
    forall msgs (midx: IdxT) (mp: MessagePool MsgT),
      ~ In midx (idsOf msgs) ->
      enqMsgs msgs (deqMP midx mp) = deqMP midx (enqMsgs msgs mp).
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
    forall minds1 (msgs2: list (Id MsgT)) (mp: MessagePool MsgT),
      DisjList minds1 (idsOf msgs2) ->
      enqMsgs msgs2 (deqMsgs minds1 mp) =
      deqMsgs minds1 (enqMsgs msgs2 mp).
  Proof.
    induction minds1; simpl; intros; auto.
    apply DisjList_cons in H; dest.
    rewrite IHminds1 by assumption.
    rewrite enqMsgs_deqMP_comm by assumption.
    reflexivity.
  Qed.

  Lemma enqMP_None:
    forall (mp: MessagePool MsgT) emidx msg midx,
      (enqMP emidx msg mp)@[midx] = None <->
      (mp@[midx] = None /\ emidx <> midx).
  Proof.
    unfold enqMP, findQ; intros; split; intros.
    - remember (mp@[emidx]) as eq; destruct eq; simpl in *;
        destruct (idx_dec emidx midx); subst; mred.
    - remember (mp@[emidx]) as eq; destruct eq; simpl in *; dest;
        destruct (idx_dec emidx midx); subst; mred.
  Qed.

  Lemma enqMsgs_None:
    forall (mp: MessagePool MsgT) msgs midx,
      (enqMsgs msgs mp)@[midx] = None <->
      (mp@[midx] = None /\ ~ In midx (idsOf msgs)).
  Proof.
    split; intros.
    - generalize dependent mp.
      induction msgs; simpl; intros; auto.
      destruct a as [amidx amsg]; simpl in *.
      specialize (IHmsgs _ H); dest.
      apply enqMP_None in H0; dest.
      split; intuition idtac.
    - generalize dependent mp.
      induction msgs; simpl; intros; dest; auto.
      destruct a as [amidx amsg]; simpl in *.
      apply IHmsgs; split; auto.
      apply enqMP_None; auto.
  Qed.

  Lemma deqMP_None:
    forall (mp: MessagePool MsgT) dmidx midx,
      (deqMP dmidx mp)@[midx] = None <->
      mp@[midx] = None.
  Proof.
    unfold deqMP, findQ; split; intros.
    - remember (mp@[dmidx]) as dq; destruct dq; simpl in *; auto.
      destruct l; simpl in *; auto.
      destruct (idx_dec dmidx midx); subst; mred.
    - remember (mp@[dmidx]) as dq; destruct dq; simpl in *; auto.
      destruct l; simpl in *; auto.
      destruct (idx_dec dmidx midx); subst; mred.
  Qed.

  Lemma deqMsgs_None:
    forall (mp: MessagePool MsgT) minds midx,
      (deqMsgs minds mp)@[midx] = None <->
      mp@[midx] = None.
  Proof.
    split; intros.
    - generalize dependent mp.
      induction minds; simpl; intros; auto.
      specialize (IHminds _ H).
      eapply deqMP_None; eauto.
    - generalize dependent mp.
      induction minds; simpl; intros; auto.
      eapply IHminds; eauto.
      eapply deqMP_None; eauto.
  Qed.

  Lemma enqMsgs_In_InMPI:
    forall ins idm (mp: MessagePool MsgT),
      In idm ins ->
      InMPI (enqMsgs ins mp) idm.
  Proof.
    induction ins; simpl; intros; [elim H|].
    destruct H; subst; auto.
    - destruct idm.
      apply InMP_or_enqMsgs; simpl.
      right; apply InMP_or_enqMP; auto.
    - destruct a; eauto.
  Qed.

  Lemma enqMsgs_app:
    forall ins1 ins2 (mp: MessagePool MsgT),
      enqMsgs (ins1 ++ ins2) mp =
      enqMsgs ins2 (enqMsgs ins1 mp).
  Proof.
    induction ins1; simpl; intros; auto.
    destruct a as [midx msg].
    apply IHins1.
  Qed.

  Lemma deqMsgs_app:
    forall minds1 minds2 (mp: MessagePool MsgT),
      deqMsgs (minds1 ++ minds2) mp =
      deqMsgs minds2 (deqMsgs minds1 mp).
  Proof.
    induction minds1; simpl; intros; auto.
  Qed.

  Lemma ValidDeq_enqMP:
    forall midx (mp: MessagePool MsgT),
      ValidDeq mp midx ->
      forall nmidx nmsg,
        ValidDeq (enqMP nmidx nmsg mp) midx.
  Proof.
    unfold ValidDeq, enqMP, findQ; intros.
    mred; simpl.
    match goal with
    | [H: ?l <> nil |- _] => destruct l; auto
    end.
    discriminate.
  Qed.

  Lemma enqMP_deqMP_ValidDeq_comm:
    forall midx (mp: MessagePool MsgT),
      ValidDeq mp midx ->
      forall nmidx nmsg,
        enqMP nmidx nmsg (deqMP midx mp) =
        deqMP midx (enqMP nmidx nmsg mp).
  Proof.
    unfold ValidDeq, enqMP, deqMP, findQ; intros.
    remember (mp@[midx]) as q; destruct q;
      simpl in *; [|elim H; reflexivity].
    destruct l; [elim H; reflexivity|].
    mred; simpl; meq.
  Qed.

  Lemma ValidDeqs_enqMP:
    forall minds (mp: MessagePool MsgT),
      ValidDeqs mp minds ->
      forall midx msg,
        ValidDeqs (enqMP midx msg mp) minds.
  Proof.
    induction minds; simpl; intros; auto.
    dest; split.
    - apply ValidDeq_enqMP; auto.
    - rewrite <-enqMP_deqMP_ValidDeq_comm by assumption.
      eapply IHminds; eauto.
  Qed.

  Lemma ValidDeqs_enqMsgs:
    forall nmsgs minds (mp: MessagePool MsgT),
      ValidDeqs mp minds ->
      ValidDeqs (enqMsgs nmsgs mp) minds.
  Proof.
    induction nmsgs; simpl; intros; auto.
    destruct a as [midx msg].
    apply IHnmsgs.
    apply ValidDeqs_enqMP; auto.
  Qed.

  Lemma enqMsgs_deqMP_ValidDeq_comm:
    forall nmsgs midx (mp: MessagePool MsgT),
      ValidDeq mp midx ->
      enqMsgs nmsgs (deqMP midx mp) =
      deqMP midx (enqMsgs nmsgs mp).
  Proof.
    induction nmsgs; simpl; intros; auto.
    destruct a as [amidx amsg].
    rewrite enqMP_deqMP_ValidDeq_comm by assumption.
    eapply IHnmsgs.
    apply ValidDeq_enqMP; auto.
  Qed.

  Lemma enqMsgs_deqMsgs_ValidDeqs_comm:
    forall minds nmsgs (mp: MessagePool MsgT),
      ValidDeqs mp minds ->
      enqMsgs nmsgs (deqMsgs minds mp) =
      deqMsgs minds (enqMsgs nmsgs mp).
  Proof.
    induction minds; simpl; intros; auto.
    dest.
    rewrite <-enqMsgs_deqMP_ValidDeq_comm by assumption.
    apply IHminds; auto.
  Qed.

  Lemma ValidDeqs_app:
    forall ins1 ins2 (mp: MessagePool MsgT),
      ValidDeqs mp ins1 ->
      ValidDeqs (deqMsgs ins1 mp) ins2 ->
      ValidDeqs mp (ins1 ++ ins2).
  Proof.
    induction ins1; simpl; intros; auto.
    dest; split; auto.
  Qed.

  Lemma FirstMP_ValidDeq:
    forall midx msg (mp: MessagePool MsgT),
      FirstMP mp midx msg ->
      ValidDeq mp midx.
  Proof.
    unfold FirstMP, firstMP, ValidDeq; intros.
    destruct (findQ midx mp); discriminate.
  Qed.

  Lemma FirstMPI_Forall_NoDup_ValidDeqs:
    forall msgs (mp: MessagePool MsgT),
      Forall (FirstMPI mp) msgs ->
      NoDup (idsOf msgs) ->
      ValidDeqs mp (idsOf msgs).
  Proof.
    induction msgs; simpl; intros; auto.
    destruct a as [midx msg]; simpl in *.
    inv H; inv H0.
    split.
    - eapply FirstMP_ValidDeq; eauto.
    - eapply IHmsgs; eauto.
      apply FirstMPI_Forall_deqMP; auto.
  Qed.

  Section OnDec.
    Variable (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).

    Lemma countMsg_In_enqMP:
      forall (mp: MessagePool MsgT) idm midx msg,
        idm = (midx, msg) ->
        countMsg msgT_dec idm (enqMP midx msg mp) =
        S (countMsg msgT_dec idm mp).
    Proof.
      unfold enqMP, countMsg, findQ; intros; subst.
      mred; simpl.
      rewrite count_occ_app; simpl.
      destruct (msgT_dec msg msg); [|exfalso; auto].
      apply Nat.add_1_r.
    Qed.

    Lemma countMsg_not_In_enqMP:
      forall (mp: MessagePool MsgT) idm midx msg,
        idm <> (midx, msg) ->
        countMsg msgT_dec idm (enqMP midx msg mp) =
        countMsg msgT_dec idm mp.
    Proof.
      unfold enqMP, countMsg, findQ; intros.
      mred; simpl.
      rewrite count_occ_app; simpl.
      destruct (msgT_dec msg (valOf idm)).
      - exfalso; subst; destruct idm; auto.
      - rewrite Nat.add_0_r; reflexivity.
    Qed.

    Lemma countMsg_enqMsgs:
      forall msgs (mp: MessagePool MsgT) idm,
        countMsg msgT_dec idm (enqMsgs msgs mp) =
        countMsg msgT_dec idm mp + count_occ (id_dec msgT_dec) msgs idm.
    Proof.
      induction msgs; simpl; intros; auto.
      destruct a as [amidx amsg].
      rewrite IHmsgs by auto.
      destruct (id_dec msgT_dec (amidx, amsg) idm).
      - subst; rewrite countMsg_In_enqMP by reflexivity.
        lia.
      - rewrite countMsg_not_In_enqMP by auto.
        reflexivity.
    Qed.

    Lemma countMsg_In_deqMP:
      forall (mp: MessagePool MsgT) idm midx,
        idOf idm = midx ->
        FirstMPI mp idm ->
        S (countMsg msgT_dec idm (deqMP midx mp)) =
        countMsg msgT_dec idm mp.
    Proof.
      unfold FirstMPI, FirstMP, firstMP, deqMP, countMsg, findQ; simpl; intros.
      destruct idm as [midx' msg]; simpl in *; subst.
      destruct (mp@[midx]) as [q|] eqn:Hq; [|discriminate].
      simpl in *.
      destruct q; [discriminate|].
      simpl in *; inv H0.
      destruct (msgT_dec msg msg); [|exfalso; auto].
      mred.
    Qed.

    Lemma countMsg_not_In_deqMP:
      forall (mp: MessagePool MsgT) idm midx,
        (idOf idm <> midx \/ ~ FirstMPI mp idm) ->
        countMsg msgT_dec idm (deqMP midx mp) =
        countMsg msgT_dec idm mp.
    Proof.
      unfold FirstMPI, FirstMP, firstMP, deqMP, countMsg, findQ; simpl; intros.
      destruct idm as [midx' msg]; simpl in *; subst.
      destruct (mp@[midx]) as [q|] eqn:Hq; simpl; [|reflexivity].
      destruct q; [reflexivity|].
      destruct H.
      - mred.
      - mred; simpl.
        destruct (msgT_dec m msg); [exfalso; subst; auto|].
        reflexivity.
    Qed.

    Lemma countMsg_deqMsgs:
      forall idm msgs (mp: MessagePool MsgT),
        NoDup (idsOf msgs) ->
        Forall (FirstMPI mp) msgs ->
        countMsg msgT_dec idm (deqMsgs (idsOf msgs) mp) +
        count_occ (id_dec msgT_dec) msgs idm =
        countMsg msgT_dec idm mp.
    Proof.
      induction msgs; simpl; intros; [lia|].
      inv H; inv H0.
      destruct (id_dec msgT_dec a idm); subst.
      - rewrite Nat.add_succ_r.
        rewrite IHmsgs.
        + apply countMsg_In_deqMP; auto.
        + assumption.
        + apply FirstMPI_Forall_deqMP; auto.
      - rewrite IHmsgs.
        + apply countMsg_not_In_deqMP.
          destruct a as [amidx amsg], idm as [midx msg].
          simpl in *.
          destruct (idx_dec midx amidx); [|auto].
          subst; right.
          intro Hx.
          pose proof (FirstMP_eq H2 Hx); simpl in *; subst.
          auto.
        + assumption.
        + apply FirstMPI_Forall_deqMP; auto.
    Qed.

    Lemma countMsg_InMPI:
      forall idm (mp: MessagePool MsgT),
        InMPI mp idm <-> countMsg msgT_dec idm mp > 0.
    Proof.
      unfold countMsg, InMPI, InMP; intros.
      apply (count_occ_In msgT_dec).
    Qed.

  End OnDec.

End Facts.

Global Opaque ForallMP.
