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

  (* Lemma firstMP_app_or: *)
  (*   forall (msg: MsgT) mind mp1 mp2, *)
  (*     firstMP mind (mp1 ++ mp2) = Some msg -> *)
  (*     firstMP mind mp1 = Some msg \/ *)
  (*     firstMP mind mp2 = Some msg. *)
  (* Proof. *)
  (*   induction mp1; intros; auto. *)
  (*   unfold firstMP in *; simpl in *. *)
  (*   destruct (isAddrOf _ _ _ _). *)
  (*   - left; inv H0; reflexivity. *)
  (*   - auto. *)
  (* Qed. *)

  (* Lemma firstMP_enqMP_or: *)
  (*   forall (msg nmsg: MsgT) mind mp, *)
  (*     firstMP mind (enqMP nmsg mp) = Some msg -> *)
  (*     msg = nmsg \/ firstMP mind mp = Some msg. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply firstMP_app_or in H0; destruct H0; auto. *)
  (*   unfold firstMP in H0; cbn in H0. *)
  (*   destruct (isAddrOf _ _ _ _); [|discriminate]. *)
  (*   inv H0; auto. *)
  (* Qed. *)

  (* Lemma firstMP_enqMsgs_or: *)
  (*   forall (msg: MsgT) mind nmsgs mp, *)
  (*     firstMP mind (enqMsgs nmsgs mp) = Some msg -> *)
  (*     firstMP mind mp = Some msg \/ *)
  (*     firstMP mind nmsgs = Some msg. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply firstMP_app_or; auto. *)
  (* Qed. *)

  (* Lemma firstMP_InMP: *)
  (*   forall (msg: MsgT) mind mp, *)
  (*     firstMP mind mp = Some msg -> *)
  (*     InMP msg mp. *)
  (* Proof. *)
  (*   induction mp; simpl; intros; [discriminate|]. *)
  (*   unfold firstMP in H0; simpl in H0. *)
  (*   destruct (isAddrOf _ _ _ _). *)
  (*   - inv H0; auto. *)
  (*   - right; apply IHmp; auto. *)
  (* Qed. *)

  (* Lemma FirstMP_InMP: *)
  (*   forall (msg: MsgT) mp, *)
  (*     FirstMP mp msg -> *)
  (*     InMP msg mp. *)
  (* Proof. *)
  (*   unfold FirstMP; intros. *)
  (*   eapply firstMP_InMP; eauto. *)
  (* Qed. *)

  (* Lemma ForallMP_InMP_SubList: *)
  (*   forall (msgs: list MsgT) mp, *)
  (*     ForallMP (fun msg => InMP msg mp) msgs -> *)
  (*     SubList msgs mp. *)
  (* Proof. *)
  (*   induction msgs; intros; [apply SubList_nil|]. *)
  (*   inv H0. *)
  (*   apply SubList_cons; auto. *)
  (* Qed. *)

  (* Lemma InMP_deqMP: *)
  (*   forall msg mind mp, *)
  (*     InMP msg (deqMP mind mp) -> *)
  (*     InMP msg mp. *)
  (* Proof. *)
  (*   induction mp; simpl; intros; auto. *)
  (*   destruct (isAddrOf _ _ _ _); auto. *)
  (*   inv H0; auto. *)
  (* Qed. *)

  (* Lemma InMP_removeMP: *)
  (*   forall msg rmsg mp, *)
  (*     InMP msg (removeMP rmsg mp) -> *)
  (*     InMP msg mp. *)
  (* Proof. *)
  (*   unfold removeMP; intros. *)
  (*   eapply InMP_deqMP; eauto. *)
  (* Qed. *)


  (* Lemma ForallMP_forall: *)
  (*   forall P mp, *)
  (*     ForallMP P mp <-> *)
  (*     (forall msg: MsgT, InMP msg mp -> P msg). *)
  (* Proof. *)
  (*   intros; apply Forall_forall. *)
  (* Qed. *)

  (* Lemma ForallMP_SubList: *)
  (*   forall P (mp1 mp2: MessagePool MsgT), *)
  (*     ForallMP P mp2 -> *)
  (*     SubList mp1 mp2 -> *)
  (*     ForallMP P mp1. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply ForallMP_forall; intros. *)
  (*   eapply ForallMP_forall in H0; eauto. *)
  (*   apply H1; auto. *)
  (* Qed. *)

  (* Lemma ForallMP_enqMP: *)
  (*   forall (P: MsgT -> Prop) (msg: MsgT) mp, *)
  (*     ForallMP P mp -> *)
  (*     P msg -> *)
  (*     ForallMP P (enqMP msg mp). *)
  (* Proof. *)
  (*   intros. *)
  (*   apply Forall_app; auto. *)
  (* Qed. *)

  (* Lemma ForallMP_deqMP: *)
  (*   forall (P: MsgT -> Prop) mind mp, *)
  (*     ForallMP P mp -> *)
  (*     ForallMP P (deqMP mind mp). *)
  (* Proof. *)
  (*   induction mp; simpl; intros; auto. *)
  (*   inv H0. *)
  (*   find_if_inside; auto. *)
  (*   constructor; auto. *)
  (*   apply IHmp; auto. *)
  (* Qed. *)

  (* Lemma ForallMP_removeMP: *)
  (*   forall (P: MsgT -> Prop) msg mp, *)
  (*     ForallMP P mp -> *)
  (*     ForallMP P (removeMP msg mp). *)
  (* Proof. *)
  (*   induction mp; simpl; intros; auto. *)
  (*   inv H0. *)
  (*   cbn; destruct (isAddrOf _ _ _ _); auto. *)
  (*   constructor; auto. *)
  (*   apply ForallMP_deqMP; auto. *)
  (* Qed. *)

  (* Lemma ForallMP_enqMsgs: *)
  (*   forall (P: MsgT -> Prop) (nmsgs: list MsgT) mp, *)
  (*     ForallMP P mp -> *)
  (*     ForallMP P nmsgs -> *)
  (*     ForallMP P (enqMsgs nmsgs mp). *)
  (* Proof. *)
  (*   intros. *)
  (*   apply Forall_app; auto. *)
  (* Qed. *)

  (* Lemma ForallMP_deqMsgs: *)
  (*   forall (P: MsgT -> Prop) (dmsgs: list MsgT) mp, *)
  (*     ForallMP P mp -> *)
  (*     ForallMP P (deqMsgs dmsgs mp). *)
  (* Proof. *)
  (*   induction dmsgs; simpl; intros; auto. *)
  (*   apply IHdmsgs. *)
  (*   apply ForallMP_removeMP; auto. *)
  (* Qed. *)

  (* Lemma ForallMP_removeOnce: *)
  (*   forall (msg_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}) *)
  (*          (P: MsgT -> Prop) tmsg mp, *)
  (*     ForallMP P mp -> *)
  (*     ForallMP P (removeOnce msg_dec tmsg mp). *)
  (* Proof. *)
  (*   induction mp; simpl; intros; auto. *)
  (*   inv H0. *)
  (*   find_if_inside; auto. *)
  (*   constructor; auto. *)
  (*   apply IHmp; auto. *)
  (* Qed. *)
  
  (* Lemma deqMP_SubList: *)
  (*   forall mind mp, *)
  (*     SubList (deqMP mind mp) mp. *)
  (* Proof. *)
  (*   induction mp; simpl; intros; [apply SubList_nil|]. *)
  (*   find_if_inside. *)
  (*   - right; auto. *)
  (*   - apply SubList_cons; [left; reflexivity|]. *)
  (*     apply SubList_cons_right; auto. *)
  (* Qed. *)

  (* Lemma findMP_MsgAddr: *)
  (*   forall mind msg mp, *)
  (*     hd_error (findMP mind mp) = Some msg -> *)
  (*     mid_addr (msg_id (getMsg msg)) = buildMsgAddr mind. *)
  (* Proof. *)
  (*   induction mp; simpl; intros; [discriminate|]. *)
  (*   unfold isAddrOf in H0. *)
  (*   destruct (msgAddr_dec _ _); auto. *)
  (*   inv H0; auto. *)
  (* Qed. *)

  (* Lemma firstMP_MsgAddr: *)
  (*   forall mind mp msg, *)
  (*     firstMP mind mp = Some msg -> *)
  (*     mid_addr (msg_id (getMsg msg)) = buildMsgAddr mind. *)
  (* Proof. *)
  (*   unfold firstMP; intros. *)
  (*   eapply findMP_MsgAddr; eauto. *)
  (* Qed. *)

  (* Lemma removeMP_deqMP: *)
  (*   forall msg mid mp, *)
  (*     msg_id (getMsg msg) = mid -> *)
  (*     removeMP msg mp = deqMP (mid_from mid) (mid_to mid) (mid_chn mid) mp. *)
  (* Proof. *)
  (*   intros; subst; reflexivity. *)
  (* Qed. *)

  (* Lemma firstMP_FirstMP: *)
  (*   forall mind mp msg, *)
  (*     firstMP mind mp = Some msg -> *)
  (*     FirstMP mp msg. *)
  (* Proof. *)
  (*   unfold FirstMP; intros. *)
  (*   pose proof (firstMP_MsgAddr _ _ _ _ H0). *)
  (*   destruct (msg_id (getMsg msg)) as [[ ]]; cbn in *. *)
  (*   inv H1; assumption. *)
  (* Qed. *)

  (* Lemma findMP_nil: *)
  (*   forall mp, *)
  (*     (forall mind, findMP mind mp = nil) -> *)
  (*     mp = nil. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct mp as [|msg ?]; auto. *)
  (*   exfalso. *)
  (*   specialize (H0 (mid_from (msg_id (getMsg msg))) *)
  (*                  (mid_to (msg_id (getMsg msg))) *)
  (*                  (mid_chn (msg_id (getMsg msg)))). *)
  (*   simpl in H0. *)
  (*   unfold isAddrOf in H0. *)
  (*   destruct (msgAddr_dec _ _); [discriminate|]. *)
  (*   elim n. *)
  (*   destruct (getMsg msg) as [[[mind] tid] val]; cbn in *. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma findMP_app: *)
  (*   forall mind mp1 mp2, *)
  (*     findMP mind (mp1 ++ mp2) = *)
  (*     findMP mind mp1 ++ findMP mind mp2. *)
  (* Proof. *)
  (*   unfold findMP; intros. *)
  (*   apply filter_app. *)
  (* Qed. *)

  (* Lemma findMP_SubList: *)
  (*   forall mind mp, *)
  (*     SubList (findMP mind mp) mp. *)
  (* Proof. *)
  (*   unfold SubList, findMP; intros. *)
  (*   apply filter_In in H0; dest; auto. *)
  (* Qed. *)

  (* Corollary findMP_enqMP: *)
  (*   forall mind mp msg, *)
  (*     findMP mind (enqMP msg mp) = *)
  (*     findMP mind mp ++ findMP mind [msg]. *)
  (* Proof. *)
  (*   unfold enqMP; intros. *)
  (*   apply findMP_app. *)
  (* Qed. *)

  (* Lemma FirstMP_enqMP: *)
  (*   forall mp msg, *)
  (*     FirstMP mp msg -> *)
  (*     forall emsg, *)
  (*       FirstMP (enqMP emsg mp) msg. *)
  (* Proof. *)
  (*   unfold FirstMP, firstMP, enqMP; intros. *)
  (*   rewrite findMP_app. *)
  (*   apply hd_error_Some_app; auto. *)
  (* Qed. *)

  (* Lemma FirstMP_enqMsgs: *)
  (*   forall mp msg, *)
  (*     FirstMP mp msg -> *)
  (*     forall eins, *)
  (*       FirstMP (enqMsgs eins mp) msg. *)
  (* Proof. *)
  (*   unfold FirstMP, firstMP, enqMsgs; intros. *)
  (*   rewrite findMP_app. *)
  (*   apply hd_error_Some_app; auto. *)
  (* Qed. *)

  (* Lemma findMP_deqMP_eq: *)
  (*   forall mind mp, *)
  (*     findMP mind (deqMP mind mp) = *)
  (*     deqMP mind (findMP mind mp). *)
  (* Proof. *)
  (*   induction mp; simpl; intros; [reflexivity|]. *)
  (*   unfold isAddrOf; destruct (msgAddr_dec _ _). *)
  (*   - simpl; unfold isAddrOf. *)
  (*     destruct (msgAddr_dec _ _); auto. *)
  (*     elim n; assumption. *)
  (*   - simpl; unfold isAddrOf. *)
  (*     destruct (msgAddr_dec _ _); auto. *)
  (*     elim n; assumption. *)
  (* Qed. *)

  (* Lemma findMP_deqMP_neq: *)
  (*   forall mind dfrom dto dchn mp, *)
  (*     buildMsgAddr mind <> buildMsgAddr dfrom dto dchn -> *)
  (*     findMP mind (deqMP dfrom dto dchn mp) = *)
  (*     findMP mind mp. *)
  (* Proof. *)
  (*   induction mp; intros; [reflexivity|]. *)
  (*   simpl; unfold isAddrOf. *)
  (*   destruct (msgAddr_dec _ _). *)
  (*   - destruct (msgAddr_dec _ _); auto. *)
  (*     rewrite e0 in e; elim H0; assumption. *)
  (*   - simpl; unfold isAddrOf. *)
  (*     destruct (msgAddr_dec _ _); auto. *)
  (*     rewrite e in n. *)
  (*     erewrite IHmp; eauto. *)
  (* Qed. *)

  (* Lemma firstMP_deqMP_app: *)
  (*   forall mp1 mind, *)
  (*     firstMP mind mp1 <> None -> *)
  (*     forall mp2, *)
  (*       deqMP mind (mp1 ++ mp2) = *)
  (*       deqMP mind mp1 ++ mp2. *)
  (* Proof. *)
  (*   induction mp1; simpl; intros; [elim H0; reflexivity|]. *)
  (*   unfold isAddrOf; destruct (msgAddr_dec _ _); auto. *)
  (*   simpl; rewrite IHmp1; [reflexivity|]. *)
  (*   assert (exists v, firstMP mind ([a] ++ mp1) = Some v). *)
  (*   { simpl. *)
  (*     destruct (firstMP mind (a :: mp1)); [|exfalso; auto]. *)
  (*     eexists; reflexivity. *)
  (*   } *)
  (*   destruct H1 as [v ?]. *)
  (*   apply firstMP_app_or in H1; destruct H1. *)
  (*   - exfalso. *)
  (*     unfold firstMP, findMP, isAddrOf in H1; simpl in H1. *)
  (*     destruct (msgAddr_dec _ _); auto. *)
  (*     discriminate. *)
  (*   - rewrite H1; discriminate. *)
  (* Qed. *)

  (* Lemma FirstMP_deqMP_enqMP_comm: *)
  (*   forall mp mind emsg, *)
  (*     firstMP mind mp <> None -> *)
  (*     deqMP mind (enqMP emsg mp) = *)
  (*     enqMP emsg (deqMP mind mp). *)
  (* Proof. *)
  (*   unfold enqMP; intros. *)
  (*   apply firstMP_deqMP_app; auto. *)
  (* Qed. *)

  (* Lemma FirstMP_deqMP_enqMsgs_comm: *)
  (*   forall mp mind mins, *)
  (*     firstMP mind mp <> None -> *)
  (*     deqMP mind (enqMsgs mins mp) = *)
  (*     enqMsgs mins (deqMP mind mp). *)
  (* Proof. *)
  (*   unfold enqMP; intros. *)
  (*   apply firstMP_deqMP_app; auto. *)
  (* Qed. *)

  (* Lemma FirstMP_removeMP_enqMP_comm: *)
  (*   forall mp rmsg, *)
  (*     FirstMP mp rmsg -> *)
  (*     forall emsg, *)
  (*       removeMP rmsg (enqMP emsg mp) = *)
  (*       enqMP emsg (removeMP rmsg mp). *)
  (* Proof. *)
  (*   unfold removeMP; intros. *)
  (*   apply FirstMP_deqMP_enqMP_comm. *)
  (*   rewrite H0; discriminate. *)
  (* Qed. *)

  (* Lemma FirstMP_removeMP_enqMsgs_comm: *)
  (*   forall mp rmsg, *)
  (*     FirstMP mp rmsg -> *)
  (*     forall mins, *)
  (*       removeMP rmsg (enqMsgs mins mp) = *)
  (*       enqMsgs mins (removeMP rmsg mp). *)
  (* Proof. *)
  (*   unfold removeMP; intros. *)
  (*   apply FirstMP_deqMP_enqMsgs_comm. *)
  (*   rewrite H0; discriminate. *)
  (* Qed. *)

  (* Lemma firstMP'_firstMP'_removeMP: *)
  (*   forall mp from1 to1 chn1 msg1 from2 to2 chn2 msg2, *)
  (*     buildMsgAddr from1 to1 chn1 <> buildMsgAddr from2 to2 chn2 -> *)
  (*     firstMP' from1 to1 chn1 mp = Some msg1 -> *)
  (*     firstMP' from2 to2 chn2 mp = Some msg2 -> *)
  (*     firstMP' from2 to2 chn2 (removeMP msg1 mp) = Some msg2. *)
  (* Proof. *)
  (*   intros. *)
  (*   pose proof H1; rewrite <-firstMP_firstMP' in H3. *)
  (*   apply firstMP_MsgAddr in H3. *)
  (*   pose proof H2; rewrite <-firstMP_firstMP' in H4. *)
  (*   apply firstMP_MsgAddr in H4. *)
  (*   induction mp; simpl; intros; [discriminate|]. *)
  (*   cbn in *. *)
  (*   remember (getMsg msg1) as m1. *)
  (*   destruct m1 as [[[mfrom1 mto1 mchn1] mtid1] mval1]; cbn in *. *)
  (*   remember (getMsg msg2) as m2. *)
  (*   destruct m2 as [[[mfrom2 mto2 mchn2] mtid2] mval2]; cbn in *. *)
  (*   inv H3; inv H4. *)
  (*   unfold isAddrOf in *. *)
  (*   destruct (msgAddr_dec _ _). *)
  (*   - destruct (msgAddr_dec _ _); auto. *)
  (*     exfalso; inv H1; inv H2. *)
  (*     rewrite e in e0; auto. *)
  (*   - simpl; unfold isAddrOf. *)
  (*     destruct (msgAddr_dec _ _); auto. *)
  (*     specialize (IHmp H1 H2). *)
  (*     erewrite removeMP_deqMP in IHmp by reflexivity. *)
  (*     rewrite <-Heqm1 in IHmp. *)
  (*     assumption. *)
  (* Qed. *)
    
  (* Lemma FirstMP_FirstMP_removeMP: *)
  (*   forall mp msg1 msg2, *)
  (*     mid_addr (msg_id (getMsg msg1)) <> mid_addr (msg_id (getMsg msg2)) -> *)
  (*     FirstMP mp msg1 -> *)
  (*     FirstMP mp msg2 -> *)
  (*     FirstMP (removeMP msg1 mp) msg2. *)
  (* Proof. *)
  (*   unfold FirstMP; intros. *)
  (*   rewrite firstMP_firstMP' in *. *)
  (*   induction mp; simpl; intros; [inv H1|]. *)
  (*   inv H1. *)
  (*   unfold FirstMP in *; intros. *)
  (*   eapply firstMP'_firstMP'_removeMP; eauto. *)
  (*   destruct (getMsg msg1) as [[[mfrom1 mto1 mchn1] mtid1] mval1]; cbn in *. *)
  (*   destruct (getMsg msg2) as [[[mfrom2 mto2 mchn2] mtid2] mval2]; cbn in *. *)
  (*   auto. *)
  (* Qed. *)

  (* Corollary FirstMP_Forall_FirstMP_removeMP: *)
  (*   forall mp msg1 msgs2, *)
  (*     Forall (fun msg2 => mid_addr (msg_id (getMsg msg1)) <> *)
  (*                         mid_addr (msg_id (getMsg msg2))) msgs2 -> *)
  (*     FirstMP mp msg1 -> *)
  (*     Forall (FirstMP mp) msgs2 -> *)
  (*     Forall (FirstMP (removeMP msg1 mp)) msgs2. *)
  (* Proof. *)
  (*   induction msgs2; simpl; intros; [constructor|]. *)
  (*   inv H0; inv H2. *)
  (*   constructor; auto. *)
  (*   apply FirstMP_FirstMP_removeMP; auto. *)
  (* Qed. *)

  (* Lemma FirstMP_deqMsgs_enqMP_comm: *)
  (*   forall msgs mp, *)
  (*     NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) msgs) -> *)
  (*     Forall (FirstMP mp) msgs -> *)
  (*     forall msg, *)
  (*       deqMsgs msgs (enqMP msg mp) = *)
  (*       enqMP msg (deqMsgs msgs mp). *)
  (* Proof. *)
  (*   induction msgs; simpl; intros; [reflexivity|]. *)
  (*   inv H0; inv H1. *)
  (*   rewrite FirstMP_removeMP_enqMP_comm by assumption. *)
  (*   rewrite <-IHmsgs; [reflexivity|assumption|]. *)
  (*   apply FirstMP_Forall_FirstMP_removeMP; auto. *)

  (*   clear -H4. *)
  (*   induction msgs; [constructor|]. *)
  (*   constructor. *)
  (*   - intro Hx; elim H4; left; auto. *)
  (*   - eapply IHmsgs. *)
  (*     intro Hx; elim H4; right; auto. *)
  (* Qed. *)

  (* Lemma FirstMP_deqMsgs_enqMsgs_comm: *)
  (*   forall msgs mp, *)
  (*     NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) msgs) -> *)
  (*     Forall (FirstMP mp) msgs -> *)
  (*     forall mins, *)
  (*       deqMsgs msgs (enqMsgs mins mp) = *)
  (*       enqMsgs mins (deqMsgs msgs mp). *)
  (* Proof. *)
  (*   induction msgs; simpl; intros; [reflexivity|]. *)
  (*   inv H0; inv H1. *)
  (*   rewrite FirstMP_removeMP_enqMsgs_comm by assumption. *)
  (*   rewrite <-IHmsgs; [reflexivity|assumption|]. *)
  (*   apply FirstMP_Forall_FirstMP_removeMP; auto. *)

  (*   clear -H4. *)
  (*   induction msgs; [constructor|]. *)
  (*   constructor. *)
  (*   - intro Hx; elim H4; left; auto. *)
  (*   - eapply IHmsgs. *)
  (*     intro Hx; elim H4; right; auto. *)
  (* Qed. *)

End Facts.

Global Opaque ForallMP.


Section Map.
  Variables (MsgT1 MsgT2: Type).
  Context `{HasMsg MsgT1} `{HasMsg MsgT2}.

  Variable (mmap: MsgT1 -> MsgT2).
  Hypothesis (Hmmap: forall msg, getMsg (mmap msg) = getMsg msg).

  Definition mpmap (mp: MessagePool MsgT1): MessagePool MsgT2 :=
    M.map (map mmap) mp.

  (* Lemma mmap_findMP: *)
  (*   forall mind mp, *)
  (*     findMP mind (map mmap mp) = *)
  (*     map mmap (findMP mind mp). *)
  (* Proof. *)
  (*   induction mp; simpl; intros; auto. *)
  (*   unfold isAddrOf in *. *)
  (*   rewrite IHmp. *)
  (*   rewrite Hmmap. *)
  (*   destruct (msgAddr_dec _ _); auto. *)
  (* Qed. *)

  (* Lemma mmap_firstMP: *)
  (*   forall mind mp, *)
  (*     firstMP mind (map mmap mp) = *)
  (*     lift mmap (firstMP mind mp). *)
  (* Proof. *)
  (*   unfold firstMP; intros. *)
  (*   rewrite mmap_findMP. *)
  (*   apply eq_sym, lift_hd_error. *)
  (* Qed. *)

  (* Lemma mmap_FirstMP: *)
  (*   forall mp msg, *)
  (*     FirstMP mp msg -> *)
  (*     FirstMP (map mmap mp) (mmap msg). *)
  (* Proof. *)
  (*   unfold FirstMP; intros. *)
  (*   rewrite mmap_firstMP. *)
  (*   rewrite Hmmap. *)
  (*   rewrite H1. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma mmap_deqMP: *)
  (*   forall mp mind, *)
  (*     map mmap (deqMP mind mp) = *)
  (*     deqMP mind (map mmap mp). *)
  (* Proof. *)
  (*   induction mp; simpl; intros; auto. *)
  (*   unfold isAddrOf in *. *)
  (*   rewrite Hmmap. *)
  (*   destruct (msgAddr_dec _ _); auto. *)
  (*   simpl; rewrite IHmp; auto. *)
  (* Qed. *)
  
  (* Lemma mmap_removeMP: *)
  (*   forall mp msg, *)
  (*     map mmap (removeMP msg mp) = *)
  (*     removeMP (mmap msg) (map mmap mp). *)
  (* Proof. *)
  (*   unfold removeMP; intros. *)
  (*   rewrite Hmmap. *)
  (*   apply mmap_deqMP. *)
  (* Qed. *)

  (* Lemma mmap_deqMsgs: *)
  (*   forall msgs mp, *)
  (*     map mmap (deqMsgs msgs mp) = *)
  (*     deqMsgs (map mmap msgs) (map mmap mp). *)
  (* Proof. *)
  (*   induction msgs; simpl; intros; auto. *)
  (*   rewrite IHmsgs. *)
  (*   rewrite mmap_removeMP. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma mmap_enqMsgs: *)
  (*   forall mp msgs, *)
  (*     map mmap (enqMsgs msgs mp) = *)
  (*     enqMsgs (map mmap msgs) (map mmap mp). *)
  (* Proof. *)
  (*   unfold enqMsgs; intros. *)
  (*   apply map_app. *)
  (* Qed. *)
  
End Map.

