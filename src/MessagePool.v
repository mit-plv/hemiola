Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax.

Set Implicit Arguments.

Section MessagePool.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Definition Queue := list MsgT.
  Definition MessagePool := list MsgT.

  Definition findMP (from to chn: IdxT) (mp: MessagePool): Queue :=
    filter (fun msg =>
              if msgAddr_dec (mid_addr (msg_id (getMsg msg))) (buildMsgAddr from to chn)
              then true
              else false) mp.

  Definition firstMP (from to chn: IdxT) (mp: MessagePool) :=
    hd_error (findMP from to chn mp).

  Fixpoint deqMP (from to chn: IdxT) (mp: MessagePool): MessagePool :=
    match mp with
    | nil => nil
    | msg :: mp' =>
      if msgAddr_dec (mid_addr (msg_id (getMsg msg))) (buildMsgAddr from to chn)
      then mp'
      else msg :: deqMP from to chn mp'
    end.

  Definition enqMP (m: MsgT) (mp: MessagePool): MessagePool := mp ++ (m :: nil).

  Definition removeMP (m: MsgT) (mp: MessagePool): MessagePool :=
    let mid := msg_id (getMsg m) in
    deqMP (mid_from mid) (mid_to mid) (mid_chn mid) mp.

  Definition FirstMP (mp: MessagePool) (m: MsgT) :=
    let mid := msg_id (getMsg m) in
    firstMP (mid_from mid) (mid_to mid) (mid_chn mid) mp = Some m.
  
  Definition EmptyMP (mp: MessagePool) := mp = nil.
  Definition InMP (msg: MsgT) (mp: MessagePool) := In msg mp.

  Definition ForallMP (P: MsgT -> Prop) (mp: MessagePool) :=
    Forall P mp.

  Definition distributeMsgs (nmsgs: list MsgT) (mp: MessagePool): MessagePool :=
    mp ++ nmsgs.

  Fixpoint removeMsgs (dmsgs: list MsgT) (mp: MessagePool): MessagePool :=
    match dmsgs with
    | nil => mp
    | dmsg :: dmsgs' =>
      removeMsgs dmsgs' (removeMP dmsg mp)
    end.
  
End MessagePool.

Section Facts.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Lemma firstMP_app_or:
    forall (msg: MsgT) from to chn mp1 mp2,
      firstMP from to chn (mp1 ++ mp2) = Some msg ->
      firstMP from to chn mp1 = Some msg \/
      firstMP from to chn mp2 = Some msg.
  Proof.
    induction mp1; intros; auto.
    unfold firstMP in *; simpl in *.
    destruct (msgAddr_dec _ _).
    - left; inv H0; reflexivity.
    - auto.
  Qed.

  Lemma firstMP_enqMP_or:
    forall (msg nmsg: MsgT) from to chn mp,
      firstMP from to chn (enqMP nmsg mp) = Some msg ->
      msg = nmsg \/ firstMP from to chn mp = Some msg.
  Proof.
    intros.
    apply firstMP_app_or in H0; destruct H0; auto.
    unfold firstMP in H0; cbn in H0.
    destruct (msgAddr_dec _ _); [|discriminate].
    inv H0; auto.
  Qed.

  Lemma firstMP_distributeMsgs_or:
    forall (msg: MsgT) from to chn nmsgs mp,
      firstMP from to chn (distributeMsgs nmsgs mp) = Some msg ->
      firstMP from to chn mp = Some msg \/
      firstMP from to chn nmsgs = Some msg.
  Proof.
    intros.
    apply firstMP_app_or; auto.
  Qed.

  Lemma inMP_enqMP_or:
    forall (msg: MsgT) nmsg mp,
      InMP msg (enqMP nmsg mp) ->
      msg = nmsg \/ InMP msg mp.
  Proof.
    intros.
    apply in_app_or in H0; destruct H0; auto.
    Common.dest_in; auto.
  Qed.

  Lemma inMP_deqMP:
    forall (msg: MsgT) from to chn mp,
      InMP msg (deqMP from to chn mp) ->
      InMP msg mp.
  Proof.
    induction mp; simpl; intros; auto.
    find_if_inside; auto.
    inv H0; auto.
  Qed.

  Lemma inMP_distributeMsgs_or:
    forall (msg: MsgT) nmsgs mp,
      InMP msg (distributeMsgs nmsgs mp) ->
      In msg nmsgs \/ InMP msg mp.
  Proof.
    intros; apply in_app_or in H0; destruct H0; auto.
  Qed.

  Lemma firstMP_InMP:
    forall (msg: MsgT) from to chn mp,
      firstMP from to chn mp = Some msg ->
      InMP msg mp.
  Proof.
    induction mp; simpl; intros; [discriminate|].
    unfold firstMP in H0; simpl in H0.
    destruct (msgAddr_dec _ _).
    - inv H0; auto.
    - right; apply IHmp; auto.
  Qed.

  Lemma FirstMP_InMP:
    forall (msg: MsgT) mp,
      FirstMP mp msg ->
      InMP msg mp.
  Proof.
    unfold FirstMP; intros.
    eapply firstMP_InMP; eauto.
  Qed.

  Lemma ForallMP_InMP_SubList:
    forall (msgs: list MsgT) mp,
      ForallMP (fun msg => InMP msg mp) msgs ->
      SubList msgs mp.
  Proof.
    induction msgs; intros; [apply SubList_nil|].
    inv H0.
    apply SubList_cons; auto.
  Qed.

  Lemma ForallMP_forall:
    forall P mp,
      ForallMP P mp <->
      (forall msg: MsgT, InMP msg mp -> P msg).
  Proof.
    intros; apply Forall_forall.
  Qed.

  Lemma ForallMP_SubList:
    forall P (mp1 mp2: MessagePool MsgT),
      ForallMP P mp2 ->
      SubList mp1 mp2 ->
      ForallMP P mp1.
  Proof.
    intros.
    apply ForallMP_forall; intros.
    eapply ForallMP_forall in H0; eauto.
    apply H1; auto.
  Qed.

  Lemma ForallMP_enqMP:
    forall (P: MsgT -> Prop) (msg: MsgT) mp,
      ForallMP P mp ->
      P msg ->
      ForallMP P (enqMP msg mp).
  Proof.
    intros.
    apply Forall_app; auto.
  Qed.

  Lemma ForallMP_deqMP:
    forall (P: MsgT -> Prop) from to chn mp,
      ForallMP P mp ->
      ForallMP P (deqMP from to chn mp).
  Proof.
    induction mp; simpl; intros; auto.
    inv H0.
    find_if_inside; auto.
    constructor; auto.
    apply IHmp; auto.
  Qed.

  Lemma ForallMP_removeMP:
    forall (P: MsgT -> Prop) msg mp,
      ForallMP P mp ->
      ForallMP P (removeMP msg mp).
  Proof.
    induction mp; simpl; intros; auto.
    inv H0.
    cbn; destruct (msgAddr_dec _ _); auto.
    constructor; auto.
    apply ForallMP_deqMP; auto.
  Qed.

  Lemma ForallMP_distributeMsgs:
    forall (P: MsgT -> Prop) (nmsgs: list MsgT) mp,
      ForallMP P mp ->
      ForallMP P nmsgs ->
      ForallMP P (distributeMsgs nmsgs mp).
  Proof.
    intros.
    apply Forall_app; auto.
  Qed.

  Lemma ForallMP_removeMsgs:
    forall (P: MsgT -> Prop) (dmsgs: list MsgT) mp,
      ForallMP P mp ->
      ForallMP P (removeMsgs dmsgs mp).
  Proof.
    induction dmsgs; simpl; intros; auto.
    apply IHdmsgs.
    apply ForallMP_removeMP; auto.
  Qed.

  Lemma ForallMP_removeOnce:
    forall (msg_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2})
           (P: MsgT -> Prop) tmsg mp,
      ForallMP P mp ->
      ForallMP P (removeOnce msg_dec tmsg mp).
  Proof.
    induction mp; simpl; intros; auto.
    inv H0.
    find_if_inside; auto.
    constructor; auto.
    apply IHmp; auto.
  Qed.
  
  Lemma deqMP_SubList:
    forall from to chn mp,
      SubList (deqMP from to chn mp) mp.
  Proof.
    induction mp; simpl; intros; [apply SubList_nil|].
    find_if_inside.
    - right; auto.
    - apply SubList_cons; [left; reflexivity|].
      apply SubList_cons_right; auto.
  Qed.

  Lemma findMP_MsgAddr:
    forall from to chn msg mp,
      hd_error (findMP from to chn mp) = Some msg ->
      mid_addr (msg_id (getMsg msg)) = buildMsgAddr from to chn.
  Proof.
    induction mp; simpl; intros; [discriminate|].
    destruct (msgAddr_dec _ _); auto.
    inv H0; auto.
  Qed.

  Lemma firstMP_MsgAddr:
    forall from to chn mp msg,
      firstMP from to chn mp = Some msg ->
      mid_addr (msg_id (getMsg msg)) = buildMsgAddr from to chn.
  Proof.
    unfold firstMP; intros.
    eapply findMP_MsgAddr; eauto.
  Qed.

  Lemma removeMP_deqMP:
    forall msg mid mp,
      msg_id (getMsg msg) = mid ->
      removeMP msg mp = deqMP (mid_from mid) (mid_to mid) (mid_chn mid) mp.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Lemma firstMP_FirstMP:
    forall from to chn mp msg,
      firstMP from to chn mp = Some msg ->
      FirstMP mp msg.
  Proof.
    unfold FirstMP; intros.
    pose proof (firstMP_MsgAddr _ _ _ _ H0).
    destruct (msg_id (getMsg msg)) as [[ ]]; cbn in *.
    inv H1; assumption.
  Qed.

End Facts.

Section Map.
  Variables (MsgT1 MsgT2: Type).
  Context `{HasMsg MsgT1} `{HasMsg MsgT2}.

  Variable (mmap: MsgT1 -> MsgT2).
  Hypothesis (Hmmap: forall msg, getMsg (mmap msg) = getMsg msg).

  Lemma mmap_findMP:
    forall from to chn mp,
      findMP from to chn (map mmap mp) =
      map mmap (findMP from to chn mp).
  Proof.
    induction mp; simpl; intros; auto.
    rewrite IHmp.
    rewrite Hmmap.
    destruct (msgAddr_dec _ _); auto.
  Qed.

  Lemma mmap_firstMP:
    forall from to chn mp,
      firstMP from to chn (map mmap mp) =
      lift mmap (firstMP from to chn mp).
  Proof.
    unfold firstMP; intros.
    rewrite mmap_findMP.
    apply eq_sym, lift_hd_error.
  Qed.

  Lemma mmap_FirstMP:
    forall mp msg,
      FirstMP mp msg ->
      FirstMP (map mmap mp) (mmap msg).
  Proof.
    unfold FirstMP; intros.
    rewrite mmap_firstMP.
    rewrite Hmmap.
    rewrite H1.
    reflexivity.
  Qed.

  Lemma mmap_deqMP:
    forall mp from to chn,
      map mmap (deqMP from to chn mp) =
      deqMP from to chn (map mmap mp).
  Proof.
    induction mp; simpl; intros; auto.
    rewrite Hmmap.
    destruct (msgAddr_dec _ _); auto.
    simpl; rewrite IHmp; auto.
  Qed.
  
  Lemma mmap_removeMP:
    forall mp msg,
      map mmap (removeMP msg mp) =
      removeMP (mmap msg) (map mmap mp).
  Proof.
    unfold removeMP; intros.
    rewrite Hmmap.
    apply mmap_deqMP.
  Qed.

  Lemma mmap_distributeMsgs:
    forall mp msgs,
      map mmap (distributeMsgs msgs mp) =
      distributeMsgs (map mmap msgs) (map mmap mp).
  Proof.
    unfold distributeMsgs; intros.
    apply map_app.
  Qed.
  
End Map.

