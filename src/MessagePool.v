Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax.

Set Implicit Arguments.

Section MessagePool.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Definition Queue := list MsgT.
  Definition MessagePool := list MsgT.

  Definition isAddrOf (from to chn: IdxT) (msg: MsgT) :=
    if msgAddr_dec (mid_addr (msg_id (getMsg msg))) (buildMsgAddr from to chn)
    then true
    else false.

  Definition findMP (from to chn: IdxT) (mp: MessagePool): Queue :=
    filter (fun msg => isAddrOf from to chn msg) mp.

  Definition firstMP (from to chn: IdxT) (mp: MessagePool) :=
    hd_error (findMP from to chn mp).

  Fixpoint firstMP' (from to chn: IdxT) (mp: MessagePool) :=
    match mp with
    | nil => None
    | msg :: mp' =>
      if isAddrOf from to chn msg
      then Some msg
      else firstMP' from to chn mp'
    end.

  Fixpoint deqMP (from to chn: IdxT) (mp: MessagePool): MessagePool :=
    match mp with
    | nil => nil
    | msg :: mp' =>
      if isAddrOf from to chn msg
      then mp'
      else msg :: deqMP from to chn mp'
    end.

  (* NOTE: the head is the oldest one. *)
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

  Lemma firstMP_firstMP':
    forall from to chn mp,
      firstMP from to chn mp = firstMP' from to chn mp.
  Proof.
    induction mp; simpl; intros; [reflexivity|].
    unfold firstMP, findMP; simpl.
    destruct (isAddrOf _ _ _ _); auto.
  Qed.

  Lemma firstMP_app_or:
    forall (msg: MsgT) from to chn mp1 mp2,
      firstMP from to chn (mp1 ++ mp2) = Some msg ->
      firstMP from to chn mp1 = Some msg \/
      firstMP from to chn mp2 = Some msg.
  Proof.
    induction mp1; intros; auto.
    unfold firstMP in *; simpl in *.
    destruct (isAddrOf _ _ _ _).
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
    destruct (isAddrOf _ _ _ _); [|discriminate].
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
    destruct (isAddrOf _ _ _ _).
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
    cbn; destruct (isAddrOf _ _ _ _); auto.
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
    unfold isAddrOf in H0.
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

  Lemma findMP_nil:
    forall mp,
      (forall from to chn, findMP from to chn mp = nil) ->
      mp = nil.
  Proof.
    intros.
    destruct mp as [|msg ?]; auto.
    exfalso.
    specialize (H0 (mid_from (msg_id (getMsg msg)))
                   (mid_to (msg_id (getMsg msg)))
                   (mid_chn (msg_id (getMsg msg)))).
    simpl in H0.
    unfold isAddrOf in H0.
    destruct (msgAddr_dec _ _); [discriminate|].
    elim n.
    destruct (getMsg msg) as [[[from to chn] tid] val]; cbn in *.
    reflexivity.
  Qed.

  Lemma findMP_app:
    forall from to chn mp1 mp2,
      findMP from to chn (mp1 ++ mp2) =
      findMP from to chn mp1 ++ findMP from to chn mp2.
  Proof.
    unfold findMP; intros.
    apply filter_app.
  Qed.

  Lemma findMP_SubList:
    forall from to chn mp,
      SubList (findMP from to chn mp) mp.
  Proof.
    unfold SubList, findMP; intros.
    apply filter_In in H0; dest; auto.
  Qed.

  Corollary findMP_enqMP:
    forall from to chn mp msg,
      findMP from to chn (enqMP msg mp) =
      findMP from to chn mp ++ findMP from to chn [msg].
  Proof.
    unfold enqMP; intros.
    apply findMP_app.
  Qed.

  Lemma FirstMP_enqMP:
    forall mp msg,
      FirstMP mp msg ->
      forall emsg,
        FirstMP (enqMP emsg mp) msg.
  Proof.
    unfold FirstMP, firstMP, enqMP; intros.
    rewrite findMP_app.
    apply hd_error_Some_app; auto.
  Qed.

  Lemma findMP_deqMP_eq:
    forall from to chn mp,
      findMP from to chn (deqMP from to chn mp) =
      deqMP from to chn (findMP from to chn mp).
  Proof.
    induction mp; simpl; intros; [reflexivity|].
    unfold isAddrOf; destruct (msgAddr_dec _ _).
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      elim n; assumption.
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      elim n; assumption.
  Qed.

  Lemma findMP_deqMP_neq:
    forall from to chn dfrom dto dchn mp,
      buildMsgAddr from to chn <> buildMsgAddr dfrom dto dchn ->
      findMP from to chn (deqMP dfrom dto dchn mp) =
      findMP from to chn mp.
  Proof.
    induction mp; intros; [reflexivity|].
    simpl; unfold isAddrOf.
    destruct (msgAddr_dec _ _).
    - destruct (msgAddr_dec _ _); auto.
      rewrite e0 in e; elim H0; assumption.
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      rewrite e in n.
      erewrite IHmp; eauto.
  Qed.

  Lemma firstMP_deqMP_app:
    forall mp1 from to chn,
      firstMP from to chn mp1 <> None ->
      forall mp2,
        deqMP from to chn (mp1 ++ mp2) =
        deqMP from to chn mp1 ++ mp2.
  Proof.
    induction mp1; simpl; intros; [elim H0; reflexivity|].
    unfold isAddrOf; destruct (msgAddr_dec _ _); auto.
    simpl; rewrite IHmp1; [reflexivity|].
    assert (exists v, firstMP from to chn ([a] ++ mp1) = Some v).
    { simpl.
      destruct (firstMP from to chn (a :: mp1)); [|exfalso; auto].
      eexists; reflexivity.
    }
    destruct H1 as [v ?].
    apply firstMP_app_or in H1; destruct H1.
    - exfalso.
      unfold firstMP, findMP, isAddrOf in H1; simpl in H1.
      destruct (msgAddr_dec _ _); auto.
      discriminate.
    - rewrite H1; discriminate.
  Qed.

  Lemma FirstMP_deqMP_enqMP_comm:
    forall mp from to chn emsg,
      firstMP from to chn mp <> None ->
      deqMP from to chn (enqMP emsg mp) =
      enqMP emsg (deqMP from to chn mp).
  Proof.
    unfold enqMP; intros.
    apply firstMP_deqMP_app; auto.
  Qed.    

  Lemma FirstMP_removeMP_enqMP_comm:
    forall mp rmsg,
      FirstMP mp rmsg ->
      forall emsg,
        removeMP rmsg (enqMP emsg mp) =
        enqMP emsg (removeMP rmsg mp).
  Proof.
    unfold removeMP; intros.
    apply FirstMP_deqMP_enqMP_comm.
    rewrite H0; discriminate.
  Qed.

  Lemma firstMP'_firstMP'_removeMP:
    forall mp from1 to1 chn1 msg1 from2 to2 chn2 msg2,
      buildMsgAddr from1 to1 chn1 <> buildMsgAddr from2 to2 chn2 ->
      firstMP' from1 to1 chn1 mp = Some msg1 ->
      firstMP' from2 to2 chn2 mp = Some msg2 ->
      firstMP' from2 to2 chn2 (removeMP msg1 mp) = Some msg2.
  Proof.
    intros.
    pose proof H1; rewrite <-firstMP_firstMP' in H3.
    apply firstMP_MsgAddr in H3.
    pose proof H2; rewrite <-firstMP_firstMP' in H4.
    apply firstMP_MsgAddr in H4.
    induction mp; simpl; intros; [discriminate|].
    cbn in *.
    remember (getMsg msg1) as m1.
    destruct m1 as [[[mfrom1 mto1 mchn1] mtid1] mval1]; cbn in *.
    remember (getMsg msg2) as m2.
    destruct m2 as [[[mfrom2 mto2 mchn2] mtid2] mval2]; cbn in *.
    inv H3; inv H4.
    unfold isAddrOf in *.
    destruct (msgAddr_dec _ _).
    - destruct (msgAddr_dec _ _); auto.
      exfalso; inv H1; inv H2.
      rewrite e in e0; auto.
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      specialize (IHmp H1 H2).
      erewrite removeMP_deqMP in IHmp by reflexivity.
      rewrite <-Heqm1 in IHmp.
      assumption.
  Qed.
    
  Lemma FirstMP_FirstMP_removeMP:
    forall mp msg1 msg2,
      mid_addr (msg_id (getMsg msg1)) <> mid_addr (msg_id (getMsg msg2)) ->
      FirstMP mp msg1 ->
      FirstMP mp msg2 ->
      FirstMP (removeMP msg1 mp) msg2.
  Proof.
    unfold FirstMP; intros.
    rewrite firstMP_firstMP' in *.
    induction mp; simpl; intros; [inv H1|].
    inv H1.
    unfold FirstMP in *; intros.
    eapply firstMP'_firstMP'_removeMP; eauto.
    destruct (getMsg msg1) as [[[mfrom1 mto1 mchn1] mtid1] mval1]; cbn in *.
    destruct (getMsg msg2) as [[[mfrom2 mto2 mchn2] mtid2] mval2]; cbn in *.
    auto.
  Qed.

  Corollary FirstMP_Forall_FirstMP_removeMP:
    forall mp msg1 msgs2,
      Forall (fun msg2 => mid_addr (msg_id (getMsg msg1)) <>
                          mid_addr (msg_id (getMsg msg2))) msgs2 ->
      FirstMP mp msg1 ->
      Forall (FirstMP mp) msgs2 ->
      Forall (FirstMP (removeMP msg1 mp)) msgs2.
  Proof.
    induction msgs2; simpl; intros; [constructor|].
    inv H0; inv H2.
    constructor; auto.
    apply FirstMP_FirstMP_removeMP; auto.
  Qed.

  Lemma FirstMP_removeMsgs_enqMP_comm:
    forall msgs mp,
      NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) msgs) ->
      Forall (FirstMP mp) msgs ->
      forall msg,
        removeMsgs msgs (enqMP msg mp) =
        enqMP msg (removeMsgs msgs mp).
  Proof.
    induction msgs; simpl; intros; [reflexivity|].
    inv H0; inv H1.
    rewrite FirstMP_removeMP_enqMP_comm by assumption.
    rewrite <-IHmsgs; [reflexivity|assumption|].
    apply FirstMP_Forall_FirstMP_removeMP; auto.

    clear -H4.
    induction msgs; [constructor|].
    constructor.
    - intro Hx; elim H4; left; auto.
    - eapply IHmsgs.
      intro Hx; elim H4; right; auto.
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
    unfold isAddrOf in *.
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
    unfold isAddrOf in *.
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

  Lemma mmap_removeMsgs:
    forall msgs mp,
      map mmap (removeMsgs msgs mp) =
      removeMsgs (map mmap msgs) (map mmap mp).
  Proof.
    induction msgs; simpl; intros; auto.
    rewrite IHmsgs.
    rewrite mmap_removeMP.
    reflexivity.
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

Section EquivMP.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.
  
  (* Every [Queue] is equal. *)
  Definition EquivMP (m1 m2: MessagePool MsgT) :=
    forall from to chn,
      findMP from to chn m1 = findMP from to chn m2.

End EquivMP.

Section EquivMPFacts.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Lemma EquivMP_refl:
    forall mp, EquivMP mp mp.
  Proof.
    unfold EquivMP; intros; reflexivity.
  Qed.

  Lemma EquivMP_sym:
    forall mp1 mp2, EquivMP mp1 mp2 -> EquivMP mp2 mp1.
  Proof.
    unfold EquivMP; intros; auto.
  Qed.

  Lemma EquivMP_trans:
    forall mp1 mp2 mp3,
      EquivMP mp1 mp2 ->
      EquivMP mp2 mp3 ->
      EquivMP mp1 mp3.
  Proof.
    unfold EquivMP; intros.
    rewrite H0; auto.
  Qed.

  Lemma EquivMP_enqMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msg,
        EquivMP (enqMP msg mp1) (enqMP msg mp2).
  Proof.
    unfold EquivMP; intros.
    do 2 rewrite findMP_enqMP.
    rewrite H0; reflexivity.
  Qed.

  Lemma EquivMP_FirstMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msg,
        FirstMP mp1 msg ->
        FirstMP mp2 msg.
  Proof.
    unfold EquivMP, FirstMP, firstMP; intros.
    rewrite <-H0; assumption.
  Qed.

  Corollary EquivMP_Forall_FirstMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msgs,
        Forall (FirstMP mp1) msgs ->
        Forall (FirstMP mp2) msgs.
  Proof.
    intros.
    eapply Forall_impl; [|eassumption].
    intros.
    eapply EquivMP_FirstMP; eauto.
  Qed.

  Lemma EquivMP_distributeMsgs:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msgs,
        EquivMP (distributeMsgs msgs mp1) (distributeMsgs msgs mp2).
  Proof.
    unfold EquivMP, distributeMsgs; intros.
    do 2 rewrite findMP_app.
    rewrite H0; reflexivity.
  Qed.

  Lemma EquivMP_deqMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall from to chn,
        EquivMP (deqMP from to chn mp1) (deqMP from to chn mp2).
  Proof.
    unfold EquivMP; intros.
    destruct (msgAddr_dec (buildMsgAddr from0 to0 chn0) (buildMsgAddr from to chn)).
    - inv e.
      do 2 rewrite findMP_deqMP_eq.
      rewrite H0; reflexivity.
    - do 2 rewrite findMP_deqMP_neq by assumption.
      auto.
  Qed.

  Lemma EquivMP_removeMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msg,
        EquivMP (removeMP msg mp1) (removeMP msg mp2).
  Proof.
    intros; apply EquivMP_deqMP; auto.
  Qed.

  Lemma EquivMP_removeMsgs:
    forall msgs mp1 mp2,
      EquivMP mp1 mp2 ->
      EquivMP (removeMsgs msgs mp1) (removeMsgs msgs mp2).
  Proof.
    induction msgs; intros; auto.
    simpl.
    apply IHmsgs.
    apply EquivMP_removeMP.
    auto.
  Qed.

  Lemma EquivMP_app:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall mp3 mp4,
        EquivMP mp3 mp4 ->
        EquivMP (mp1 ++ mp3) (mp2 ++ mp4).
  Proof.
    unfold EquivMP; intros.
    do 2 rewrite findMP_app.
    rewrite H0, H1; reflexivity.
  Qed.

  Lemma MsgAddr_NoDup_not_In_findMP:
    forall mp,
      NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) mp) ->
      forall from to chn,
        ~ In (buildMsgAddr from to chn)
          (map (fun msg => mid_addr (msg_id (getMsg msg))) mp) ->
        findMP from to chn mp = nil.
  Proof.
    induction mp; simpl; intros; [reflexivity|].
    inv H0; specialize (IHmp H5); clear H5.
    unfold isAddrOf; destruct (msgAddr_dec _ _); auto.
    exfalso; eauto.
  Qed.
  
  Lemma MsgAddr_NoDup_In_findMP:
    forall mp,
      NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) mp) ->
      forall from to chn,
        In (buildMsgAddr from to chn) (map (fun msg => mid_addr (msg_id (getMsg msg))) mp) ->
        exists msg,
          findMP from to chn mp = [msg] /\
          mid_addr (msg_id (getMsg msg)) = buildMsgAddr from to chn.
  Proof.
    induction mp; simpl; intros; [elim H1|].
    inv H0; specialize (IHmp H5).
    unfold isAddrOf; destruct (msgAddr_dec _ _).
    - exists a; split; auto.
      rewrite MsgAddr_NoDup_not_In_findMP; auto.
      rewrite <-e; assumption.
    - destruct H1; eauto.
      elim n; assumption.
  Qed.

  Lemma EquivMP_MsgAddr_NoDup_EquivList:
    forall mp1 mp2,
      NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) mp1) ->
      NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) mp2) ->
      EquivList mp1 mp2 ->
      EquivMP mp1 mp2.
  Proof.
    unfold EquivMP; intros.

    assert (EquivList (map (fun msg => mid_addr (msg_id (getMsg msg))) mp1)
                      (map (fun msg => mid_addr (msg_id (getMsg msg))) mp2)).
    { destruct H2; split; apply SubList_map; auto. }
    
    destruct (in_dec msgAddr_dec (buildMsgAddr from to chn)
                     (map (fun msg : MsgT => mid_addr (msg_id (getMsg msg))) mp1));
      destruct (in_dec msgAddr_dec (buildMsgAddr from to chn)
                       (map (fun msg : MsgT => mid_addr (msg_id (getMsg msg))) mp2)).
    - apply MsgAddr_NoDup_In_findMP in i; [|assumption]; destruct i as [msg1].
      apply MsgAddr_NoDup_In_findMP in i0; [|assumption]; destruct i0 as [msg2].
      dest; rewrite H4, H5.
      
      pose proof (findMP_SubList from to chn mp1); rewrite H4 in H8.
      specialize (H8 _ (or_introl eq_refl)).
      pose proof (findMP_SubList from to chn mp2); rewrite H5 in H9.
      specialize (H9 _ (or_introl eq_refl)).
      assert (msg1 = msg2).
      { eapply NoDup_map_In; eauto.
        { apply H2; auto. }
        { simpl; rewrite H6, H7; reflexivity. }
      }
      subst; reflexivity.
    - elim n; apply H3; assumption.
    - elim n; apply H3; assumption.
    - do 2 (rewrite MsgAddr_NoDup_not_In_findMP by assumption).
      reflexivity.
  Qed.

End EquivMPFacts.

