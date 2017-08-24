Require Import Bool List String Peano_dec.
Require Import FunctionalExtensionality.
Require Import FMap Tactics Language.

Set Implicit Arguments.

Lemma forall_filter:
  forall {A} (l: list A) P (f: A -> bool),
    Forall P l -> Forall P (filter f l).
Proof.
  induction l; simpl; intros; auto.
  inv H; destruct (f a); auto.
Qed.

Lemma forall_app:
  forall {A} (l1 l2: list A) P,
    Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction l1; simpl; intros; auto.
  inv H; constructor; auto.
Qed.

Lemma forall_sublist:
  forall {A} P (l1 l2: list A),
    Forall P l1 -> SubList l2 l1 -> Forall P l2.
Proof.
  induction l2; intros; auto.
  apply SubList_cons_inv in H0; dest.
  constructor; auto.
  eapply Forall_forall in H; eauto.
Qed.

Section Label.
  Variable MsgT: Type.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).
  Variable ValT: Type.
  Hypothesis (valT_dec: forall m1 m2: ValT, {m1 = m2} + {m1 <> m2}).
  Variable StateT: Type.

  Local Notation Object := (Object MsgT ValT StateT).
  Local Notation System := (System MsgT ValT StateT).

  Local Notation Label := (Label MsgT ValT).
  Local Notation emptyLabel := (emptyLabel MsgT ValT).
  Local Notation combineLabel := (combineLabel msgT_dec valT_dec).

  Local Notation subtractMsgs := (subtractMsgs msgT_dec valT_dec).
  Local Notation step_sys := (step_sys msgT_dec valT_dec).
  Local Notation step := (step msgT_dec valT_dec).
  Local Notation steps := (steps msgT_dec valT_dec).
  Local Notation Behavior := (Behavior msgT_dec valT_dec).

  Lemma validOuts_nil:
    forall from, ValidOuts (MsgT:= MsgT) (ValT:= ValT) from nil.
  Proof.
    intros; split; constructor.
  Qed.

  Lemma validOuts_subtractMsgs:
    forall from sl l1,
      ValidOuts from l1 -> ValidOuts from (subtractMsgs l1 sl).
  Proof.
  Admitted.

  Lemma step_obj_validLabel:
    forall (obj: Object) st1 mf1 lbl st2 mf2,
      step_obj obj st1 mf1 lbl st2 mf2 -> ValidLabel lbl.
  Proof.
    intros; inv H; cbn.
    - split; [reflexivity|].
      exists O; apply validOuts_nil.
    - split; [reflexivity|].
      rewrite H2; auto.
    - split; [reflexivity|].
      eexists; split.
      + repeat constructor.
        rewrite H0; auto.
      + repeat constructor.
        intro Hx; dest_in.
  Qed.

  Lemma combineLabel_validLabel:
    forall lbl1 lbl2,
      CombinableLabel lbl1 lbl2 ->
      ValidLabel lbl1 -> ValidLabel lbl2 ->
      ValidLabel (combineLabel lbl1 lbl2).
  Proof.
    unfold ValidLabel, combineLabel;
      destruct lbl1 as [ins1 hdl1 outs1], lbl2 as [ins2 hdl2 outs2]; simpl; intros.
    destruct hdl1, hdl2; subst; simpl; split; try reflexivity.
    - exists 0; apply validOuts_nil.
    - dest; apply validOuts_subtractMsgs; auto.
    - dest; apply validOuts_subtractMsgs; auto.
    - auto.
  Qed.

  Lemma step_sys_validLabel:
    forall (sys: System) st1 lbl st2,
      step_sys sys st1 lbl st2 -> ValidLabel lbl.
  Proof.
    induction 1; simpl; intros.
    - eapply step_obj_validLabel; eauto.
    - apply combineLabel_validLabel; auto.
  Qed.

  Lemma step_validLabel:
    forall (sys: System) st1 lbl st2,
      step sys st1 lbl st2 -> ValidLabel lbl.
  Proof.
    intros; inv H.
    eauto using step_sys_validLabel.
  Qed.

  Lemma steps_validLabel:
    forall (sys: System) st1 tr st2,
      steps sys st1 tr st2 -> Forall (@ValidLabel _ _) tr.
  Proof.
    induction 1; auto.
    constructor; auto.
    eauto using step_validLabel.
  Qed.

  Lemma behaviorOf_sublist:
    forall tr: Trace MsgT ValT, SubList (behaviorOf tr) tr.
  Proof.
    induction tr; intros; simpl; [apply SubList_nil|].
    destruct a as [ins hdl outs]; cbn.
    destruct ins; cbn.
    - destruct outs; cbn.
      + apply SubList_cons_right; auto.
      + apply SubList_cons; [left; reflexivity|apply SubList_cons_right; auto].
    - apply SubList_cons; [left; reflexivity|apply SubList_cons_right; auto].
  Qed.

  Lemma behavior_validLabel:
    forall (sys: System) tr,
      Behavior sys tr -> Forall (@ValidLabel _ _) tr.
  Proof.
    intros; inv H.
    apply steps_validLabel in H0.
    eauto using forall_sublist, behaviorOf_sublist.
  Qed.
  
  Lemma combineLabel_emptyLabel_1:
    forall l, ValidLabel l -> combineLabel emptyLabel l = l.
  Proof.
    unfold ValidLabel; destruct l as [ins hdl outs]; cbn; intros.
    destruct hdl; dest; subst; auto.
    f_equal.
    clear H0; induction outs; simpl; auto.
    f_equal; auto.
  Qed.
  
  Lemma combineLabel_emptyLabel_2:
    forall l, ValidLabel l -> combineLabel l emptyLabel = l.
  Proof.
    unfold ValidLabel, combineLabel; destruct l as [ins hdl outs]; cbn; intros.
    destruct hdl; dest; subst; auto.
    - f_equal.
      clear H0; induction outs; simpl; auto.
      f_equal; auto.
    - rewrite app_nil_r; reflexivity.
  Qed.

End Label.
  
Section Singleton.
  Variable MsgT: Type.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).
  Variable ValT: Type.
  Hypothesis (valT_dec: forall m1 m2: ValT, {m1 = m2} + {m1 <> m2}).
  Variable StateT: Type.

  Local Notation Object := (Object MsgT ValT StateT).
  Local Notation System := (System MsgT ValT StateT).

  Local Notation emptyLabel := (emptyLabel MsgT ValT).
  Local Notation step_sys := (step_sys msgT_dec valT_dec).

  Lemma step_obj_msgTo:
    forall (obj: Object) st1 mf1 lbl st2 mf2,
      step_obj obj st1 mf1 lbl st2 mf2 ->
      Forall (fun m => msgTo (msg_id m) = obj_idx obj) (lbl_ins lbl) /\
      Forall (fun m => msgTo (msg_id m) <> obj_idx obj) (lbl_outs lbl).
  Proof.
    intros; inv H.
    - cbn; split; constructor.
    - cbn; split; [constructor|].
      destruct H6.
      eapply Forall_impl; try eassumption.
      simpl; intros; destruct H7; auto.
    - cbn; split; constructor; auto.
  Qed.

  Lemma step_sys_singleton_msgTo:
    forall (obj: Object) s1 lbl s2,
      step_sys [obj] s1 lbl s2 ->
      Forall (fun m => msgTo (msg_id m) = obj_idx obj) (lbl_ins lbl) /\
      Forall (fun m => msgTo (msg_id m) <> obj_idx obj) (lbl_outs lbl).
  Proof.
    induction 1.
    - dest_in; eapply step_obj_msgTo; eauto.
    - destruct lbl1 as [ins1 hdl1 outs1], lbl2 as [ins2 hdl2 outs2].
      unfold combineLabel; simpl in *.
      destruct hdl1, hdl2; simpl.
      + split; constructor.
      + split; [constructor|].
        dest; apply forall_filter; auto.
      + split; [constructor|].
        dest; apply forall_filter; auto.
      + split; [|constructor].
        dest; apply forall_app; auto.
  Qed.

  Lemma step_obj_singleton_no_combs:
    forall (obj: Object) st11 mf11 lbl1 st12 mf12 st21 mf21 lbl2 st22 mf22,
      step_obj obj st11 mf11 lbl1 st12 mf12 ->
      step_obj obj st21 mf21 lbl2 st22 mf22 ->
      (lbl1 = emptyLabel \/ lbl2 = emptyLabel \/ ~ CombinableLabel lbl1 lbl2).
  Proof.
    intros.
    inv H; [tauto| |].
    - inv H0; [tauto|tauto|].
      right; right.
      cbn; intro Hx.
      specialize (Hx emsg (or_introl eq_refl)).
      destruct H7.
      eapply Forall_forall in H0; eauto.
      destruct H0.
      elim H8; auto.
    - inv H0; [tauto| |].
      + right; right.
        cbn; intro Hx.
        specialize (Hx emsg (or_introl eq_refl)).
        destruct H8.
        eapply Forall_forall in H0; eauto.
        destruct H0.
        elim H9; auto.
      + right; right.
        cbn; intro Hx.
        unfold ValidOuts in Hx; dest.
        inv H4; elim H7.
        rewrite H, H1.
        left; reflexivity.
  Qed.

  Lemma step_sys_singleton_no_combs:
    forall (obj: Object) st11 lbl1 st12 st21 lbl2 st22,
      step_sys [obj] st11 lbl1 st12 ->
      step_sys [obj] st21 lbl2 st22 ->
      (lbl1 = emptyLabel \/ lbl2 = emptyLabel \/ ~ CombinableLabel lbl1 lbl2).
  Proof.
    intros.
    pose proof (step_sys_validLabel H).
    pose proof (step_sys_validLabel H0).
    pose proof (step_sys_singleton_msgTo H).
    pose proof (step_sys_singleton_msgTo H0).
    dest.

    unfold ValidLabel in *;
      destruct lbl1 as [ins1 hdl1 outs1], lbl2 as [ins2 hdl2 outs2]; simpl in *.

    destruct hdl1; dest; subst.
    - destruct hdl2; dest; subst; auto.
      destruct ins2; auto.
      right; right; cbn.
      intro Hx; apply SubList_cons_inv in Hx; dest.
      eapply Forall_forall in H6; eauto.
      inv H4; elim H6; auto.
    - destruct ins1; auto.
      destruct hdl2; dest; subst.
      + right; right; cbn.
        intro Hx; apply SubList_cons_inv in Hx; dest.
        eapply Forall_forall in H5; eauto.
        inv H3; elim H5; auto.
      + destruct ins2; auto.
        right; right; cbn.
        inv H3; inv H4.
        unfold ValidOuts; intro Hx; dest; inv H3; elim H13.
        rewrite map_app; simpl; apply in_or_app.
        right; left.
        rewrite H8, H9; reflexivity.
  Qed.
      
  Lemma step_obj_singleton_step_sys:
    forall (obj: Object) st1 mf1 lbl st2 mf2,
      step_obj obj st1 mf1 lbl st2 mf2 ->
      step_sys [obj] {| st_oss := [obj_idx obj <- st1];
                        st_msgs := [obj_idx obj <- mf1] |}
               lbl {| st_oss := [obj_idx obj <- st2];
                      st_msgs := [obj_idx obj <- mf2] |}.
  Proof.
    intros.
    replace [obj_idx obj <- st2] with [obj_idx obj <- st1]+[obj_idx obj <- st2] by meq.
    replace [obj_idx obj <- mf2] with [obj_idx obj <- mf1]+[obj_idx obj <- mf2] by meq.
    eapply SsLift; eauto.
    - left; reflexivity.
    - mred.
    - mred.
  Qed.
      
  Lemma step_sys_singleton_step_obj:
    forall (obj: Object) s1 lbl s2,
      step_sys [obj] s1 lbl s2 ->
      exists st1 mf1 st2 mf2,
        (st_oss s1)@[obj_idx obj] = Some st1 /\
        (st_msgs s1)@[obj_idx obj] = Some mf1 /\
        (st_oss s2)@[obj_idx obj] = Some st2 /\
        (st_msgs s2)@[obj_idx obj] = Some mf2 /\
        step_obj obj st1 mf1 lbl st2 mf2.
  Proof.
    induction 1; simpl; intros; subst.
    - dest_in.
      do 4 eexists; repeat split; eauto; mred.
    - pose proof (step_sys_singleton_no_combs H H0).
      destruct H4 as [|[|]]; subst.
      + unfold DisjointState in H1, H2; dest.
        do 4 eexists; repeat split; try (apply M.Disj_find_union_2; eauto; fail).
        rewrite combineLabel_emptyLabel_1; auto.
        eapply step_obj_validLabel; eauto.
      + unfold DisjointState in H1, H2; dest.
        do 4 eexists; repeat split; try (apply M.Disj_find_union_1; eauto; fail).
        rewrite combineLabel_emptyLabel_2; auto.
        eapply step_obj_validLabel; eauto.
      + elim H4; auto.
  Qed.

End Singleton.

