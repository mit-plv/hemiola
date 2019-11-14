Require Import List FMap Omega.
Require Import Common Topology IndexSupport Syntax Semantics StepM SemFacts.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Lemma extendInds_DisjList:
  forall inds1 inds2,
    DisjList inds1 inds2 ->
    forall ext,
      DisjList (extendInds ext inds1) (extendInds ext inds2).
Proof.
  intros.
  apply (DisjList_spec_1 idx_dec).
  intros idx ?.
  apply in_map_iff in H0; destruct H0 as [oidx1 [? ?]]; subst.
  intro Hx.
  apply in_map_iff in Hx; destruct Hx as [oidx2 [? ?]]; subst.
  inv H0.
  eapply DisjList_In_1; eauto.
Qed.

Lemma extendInds_DisjList_inv:
  forall inds1 inds2 ext,
    DisjList (extendInds ext inds1) (extendInds ext inds2) ->
    DisjList inds1 inds2.
Proof.
  intros.
  apply (DisjList_spec_1 idx_dec).
  intros idx ?; intro Hx.
  eapply DisjList_In_1 with (a:= idx~>ext); [eassumption|..].
  - apply in_map; assumption.
  - apply in_map; assumption.
Qed.

Lemma behaviorOf_cons_inv:
  forall {LabelT} `{HasLabel LabelT} (ll: list LabelT) lbl rll,
    behaviorOf ll = lbl :: rll ->
    exists hll tll,
      hll ++ tll = ll /\
      behaviorOf hll = [lbl] /\
      behaviorOf tll = rll.
Proof.
  induction ll as [|rlbl ll]; simpl; intros; [discriminate|].
  destruct (getLabel rlbl) as [lbl'|] eqn:Hlbl; simpl in *.
  - inv H0.
    exists [rlbl], ll; repeat split.
    simpl; rewrite Hlbl; reflexivity.
  - specialize (IHll _ _ H0).
    destruct IHll as [hll [tll ?]]; dest; subst.
    exists (rlbl :: hll), tll; repeat split.
    simpl; rewrite Hlbl; simpl; assumption.
Qed.

Section Lift.
  Context `{OStateIfc}.
  Variable (ln: nat).

  Definition liftMsgs {MsgT} (msgs: list (Id MsgT)): list (Id MsgT) :=
    map (fun idm => ((fst idm)~>ln, snd idm)) msgs.

  Definition unliftMsgs {MsgT} (msgs: list (Id MsgT)): list (Id MsgT) :=
    map (fun idm => (idxTl (fst idm), snd idm)) msgs.

  Definition liftRulePrec (prec: OPrec): OPrec :=
    fun ost orq mins =>
      prec ost orq (unliftMsgs mins).

  Definition liftRuleTrs (trs: OTrs): OTrs :=
    fun ost orq mins =>
      let (osr, mouts) := trs ost orq (unliftMsgs mins) in
      (osr, liftMsgs mouts).

  Definition liftRule (rule: Rule): Rule :=
    {| rule_idx := rule.(rule_idx); (* Don't need to lift it since it's local. *)
       rule_precond := liftRulePrec rule.(rule_precond);
       rule_trs := liftRuleTrs rule.(rule_trs) |}.

  Lemma lift_obj_rules_valid:
    forall rules,
      NoDup (map rule_idx rules) ->
      NoDup (map rule_idx (map liftRule rules)).
  Proof.
    intros; rewrite map_trans; assumption.
  Qed.

  Definition liftObject (obj: Object): Object :=
    {| obj_idx := obj.(obj_idx)~>ln;
       obj_rules := map liftRule obj.(obj_rules);
       obj_rules_valid := lift_obj_rules_valid _ obj.(obj_rules_valid) |}.

  Definition liftFMap {A} (m: M.t A): M.t A :=
    M.fold (fun k v m => m +[k~>ln <- v]) m (M.empty _).

  Lemma lift_sys_oinds_valid:
    forall objs,
      NoDup (map obj_idx objs) ->
      NoDup (map obj_idx (map liftObject objs)).
  Proof.
    intros.
    apply extendIdx_NoDup with (ext:= ln) in H0.
    unfold extendInds in H0; rewrite map_trans in H0.
    rewrite map_trans; assumption.
  Qed.

  Lemma lift_sys_msg_inds_valid:
    forall minds merqs merss,
      NoDup (minds ++ merqs ++ merss) ->
      NoDup ((extendInds ln minds)
               ++ (extendInds ln merqs)
               ++ (extendInds ln merss)).
  Proof.
    intros.
    unfold extendInds.
    do 2 rewrite <-map_app.
    apply extendIdx_NoDup.
    assumption.
  Qed.

  Definition liftSystem (sys: System): System :=
    {| sys_objs := map liftObject sys.(sys_objs);
       sys_oinds_valid := lift_sys_oinds_valid _ sys.(sys_oinds_valid);
       sys_minds := extendInds ln sys.(sys_minds);
       sys_merqs := extendInds ln sys.(sys_merqs);
       sys_merss := extendInds ln sys.(sys_merss);
       sys_msg_inds_valid := lift_sys_msg_inds_valid _ _ _ sys.(sys_msg_inds_valid);
       sys_oss_inits := liftFMap sys.(sys_oss_inits);
       sys_orqs_inits := liftFMap sys.(sys_orqs_inits) |}.

End Lift.

Section Replicate.
  Context `{OStateIfc}.

  Definition mergeSystem (sys1 sys2: System)
             (HoidxOk: NoDup (map obj_idx (sys_objs sys1 ++ sys_objs sys2)))
             (HmidxOk: NoDup ((sys_minds sys1 ++ sys_minds sys2)
                                ++ (sys_merqs sys1 ++ sys_merqs sys2)
                                ++ (sys_merss sys1 ++ sys_merss sys2))): System :=
    {| sys_objs := sys1.(sys_objs) ++ sys2.(sys_objs);
       sys_oinds_valid := HoidxOk;
       sys_minds := sys1.(sys_minds) ++ sys2.(sys_minds);
       sys_merqs := sys1.(sys_merqs) ++ sys2.(sys_merqs);
       sys_merss := sys1.(sys_merss) ++ sys2.(sys_merss);
       sys_msg_inds_valid := HmidxOk;
       sys_oss_inits := M.union sys1.(sys_oss_inits) sys2.(sys_oss_inits);
       sys_orqs_inits := M.union sys1.(sys_orqs_inits) sys2.(sys_orqs_inits) |}.

  Fixpoint repSystem (n: nat) (osys: System): System :=
    match n with
    | O => liftSystem O osys
    | S n' => mergeSystem (liftSystem n osys) (repSystem n' osys) (cheat _) (cheat _)
    end.

End Replicate.

Section ValidState.
  Context `{OStateIfc}.
  Variable (sys: System).

  Definition ValidState (st: MState) :=
    M.KeysSubset (bst_oss st) (map (@obj_idx _) (sys_objs sys)) /\
    M.KeysSubset (bst_orqs st) (map (@obj_idx _) (sys_objs sys)) /\
    M.KeysSubset (bst_msgs st) (sys_minds sys ++ sys_merqs sys ++ sys_merss sys).

  Definition InitStateValid := ValidState (initsOf sys).

  Lemma enqMP_msgs_valid:
    forall (msgs: MessagePool Msg),
      M.KeysSubset msgs (sys_minds sys ++ sys_merqs sys ++ sys_merss sys) ->
      forall midx msg,
        In midx (sys_minds sys ++ sys_merqs sys ++ sys_merss sys) ->
        M.KeysSubset (enqMP midx msg msgs) (sys_minds sys ++ sys_merqs sys ++ sys_merss sys).
  Proof.
    intros; unfold enqMP.
    apply M.KeysSubset_add; auto.
  Qed.

  Lemma enqMsgs_msgs_valid:
    forall (nmsgs: list (Id Msg)) (msgs: MessagePool Msg),
      M.KeysSubset msgs (sys_minds sys ++ sys_merqs sys ++ sys_merss sys) ->
      SubList (idsOf nmsgs) (sys_minds sys ++ sys_merqs sys ++ sys_merss sys) ->
      M.KeysSubset (enqMsgs nmsgs msgs) (sys_minds sys ++ sys_merqs sys ++ sys_merss sys).
  Proof.
    induction nmsgs as [|[midx msg] nmsgs]; simpl; intros; auto.
    apply SubList_cons_inv in H1; dest.
    apply IHnmsgs; auto.
    apply enqMP_msgs_valid; auto.
  Qed.

  Lemma deqMP_msgs_valid:
    forall (msgs: MessagePool Msg),
      M.KeysSubset msgs (sys_minds sys ++ sys_merqs sys ++ sys_merss sys) ->
      forall midx,
        M.KeysSubset (deqMP midx msgs) (sys_minds sys ++ sys_merqs sys ++ sys_merss sys).
  Proof.
    intros; unfold deqMP.
    unfold findQ.
    destruct (msgs@[midx]) as [q|] eqn:Hq; simpl; [|assumption].
    destruct q; [assumption|].
    apply M.KeysSubset_add; auto.
    apply H0; findeq.
  Qed.

  Lemma deqMsgs_msgs_valid:
    forall (rminds: list IdxT) (msgs: MessagePool Msg),
      M.KeysSubset msgs (sys_minds sys ++ sys_merqs sys ++ sys_merss sys) ->
      M.KeysSubset (deqMsgs rminds msgs) (sys_minds sys ++ sys_merqs sys ++ sys_merss sys).
  Proof.
    induction rminds as [|rmidx rminds]; simpl; intros; auto.
    apply IHrminds; auto.
    apply deqMP_msgs_valid; auto.
  Qed.

  Lemma step_ValidState:
    forall st1,
      ValidState st1 ->
      forall lbl st2,
        step_m sys st1 lbl st2 -> ValidState st2.
  Proof.
    intros; inv H1; auto.
    - red in H0; simpl in H0; dest.
      red; simpl; repeat ssplit; try assumption.
      apply enqMsgs_msgs_valid; auto.
      destruct H3.
      eapply SubList_trans; [eassumption|].
      apply SubList_app_2, SubList_app_1, SubList_refl.
    - red in H0; simpl in H0; dest.
      red; simpl; repeat ssplit; try assumption.
      apply deqMsgs_msgs_valid; auto.
    - red in H0; simpl in H0; dest.
      red; simpl; repeat ssplit.
      + apply M.KeysSubset_add; auto; apply in_map; assumption.
      + apply M.KeysSubset_add; auto; apply in_map; assumption.
      + destruct H11.
        apply enqMsgs_msgs_valid.
        * apply deqMsgs_msgs_valid; auto.
        * eapply SubList_trans; [eassumption|].
          apply SubList_app_3.
          { apply SubList_app_1, SubList_refl. }
          { apply SubList_app_2, SubList_app_2, SubList_refl. }
  Qed.

  Lemma steps_ValidState:
    forall st1,
      ValidState st1 ->
      forall hst st2,
        steps step_m sys st1 hst st2 -> ValidState st2.
  Proof.
    induction 2; simpl; intros; auto.
    eapply step_ValidState; [|eassumption].
    auto.
  Qed.

  Lemma reachable_state_valid:
    InitStateValid ->
    forall st,
      Reachable (steps step_m) sys st ->
      ValidState st.
  Proof.
    unfold Reachable; intros.
    destruct H1 as [hst ?].
    eapply steps_ValidState; eauto.
  Qed.

End ValidState.

Section Facts.
  Context `{OStateIfc}.

  Section Lift.
    Variable ln: nat.

    Section FMap.
      Context {A: Type}.

      Lemma transpose_neqkey_lift_add:
        M.F.P.transpose_neqkey eq (fun k v (m: M.t A) => m +[k~>ln <- v]).
      Proof.
        red; intros.
        assert (k~>ln <> k'~>ln) by (intro Hx; inv Hx; auto).
        meq.
      Qed.

      Local Hint Resolve transpose_neqkey_lift_add.

      Lemma liftFMap_add:
        forall k v (m: M.t A),
          liftFMap ln (m +[k <- v]) = (liftFMap ln m) +[k~>ln <- v].
      Proof.
        intros.
        revert k v.
        M.mind m; intros; [reflexivity|].
        M.cmp k k0.
        - rewrite M.add_idempotent.
          rewrite (H0 k0 v).
          rewrite M.add_idempotent.
          auto.
        - unfold liftFMap in H0.
          rewrite M.add_comm by auto.
          unfold liftFMap.
          rewrite M.F.P.fold_add; auto.
          + rewrite H0.
            rewrite M.F.P.fold_add with (eqA:= eq); auto.
          + findeq.
      Qed.

      Lemma liftFMap_find:
        forall k (m: M.t A),
          (liftFMap ln m)@[k~>ln] = m@[k].
      Proof.
        intros.
        M.mind m; [reflexivity|].
        rewrite liftFMap_add.
        M.cmp k k0.
        - findeq.
        - assert (k~>ln <> k0~>ln) by (intro Hx; inv Hx; auto).
          findeq.
      Qed.

    End FMap.

    Section Messages.
      Context {MsgT: Type}.

      Lemma liftMsgs_unliftMsgs:
        forall (msgs: list (Id MsgT)),
          unliftMsgs (liftMsgs ln msgs) = msgs.
      Proof.
        induction msgs as [|msg msgs]; simpl; intros; auto.
        destruct msg; simpl.
        rewrite IHmsgs; reflexivity.
      Qed.

      Lemma extendInds_idsOf_liftMsgs:
        forall (msgs: list (Id MsgT)),
          map (extendIdx ln) (idsOf msgs) = idsOf (liftMsgs ln msgs).
      Proof.
        unfold idsOf, liftMsgs; intros.
        do 2 rewrite map_trans.
        reflexivity.
      Qed.

      Lemma liftFMap_enqMP:
        forall midx msg (mp: MessagePool MsgT),
          liftFMap ln (enqMP midx msg mp) =
          enqMP midx~>ln msg (liftFMap ln mp).
      Proof.
        unfold enqMP, findQ; intros.
        rewrite liftFMap_add, liftFMap_find.
        reflexivity.
      Qed.

      Lemma liftFMap_enqMsgs:
        forall msgs (mp: MessagePool MsgT),
          liftFMap ln (enqMsgs msgs mp) =
          enqMsgs (liftMsgs ln msgs) (liftFMap ln mp).
      Proof.
        induction msgs as [|[midx msg] msgs]; simpl; intros; auto.
        rewrite <-liftFMap_enqMP; auto.
      Qed.

      Lemma liftFMap_deqMP:
        forall midx (mp: MessagePool MsgT),
          liftFMap ln (deqMP midx mp) =
          deqMP midx~>ln (liftFMap ln mp).
      Proof.
        unfold deqMP, findQ; intros.
        rewrite liftFMap_find.
        destruct mp@[midx]; simpl.
        - destruct l; [reflexivity|].
          apply liftFMap_add.
        - reflexivity.
      Qed.

      Lemma liftFMap_deqMsgs:
        forall minds (mp: MessagePool MsgT),
          liftFMap ln (deqMsgs minds mp) =
          deqMsgs (extendInds ln minds) (liftFMap ln mp).
      Proof.
        induction minds as [|midx minds]; simpl; intros; auto.
        rewrite <-liftFMap_deqMP; auto.
      Qed.

      Lemma liftFMap_FirstMP:
        forall midx msg (mp: MessagePool MsgT),
          FirstMP mp midx msg ->
          FirstMP (liftFMap ln mp) midx~>ln msg.
      Proof.
        unfold FirstMP, firstMP, findQ; intros.
        rewrite liftFMap_find.
        assumption.
      Qed.

      Lemma liftFMap_FirstMPI_Forall:
        forall msgs (mp: MessagePool MsgT),
          Forall (FirstMPI mp) msgs ->
          Forall (FirstMPI (liftFMap ln mp)) (liftMsgs ln msgs).
      Proof.
        intros.
        apply Forall_forall; intros midx ?.
        apply in_map_iff in H1; destruct H1 as [[rmidx msg] ?].
        simpl in H1; dest; subst.
        rewrite Forall_forall in H0; specialize (H0 _ H2).
        apply liftFMap_FirstMP; assumption.
      Qed.

      Lemma liftFMap_FirstMP_inv:
        forall midx msg (mp: MessagePool MsgT),
          FirstMP (liftFMap ln mp) midx~>ln msg ->
          FirstMP mp midx msg.
      Proof.
        unfold FirstMP, firstMP, findQ; intros.
        rewrite liftFMap_find in H0.
        assumption.
      Qed.

      Lemma liftFMap_FirstMPI_Forall_inv:
        forall msgs (mp: MessagePool MsgT),
          Forall (FirstMPI (liftFMap ln mp)) (liftMsgs ln msgs) ->
          Forall (FirstMPI mp) msgs.
      Proof.
        intros.
        apply Forall_forall; intros midx ?.
        apply liftFMap_FirstMP_inv.
        rewrite Forall_forall in H0.
        apply (H0 ((idOf midx)~>ln, valOf midx)).
        eapply in_map in H1; exact H1.
      Qed.

    End Messages.

    Definition liftMLabel (lbl: MLabel): MLabel :=
      match lbl with
      | RlblEmpty _ => RlblEmpty _
      | RlblIns ins => RlblIns (liftMsgs ln ins)
      | RlblOuts outs => RlblOuts (liftMsgs ln outs)
      | RlblInt oidx ridx rins routs =>
        RlblInt oidx~>ln ridx (liftMsgs ln rins) (liftMsgs ln routs)
      end.

    Definition unliftMLabel (lbl: MLabel): MLabel :=
      match lbl with
      | RlblEmpty _ => RlblEmpty _
      | RlblIns ins => RlblIns (unliftMsgs ins)
      | RlblOuts outs => RlblOuts (unliftMsgs outs)
      | RlblInt oidx ridx rins routs =>
        RlblInt (idxTl oidx) ridx (unliftMsgs rins) (unliftMsgs routs)
      end.

    Definition liftLabel (lbl: Label): Label :=
      match lbl with
      | LblIns ins => LblIns (liftMsgs ln ins)
      | LblOuts outs => LblOuts (liftMsgs ln outs)
      end.

    Definition liftMState (st: MState): MState :=
      {| bst_oss := liftFMap ln st.(bst_oss);
         bst_orqs := liftFMap ln st.(bst_orqs);
         bst_msgs := liftFMap ln st.(bst_msgs) |}.

    Section System.
      Variable sys: System.

      Lemma step_lifted:
        forall st1 lbl st2,
          step_m sys st1 lbl st2 ->
          step_m (liftSystem ln sys) (liftMState st1) (liftMLabel lbl) (liftMState st2).
      Proof.
        intros; inv H0.
        - constructor.
        - econstructor.
          + intro Hx; elim H1.
            apply map_eq_nil in Hx; assumption.
          + destruct H2; split.
            * apply SubList_map with (f:= extendIdx ln) in H0.
              rewrite extendInds_idsOf_liftMsgs in H0.
              assumption.
            * red; rewrite <-extendInds_idsOf_liftMsgs.
              apply extendIdx_NoDup; assumption.
          + reflexivity.
          + unfold liftMState; simpl.
            rewrite liftFMap_enqMsgs.
            reflexivity.

        - econstructor.
          + intro Hx; elim H1.
            apply map_eq_nil in Hx; assumption.
          + apply liftFMap_FirstMPI_Forall; eassumption.
          + destruct H3; split.
            * apply SubList_map with (f:= extendIdx ln) in H0.
              rewrite extendInds_idsOf_liftMsgs in H0.
              assumption.
            * red; rewrite <-extendInds_idsOf_liftMsgs.
              apply extendIdx_NoDup; assumption.
          + reflexivity.
          + unfold liftMState; simpl.
            rewrite liftFMap_deqMsgs.
            rewrite <-extendInds_idsOf_liftMsgs.
            reflexivity.

        - change (rule_idx rule) with (rule_idx (liftRule ln rule)).
          econstructor.
          + apply in_map; eassumption.
          + apply in_map; assumption.
          + reflexivity.
          + instantiate (1:= os).
            instantiate (1:= liftFMap ln oss).
            rewrite liftFMap_find; assumption.
          + instantiate (1:= porq).
            instantiate (1:= liftFMap ln orqs).
            rewrite liftFMap_find; assumption.
          + instantiate (1:= liftFMap ln msgs).
            apply liftFMap_FirstMPI_Forall; assumption.
          + destruct H7; split.
            * simpl; rewrite <-extendInds_idsOf_liftMsgs.
              unfold extendInds; rewrite <-map_app.
              apply SubList_map; assumption.
            * red; rewrite <-extendInds_idsOf_liftMsgs.
              apply extendIdx_NoDup; assumption.
          + simpl; red.
            rewrite liftMsgs_unliftMsgs; assumption.
          + instantiate (1:= norq).
            instantiate (1:= pos).
            simpl; unfold liftRuleTrs.
            rewrite liftMsgs_unliftMsgs.
            rewrite H9; reflexivity.
          + destruct H10; split.
            * simpl; rewrite <-extendInds_idsOf_liftMsgs.
              unfold extendInds; rewrite <-map_app.
              apply SubList_map; assumption.
            * red; rewrite <-extendInds_idsOf_liftMsgs.
              apply extendIdx_NoDup; assumption.
          + do 2 rewrite <-extendInds_idsOf_liftMsgs.
            apply extendInds_DisjList; assumption.
          + reflexivity.
          + unfold liftMState; simpl.
            do 2 rewrite liftFMap_add.
            rewrite liftFMap_enqMsgs.
            rewrite liftFMap_deqMsgs.
            unfold extendInds; rewrite extendInds_idsOf_liftMsgs.
            reflexivity.
      Qed.

      Lemma steps_lifted:
        forall st1 hst st2,
          steps step_m sys st1 hst st2 ->
          steps step_m (liftSystem ln sys)
                (liftMState st1) (map liftMLabel hst) (liftMState st2).
      Proof.
        induction 1; simpl; intros; [constructor|].
        econstructor; [eassumption|].
        apply step_lifted; assumption.
      Qed.

      Lemma liftLabel_liftMLabel:
        forall ll,
          map liftLabel (behaviorOf ll) = behaviorOf (map liftMLabel ll).
      Proof.
        induction ll as [|lbl ll]; simpl; [reflexivity|].
        destruct lbl; simpl; auto.
        - unfold liftMsgs, imap, liftI.
          do 2 rewrite map_trans; simpl.
          rewrite IHll; reflexivity.
        - unfold liftMsgs, imap, liftI.
          do 2 rewrite map_trans; simpl.
          rewrite IHll; reflexivity.
      Qed.
        
      Lemma Behavior_lifted:
        forall tr,
          Behavior (steps step_m) sys tr ->
          Behavior (steps step_m) (liftSystem ln sys) (map liftLabel tr).
      Proof.
        intros.
        inv H0.
        econstructor.
        - instantiate (1:= liftMState st).
          instantiate (1:= map liftMLabel ll).
          apply steps_lifted in H1; assumption.
        - apply liftLabel_liftMLabel.
      Qed.

      Lemma SubList_unlifted:
        forall (l1: list IdxT) l2,
          SubList l1 (extendInds ln l2) ->
          exists rl1, SubList rl1 l2 /\ l1 = extendInds ln rl1.
      Proof.
        induction l1; simpl; intros.
        - exists nil; split; auto.
          apply SubList_nil.
        - apply SubList_cons_inv in H0; dest.
          apply in_map_iff in H0; destruct H0 as [ra [? ?]]; subst.
          specialize (IHl1 _ H1).
          destruct IHl1 as [rl1 [? ?]]; subst.
          exists (ra :: rl1); split; auto.
          apply SubList_cons; auto.
      Qed.

      Lemma idsOf_unlifted:
        forall {A} (l1: list (Id A)) l2,
          idsOf l1 = extendInds ln l2 ->
          exists rl1, idsOf rl1 = l2 /\ l1 = liftMsgs ln rl1.
      Proof.
        induction l1; simpl; intros.
        - destruct l2; [|discriminate].
          exists nil; split; auto.
        - destruct l2; [discriminate|].
          inv H0.
          specialize (IHl1 _ H3); destruct IHl1 as [rl1 [? ?]]; subst.
          exists ((i, snd a) :: rl1).
          split; auto.
          destruct a; simpl in *; subst; reflexivity.
      Qed.

      Lemma ValidMsgsExtIn_unlifted:
        forall {MsgT} (eins: list (Id MsgT)),
          ValidMsgsExtIn (liftSystem ln sys) eins ->
          exists reins, ValidMsgsExtIn sys reins /\ eins = liftMsgs ln reins.
      Proof.
        intros.
        destruct H0; simpl in H0.
        red in H1.
        apply SubList_unlifted in H0.
        destruct H0 as [rl [? ?]].
        rewrite H2 in H1.
        apply idsOf_unlifted in H2.
        destruct H2 as [reins [? ?]]; subst.
        exists reins; split; [|reflexivity].
        split; auto.
        eapply extendIdx_NoDup_inv; eauto.
      Qed.

      Lemma ValidMsgsExtOut_unlifted:
        forall {MsgT} (eouts: list (Id MsgT)),
          ValidMsgsExtOut (liftSystem ln sys) eouts ->
          exists reouts,
            ValidMsgsExtOut sys reouts /\ eouts = liftMsgs ln reouts.
      Proof.
        intros.
        destruct H0; simpl in H0.
        red in H1.
        apply SubList_unlifted in H0.
        destruct H0 as [rl [? ?]].
        rewrite H2 in H1.
        apply idsOf_unlifted in H2.
        destruct H2 as [reouts [? ?]]; subst.
        exists reouts; split; [|reflexivity].
        split; auto.
        eapply extendIdx_NoDup_inv; eauto.
      Qed.

      Lemma obj_rule_unlifted:
        forall sys obj rule,
          In obj (sys_objs (liftSystem ln sys)) ->
          In rule (obj_rules obj) ->
          exists robj rrule,
            In robj (sys_objs sys) /\
            obj = liftObject ln robj /\
            In rrule (obj_rules robj) /\
            rule = liftRule ln rrule.
      Proof.
        intros.
        apply in_map_iff in H0.
        destruct H0 as [robj [? ?]]; subst.
        apply in_map_iff in H1.
        destruct H1 as [rrule [? ?]]; subst.
        exists robj, rrule; auto.
      Qed.

      Lemma ValidMsgsIn_unlifted:
        forall {MsgT} (ins: list (Id MsgT)),
          ValidMsgsIn (liftSystem ln sys) ins ->
          exists rins, ValidMsgsIn sys rins /\ ins = liftMsgs ln rins.
      Proof.
        intros.
        destruct H0; simpl in H0.
        red in H1.
        unfold extendInds in H0; rewrite <-map_app in H0.
        apply SubList_unlifted in H0.
        destruct H0 as [rl [? ?]].
        rewrite H2 in H1.
        apply idsOf_unlifted in H2.
        destruct H2 as [rins [? ?]]; subst.
        exists rins; split; [|reflexivity].
        split; auto.
        eapply extendIdx_NoDup_inv; eauto.
      Qed.

      Lemma ValidMsgsOut_unlifted:
        forall {MsgT} (outs: list (Id MsgT)),
          ValidMsgsOut (liftSystem ln sys) outs ->
          exists routs, ValidMsgsOut sys routs /\ outs = liftMsgs ln routs.
      Proof.
        intros.
        destruct H0; simpl in H0.
        red in H1.
        unfold extendInds in H0; rewrite <-map_app in H0.
        apply SubList_unlifted in H0.
        destruct H0 as [rl [? ?]].
        rewrite H2 in H1.
        apply idsOf_unlifted in H2.
        destruct H2 as [routs [? ?]]; subst.
        exists routs; split; [|reflexivity].
        split; auto.
        eapply extendIdx_NoDup_inv; eauto.
      Qed.

      Lemma rule_prec_unlifted:
        forall rule ost orq ins,
          liftRulePrec (rule_precond rule) ost orq (liftMsgs ln ins) ->
          rule_precond rule ost orq ins.
      Proof.
        intros.
        red in H0.
        rewrite liftMsgs_unliftMsgs in H0.
        assumption.
      Qed.

      Lemma rule_trs_unlifted:
        forall rule post porq ins nost norq outs,
          liftRuleTrs ln (rule_trs rule) post porq (liftMsgs ln ins) =
          (nost, norq, liftMsgs ln outs) ->
          rule_trs rule post porq ins = (nost, norq, outs).
      Proof.
        intros.
        unfold liftRuleTrs in H0.
        rewrite liftMsgs_unliftMsgs in H0.
        destruct (rule_trs rule post porq ins) as [[nost' norq'] outs'].
        inv H0.
        apply f_equal with (f:= unliftMsgs) in H4.
        do 2 rewrite liftMsgs_unliftMsgs in H4.
        subst; reflexivity.
      Qed.

      Lemma step_unlifted:
        forall st1 llbl lst2,
          step_m (liftSystem ln sys) (liftMState st1) llbl lst2 ->
          exists lbl st2,
            step_m sys st1 lbl st2 /\
            lst2 = liftMState st2 /\ llbl = liftMLabel lbl.
      Proof.
        intros.
        remember (liftMState st1) as lst1.
        inv H0.
        - do 2 eexists; repeat split.
          + constructor.
          + reflexivity.

        - destruct st1 as [oss1 orqs1 msgs1]; inv H3.
          apply ValidMsgsExtIn_unlifted in H2.
          destruct H2 as [reins [? ?]]; subst.
                     
          do 2 eexists; repeat split.
          + econstructor 2.
            * instantiate (1:= reins).
              intro Hx; subst; auto.
            * assumption.
            * reflexivity.
            * reflexivity.
          + unfold liftMState; simpl.
            rewrite liftFMap_enqMsgs; reflexivity.
          + reflexivity.

        - destruct st1 as [oss1 orqs1 msgs1]; inv H4.
          apply ValidMsgsExtOut_unlifted in H3.
          destruct H3 as [reouts [? ?]]; subst.
          apply liftFMap_FirstMPI_Forall_inv in H2.
                     
          do 2 eexists; repeat split.
          + econstructor 3.
            * instantiate (1:= reouts).
              intro Hx; subst; auto.
            * eassumption.
            * assumption.
            * reflexivity.
            * reflexivity.
          + unfold liftMState; simpl.
            rewrite liftFMap_deqMsgs.
            rewrite <-extendInds_idsOf_liftMsgs.
            reflexivity.
          + reflexivity.

        - destruct st1 as [oss1 orqs1 msgs1]; inv H12.
          eapply obj_rule_unlifted in H1; [|eassumption].
          clear H2; destruct H1 as [robj [rrule ?]]; dest; subst.
          simpl in H4; rewrite liftFMap_find in H4.
          simpl in H5; rewrite liftFMap_find in H5.
          apply ValidMsgsIn_unlifted in H7.
          destruct H7 as [rins [? ?]]; subst.
          apply liftFMap_FirstMPI_Forall_inv in H6.
          apply rule_prec_unlifted in H8.
          apply ValidMsgsOut_unlifted in H10.
          destruct H10 as [routs [? ?]]; subst.
          apply rule_trs_unlifted in H9.
          do 2 rewrite <-extendInds_idsOf_liftMsgs in H11.
          apply extendInds_DisjList_inv in H11.

          do 2 eexists; repeat split.
          + econstructor 4; eauto.
          + unfold liftMState; simpl.
            do 2 rewrite liftFMap_add.
            rewrite liftFMap_enqMsgs, liftFMap_deqMsgs.
            rewrite <-extendInds_idsOf_liftMsgs.
            reflexivity.
          + reflexivity.

      Qed.

      Lemma steps_unlifted:
        forall st1 lhst lst1 lst2,
          lst1 = liftMState st1 ->
          steps step_m (liftSystem ln sys) lst1 lhst lst2 ->
          exists hst st2,
            steps step_m sys st1 hst st2 /\
            lst2 = liftMState st2 /\ lhst = map liftMLabel hst.
      Proof.
        induction 2; intros; subst.
        - do 2 eexists; repeat split.
          + constructor.
          + reflexivity.
        - specialize (IHsteps eq_refl).
          destruct IHsteps as [hst [rst2 ?]]; dest; subst.
          apply step_unlifted in H2.
          destruct H2 as [rlbl [st2 ?]]; dest; subst.
          eexists (_ :: _), _; repeat split.
          econstructor; eauto.
      Qed.

      Lemma liftSystem_initsOf:
        initsOf (liftSystem ln sys) = liftMState (initsOf sys).
      Proof.
        reflexivity.
      Qed.

      Lemma Behavior_unlifted:
        forall tr,
          Behavior (steps step_m) (liftSystem ln sys) tr ->
          exists utr,
            Behavior (steps step_m) sys utr /\ tr = map liftLabel utr.
      Proof.
        intros.
        inv H0.
        rewrite liftSystem_initsOf in H1.
        eapply steps_unlifted in H1; [|reflexivity].
        destruct H1 as [hst [st2 ?]]; dest; subst.
        eexists; split.
        - econstructor; [eassumption|reflexivity].
        - apply eq_sym, liftLabel_liftMLabel.
      Qed.

    End System.

    Lemma refines_liftSystem:
      forall impl spec,
        Refines (steps step_m) (steps step_m) impl spec ->
        Refines (steps step_m) (steps step_m)
                (liftSystem ln impl) (liftSystem ln spec).
    Proof.
      unfold Refines; intros.
      apply Behavior_unlifted in H1.
      destruct H1 as [utr [? ?]]; subst.
      apply Behavior_lifted; auto.
    Qed.

  End Lift.

  Section Merge.

    Definition mergeMState (st1 st2: MState): MState :=
      {| bst_oss := M.union (bst_oss st1) (bst_oss st2);
         bst_orqs := M.union (bst_orqs st1) (bst_orqs st2);
         bst_msgs := M.union (bst_msgs st1) (bst_msgs st2) |}.

    Inductive HistoryMerged: list MLabel -> list MLabel -> list MLabel -> Prop :=
    | NilMerged: HistoryMerged nil nil nil
    | HLeftMerged:
        forall hst1 hst2 hst,
          HistoryMerged hst1 hst2 hst ->
          forall lbl,
            HistoryMerged (lbl :: hst1) hst2 (lbl :: hst)
    | HRightMerged:
        forall hst1 hst2 hst,
          HistoryMerged hst1 hst2 hst ->
          forall lbl,
            HistoryMerged hst1 (lbl :: hst2) (lbl :: hst).

    Lemma HistoryMerged_left:
      forall ll, HistoryMerged ll nil ll.
    Proof.
      induction ll; [constructor|].
      constructor; assumption.
    Qed.

    Lemma HistoryMerged_right:
      forall ll, HistoryMerged nil ll ll.
    Proof.
      induction ll; [constructor|].
      constructor; assumption.
    Qed.

    Lemma HistoryMerged_basic_1:
      forall ll1 ll2, HistoryMerged ll1 ll2 (ll1 ++ ll2).
    Proof.
      induction ll1; simpl; intros.
      - apply HistoryMerged_right.
      - constructor; auto.
    Qed.

    Lemma HistoryMerged_basic_2:
      forall ll1 ll2, HistoryMerged ll1 ll2 (ll2 ++ ll1).
    Proof.
      induction ll2; simpl; intros.
      - apply HistoryMerged_left.
      - constructor; auto.
    Qed.

    Lemma HistoryMerged_app_1:
      forall ll1 ll2 ll,
        HistoryMerged ll1 ll2 ll ->
        forall nll,
          HistoryMerged (nll ++ ll1) ll2 (nll ++ ll).
    Proof.
      induction nll; simpl; intros; [assumption|].
      constructor; auto.
    Qed.

    Lemma HistoryMerged_app_2:
      forall ll1 ll2 ll,
        HistoryMerged ll1 ll2 ll ->
        forall nll,
          HistoryMerged ll1 (nll ++ ll2) (nll ++ ll).
    Proof.
      induction nll; simpl; intros; [assumption|].
      constructor; auto.
    Qed.

  End Merge.

  Section Compose.
    Variables (sys1 sys2: System).
    Hypotheses
      (Hvi1: InitStateValid sys1)
      (Hvi2: InitStateValid sys2)
      (HoidxOk: NoDup (map obj_idx (sys_objs sys1 ++ sys_objs sys2)))
      (HmidxOk: NoDup ((sys_minds sys1 ++ sys_minds sys2)
                         ++ (sys_merqs sys1 ++ sys_merqs sys2)
                         ++ (sys_merss sys1 ++ sys_merss sys2))).

    Lemma mergeMState_init:
      initsOf (mergeSystem sys1 sys2 HoidxOk HmidxOk) =
      mergeMState (initsOf sys1) (initsOf sys2).
    Proof.
      reflexivity.
    Qed.

    Section DisjMP.
      Variables (msgs1 msgs2: MessagePool Msg).

      Local Notation chns1 := (sys_minds sys1 ++ sys_merqs sys1 ++ sys_merss sys1).
      Local Notation chns2 := (sys_minds sys2 ++ sys_merqs sys2 ++ sys_merss sys2).
      
      Hypotheses (Hks1: M.KeysSubset msgs1 chns1)
                 (Hks2: M.KeysSubset msgs2 chns2).

      Lemma chns_disj: DisjList chns1 chns2.
      Proof.
      Admitted.

      Lemma disj_mp_findQ_1:
        forall midx,
          In midx chns1 ->
          findQ midx msgs1 = findQ midx (M.union msgs1 msgs2).
      Proof.
      Admitted.

      Lemma disj_mp_findQ_2:
        forall midx,
          In midx chns2 ->
          findQ midx msgs2 = findQ midx (M.union msgs1 msgs2).
      Proof.
      Admitted.

      Lemma disj_mp_FirstMP_1:
        forall midx msg,
          In midx chns1 ->
          FirstMP msgs1 midx msg <->
          FirstMP (M.union msgs1 msgs2) midx msg.
      Proof.
        unfold FirstMP, firstMP; intros.
        rewrite <-disj_mp_findQ_1 by assumption.
        split; intros; assumption.
      Qed.

      Lemma disj_mp_FirstMP_2:
        forall midx msg,
          In midx chns2 ->
          FirstMP msgs2 midx msg <->
          FirstMP (M.union msgs1 msgs2) midx msg.
      Proof.
        unfold FirstMP, firstMP; intros.
        rewrite <-disj_mp_findQ_2 by assumption.
        split; intros; assumption.
      Qed.

      Lemma disj_mp_enqMP_1:
        forall midx msg,
          In midx chns1 ->
          M.union (enqMP midx msg msgs1) msgs2 = enqMP midx msg (M.union msgs1 msgs2).
      Proof.
        unfold enqMP; intros.
        rewrite M.union_add.
        rewrite disj_mp_findQ_1 by assumption.
        reflexivity.
      Qed.

      Lemma disj_mp_enqMP_2:
        forall midx msg,
          In midx chns2 ->
          M.union msgs1 (enqMP midx msg msgs2) = enqMP midx msg (M.union msgs1 msgs2).
      Proof.
        unfold enqMP; intros.
        rewrite M.union_comm
          by (eapply M.DisjList_KeysSubset_Disj; [apply chns_disj|assumption|];
              apply M.KeysSubset_add; auto).
        rewrite M.union_comm with (m1:= msgs1) (m2:= msgs2) at 2
          by (eapply M.DisjList_KeysSubset_Disj; [apply chns_disj|eassumption..]).
        rewrite M.union_add.
        rewrite disj_mp_findQ_2 by assumption.
        reflexivity.
      Qed.

      Lemma disj_mp_enqMsgs_1:
        forall nmsgs,
          SubList (idsOf nmsgs) chns1 ->
          M.union (enqMsgs nmsgs msgs1) msgs2 = enqMsgs nmsgs (M.union msgs1 msgs2).
      Proof.
      Admitted.

      Lemma disj_mp_enqMsgs_2:
        forall nmsgs,
          SubList (idsOf nmsgs) chns2 ->
          M.union msgs1 (enqMsgs nmsgs msgs2) = enqMsgs nmsgs (M.union msgs1 msgs2).
      Proof.
      Admitted.

      Lemma disj_mp_deqMP_1:
        forall midx,
          In midx chns1 ->
          M.union (deqMP midx msgs1) msgs2 = deqMP midx (M.union msgs1 msgs2).
      Proof.
        unfold deqMP; intros.
        rewrite <-disj_mp_findQ_1 by assumption.
        destruct (findQ midx msgs1); [reflexivity|].
        rewrite M.union_add.
        reflexivity.
      Qed.

      Lemma disj_mp_deqMP_2:
        forall midx,
          In midx chns2 ->
          M.union msgs1 (deqMP midx msgs2) = deqMP midx (M.union msgs1 msgs2).
      Proof.
        unfold deqMP; intros.
        rewrite <-disj_mp_findQ_2 by assumption.
        destruct (findQ midx msgs2); [reflexivity|].
        rewrite M.union_comm
          by (eapply M.DisjList_KeysSubset_Disj; [apply chns_disj|assumption|];
              apply M.KeysSubset_add; auto).
        rewrite M.union_add.
        rewrite M.union_comm
          by (eapply M.DisjList_KeysSubset_Disj;
              [apply DisjList_comm, chns_disj|assumption..]).
        reflexivity.
      Qed.

      Lemma disj_mp_deqMsgs_1:
        forall rminds,
          SubList rminds chns1 ->
          M.union (deqMsgs rminds msgs1) msgs2 = deqMsgs rminds (M.union msgs1 msgs2).
      Proof.
      Admitted.

      Lemma disj_mp_deqMsgs_2:
        forall rminds,
          SubList rminds chns2 ->
          M.union msgs1 (deqMsgs rminds msgs2) = deqMsgs rminds (M.union msgs1 msgs2).
      Proof.
      Admitted.

    End DisjMP.

    Lemma step_mergeSystem_lifted_1:
      forall st11 lbl st12,
        Reachable (steps step_m) sys1 st11 ->
        step_m sys1 st11 lbl st12 ->
        forall st2,
          Reachable (steps step_m) sys2 st2 ->
          step_m (mergeSystem sys1 sys2 HoidxOk HmidxOk)
                 (mergeMState st11 st2) lbl (mergeMState st12 st2).
    Proof.
      intros.
      apply reachable_state_valid in H0; [|assumption].
      red in H0; dest.
      apply reachable_state_valid in H2; [|assumption].
      red in H2; dest.
      inv H1; [constructor|..].

      - destruct st2 as [oss2 orqs2 msgs2].
        eapply SmIns; [assumption| |reflexivity|].
        + destruct H8.
          split; [|eassumption].
          simpl; apply SubList_app_1; assumption.
        + unfold mergeMState; simpl.
          destruct H8.
          f_equal.
          apply disj_mp_enqMsgs_1; try assumption.
          eapply SubList_trans; [eassumption|].
          apply SubList_app_2, SubList_app_1, SubList_refl.

      - destruct st2 as [oss2 orqs2 msgs2].
        eapply SmOuts; [assumption| | |reflexivity|].
        + simpl.
          apply Forall_forall; intros.
          rewrite Forall_forall in H8; specialize (H8 _ H1).
          eapply disj_mp_FirstMP_1 with (msgs1:= msgs) (msgs2:= msgs2); eauto.
          destruct H9.
          do 2 (apply in_or_app; right).
          apply H9; apply in_map; assumption.
        + destruct H9.
          split; [|eassumption].
          simpl; apply SubList_app_1; assumption.
        + unfold mergeMState; simpl.
          destruct H9.
          f_equal.
          apply disj_mp_deqMsgs_1; try assumption.
          eapply SubList_trans; [eassumption|].
          do 2 apply SubList_app_2; apply SubList_refl.

      - destruct st2 as [oss2 orqs2 msgs2].
        eapply SmInt.
        + apply in_or_app; left; eassumption.
        + assumption.
        + reflexivity.
        + instantiate (1:= os).
          instantiate (1:= M.union oss oss2).
          apply M.Disj_find_union_1.
          * eapply M.DisjList_KeysSubset_Disj.
            { rewrite map_app in HoidxOk.
              eapply (DisjList_NoDup idx_dec); [apply HoidxOk|..]; eassumption.
            }
            { assumption. }
            { assumption. }
          * assumption.
        + instantiate (1:= porq).
          instantiate (1:= M.union orqs orqs2).
          apply M.Disj_find_union_1.
          * eapply M.DisjList_KeysSubset_Disj.
            { rewrite map_app in HoidxOk.
              eapply (DisjList_NoDup idx_dec); [apply HoidxOk|..]; eassumption.
            }
            { assumption. }
            { assumption. }
          * assumption.

        + instantiate (1:= M.union msgs msgs2).
          apply Forall_forall; intros.
          rewrite Forall_forall in H12; specialize (H12 _ H1).
          eapply disj_mp_FirstMP_1 with (msgs1:= msgs) (msgs2:= msgs2); eauto.
          destruct H13.
          apply in_map with (f:= idOf) in H1.
          apply H9 in H1.
          apply in_app_or in H1; destruct H1.
          * apply in_or_app; left; assumption.
          * apply in_or_app; right; apply in_or_app; left; assumption.

        + destruct H13.
          split; [|assumption].
          simpl; eapply SubList_trans; [eassumption|].
          apply SubList_app_3.
          * apply SubList_app_1, SubList_app_1, SubList_refl.
          * apply SubList_app_2, SubList_app_1, SubList_refl.

        + assumption.
        + eassumption.
        + destruct H16.
          split; [|assumption].
          simpl; eapply SubList_trans; [eassumption|].
          apply SubList_app_3.
          * apply SubList_app_1, SubList_app_1, SubList_refl.
          * apply SubList_app_2, SubList_app_1, SubList_refl.

        + assumption.
        + reflexivity.
        + unfold mergeMState; simpl.
          do 2 rewrite M.union_add; f_equal.
          rewrite disj_mp_enqMsgs_1; try assumption.
          * f_equal.
            apply disj_mp_deqMsgs_1; try assumption.
            destruct H13.
            simpl; eapply SubList_trans; [eassumption|].
            apply SubList_app_3.
            { apply SubList_app_1, SubList_refl. }
            { apply SubList_app_2, SubList_app_1, SubList_refl. }
          * apply deqMsgs_msgs_valid; assumption.
          * destruct H16.
            eapply SubList_trans; [eassumption|].
            apply SubList_app_3.
            { apply SubList_app_1, SubList_refl. }
            { apply SubList_app_2, SubList_app_2, SubList_refl. }
    Qed.

    Lemma step_mergeSystem_lifted_2:
      forall st21 lbl st22,
        Reachable (steps step_m) sys2 st21 ->
        step_m sys2 st21 lbl st22 ->
        forall st1,
          Reachable (steps step_m) sys1 st1 ->
          step_m (mergeSystem sys1 sys2 HoidxOk HmidxOk)
                 (mergeMState st1 st21) lbl (mergeMState st1 st22).
    Proof.
      intros.
      apply reachable_state_valid in H0; [|assumption].
      red in H0; dest.
      apply reachable_state_valid in H2; [|assumption].
      red in H2; dest.
      inv H1; [constructor|..].

      - destruct st1 as [oss1 orqs1 msgs1].
        eapply SmIns; [assumption| |reflexivity|].
        + destruct H8.
          split; [|eassumption].
          simpl; apply SubList_app_2; assumption.
        + unfold mergeMState; simpl.
          destruct H8.
          f_equal.
          apply disj_mp_enqMsgs_2; try assumption.
          eapply SubList_trans; [eassumption|].
          apply SubList_app_2, SubList_app_1, SubList_refl.

      - destruct st1 as [oss1 orqs1 msgs1].
        eapply SmOuts; [assumption| | |reflexivity|].
        + simpl.
          apply Forall_forall; intros.
          rewrite Forall_forall in H8; specialize (H8 _ H1).
          eapply disj_mp_FirstMP_2 with (msgs1:= msgs1) (msgs2:= msgs); eauto.
          destruct H9.
          do 2 (apply in_or_app; right).
          apply H9; apply in_map; assumption.
        + destruct H9.
          split; [|eassumption].
          simpl; apply SubList_app_2; assumption.
        + unfold mergeMState; simpl.
          destruct H9.
          f_equal.
          apply disj_mp_deqMsgs_2; try assumption.
          eapply SubList_trans; [eassumption|].
          do 2 apply SubList_app_2; apply SubList_refl.

      - destruct st1 as [oss1 orqs1 msgs1].
        eapply SmInt.
        + apply in_or_app; right; eassumption.
        + assumption.
        + reflexivity.
        + instantiate (1:= os).
          instantiate (1:= M.union oss1 oss).
          apply M.Disj_find_union_2.
          * eapply M.DisjList_KeysSubset_Disj.
            { rewrite map_app in HoidxOk.
              eapply (DisjList_NoDup idx_dec); [apply HoidxOk|..]; eassumption.
            }
            { assumption. }
            { assumption. }
          * assumption.
        + instantiate (1:= porq).
          instantiate (1:= M.union orqs1 orqs).
          apply M.Disj_find_union_2.
          * eapply M.DisjList_KeysSubset_Disj.
            { rewrite map_app in HoidxOk.
              eapply (DisjList_NoDup idx_dec); [apply HoidxOk|..]; eassumption.
            }
            { assumption. }
            { assumption. }
          * assumption.

        + instantiate (1:= M.union msgs1 msgs).
          apply Forall_forall; intros.
          rewrite Forall_forall in H12; specialize (H12 _ H1).
          eapply disj_mp_FirstMP_2 with (msgs1:= msgs1) (msgs2:= msgs); eauto.
          destruct H13.
          apply in_map with (f:= idOf) in H1.
          apply H9 in H1.
          apply in_app_or in H1; destruct H1.
          * apply in_or_app; left; assumption.
          * apply in_or_app; right; apply in_or_app; left; assumption.

        + destruct H13.
          split; [|assumption].
          simpl; eapply SubList_trans; [eassumption|].
          apply SubList_app_3.
          * apply SubList_app_1, SubList_app_2, SubList_refl.
          * apply SubList_app_2, SubList_app_2, SubList_refl.

        + assumption.
        + eassumption.
        + destruct H16.
          split; [|assumption].
          simpl; eapply SubList_trans; [eassumption|].
          apply SubList_app_3.
          * apply SubList_app_1, SubList_app_2, SubList_refl.
          * apply SubList_app_2, SubList_app_2, SubList_refl.

        + assumption.
        + reflexivity.
        + unfold mergeMState; simpl.
          f_equal; [admit|admit|].
          rewrite disj_mp_enqMsgs_2; try assumption.
          * f_equal.
            apply disj_mp_deqMsgs_2; try assumption.
            destruct H13.
            simpl; eapply SubList_trans; [eassumption|].
            apply SubList_app_3.
            { apply SubList_app_1, SubList_refl. }
            { apply SubList_app_2, SubList_app_1, SubList_refl. }
          * apply deqMsgs_msgs_valid; assumption.
          * destruct H16.
            eapply SubList_trans; [eassumption|].
            apply SubList_app_3.
            { apply SubList_app_1, SubList_refl. }
            { apply SubList_app_2, SubList_app_2, SubList_refl. }
    Qed.

    Lemma steps_composed:
      forall ll1 ll2 ll,
        HistoryMerged ll1 ll2 ll ->
        forall st11 st12,
          Reachable (steps step_m) sys1 st11 ->
          steps step_m sys1 st11 ll1 st12 ->
          forall st21 st22,
            Reachable (steps step_m) sys2 st21 ->
            steps step_m sys2 st21 ll2 st22 ->
            steps step_m (mergeSystem sys1 sys2 HoidxOk HmidxOk)
                  (mergeMState st11 st21) ll (mergeMState st12 st22).
    Proof.
      induction 1; simpl; intros.
      - inv H1; inv H3; constructor.
      - inv H2.
        specialize (IHHistoryMerged _ _ H1 H8 _ _ H3 H4).
        econstructor; [eassumption|].
        apply step_mergeSystem_lifted_1.
        + eapply reachable_steps; eauto.
        + assumption.
        + eapply reachable_steps; eauto.
      - inv H4.
        specialize (IHHistoryMerged _ _ H1 H2 _ _ H3 H8).
        econstructor; [eassumption|].
        apply step_mergeSystem_lifted_2.
        + eapply reachable_steps; eauto.
        + assumption.
        + eapply reachable_steps; eauto.
    Qed.

  End Compose.

  Section Split.
    Variables (sys1 sys2: System).
    Hypotheses
      (HoidxOk: NoDup (map obj_idx (sys_objs sys1 ++ sys_objs sys2)))
      (HmidxOk: NoDup ((sys_minds sys1 ++ sys_minds sys2)
                         ++ (sys_merqs sys1 ++ sys_merqs sys2)
                         ++ (sys_merss sys1 ++ sys_merss sys2))).

    Lemma step_mergeSystem_unlifted:
      forall st11 st21 lbl st2,
        step_m (mergeSystem sys1 sys2 HoidxOk HmidxOk)
               (mergeMState st11 st21) lbl st2 ->
        (exists st12, step_m sys1 st11 lbl st12 /\
                      mergeMState st12 st21 = st2) \/
        (exists st22, step_m sys2 st21 lbl st22 /\
                      mergeMState st11 st22 = st2).
    Proof.
    Admitted.

    Lemma steps_split:
      forall st1 ll st2,
        steps step_m (mergeSystem sys1 sys2 HoidxOk HmidxOk) st1 ll st2 ->
        forall st11 st21,
          mergeMState st11 st21 = st1 ->
          exists ll1 st12 ll2 st22,
            steps step_m sys1 st11 ll1 st12 /\
            steps step_m sys2 st21 ll2 st22 /\
            mergeMState st12 st22 = st2 /\
            HistoryMerged ll1 ll2 ll.
    Proof.
      induction 1; simpl; intros.
      - eexists nil, _, nil, _.
        repeat split; try constructor; assumption.
      - specialize (IHsteps _ _ H2).
        destruct IHsteps as [ll1 [st12 [ll2 [st22 ?]]]]; dest.
        subst st2; apply step_mergeSystem_unlifted in H1.
        destruct H1.
        + destruct H1 as [st13 [? ?]].
          do 4 eexists; repeat split.
          * eapply StepsCons; eassumption.
          * eassumption.
          * assumption.
          * constructor; assumption.
        + destruct H1 as [st23 [? ?]].
          do 4 eexists; repeat split.
          * eassumption.
          * eapply StepsCons; eassumption.
          * assumption.
          * constructor; assumption.
    Qed.          

  End Split.

  Lemma HistoryMerged_behaviorOf_compositional:
    forall hst1 hst2 hst,
      HistoryMerged hst1 hst2 hst ->
      forall rhst1 rhst2,
        behaviorOf hst1 = behaviorOf rhst1 ->
        behaviorOf hst2 = behaviorOf rhst2 ->
        exists rhst,
          HistoryMerged rhst1 rhst2 rhst /\
          behaviorOf hst = behaviorOf rhst.
  Proof.
    induction 1; simpl; intros.
    - exists (rhst1 ++ rhst2); split.
      + apply HistoryMerged_basic_1.
      + rewrite behaviorOf_app.
        rewrite <-H0, <-H1; reflexivity.

    - destruct (rToLabel lbl) as [lbl1|]; simpl in *; [|eauto; fail].
      apply eq_sym, behaviorOf_cons_inv in H1.
      destruct H1 as [hll1 [tll1 ?]]; dest; subst.
      apply eq_sym in H4.
      specialize (IHHistoryMerged _ _ H4 H2).
      destruct IHHistoryMerged as [prhst [? ?]].
      exists (hll1 ++ prhst); split.
      + apply HistoryMerged_app_1; assumption.
      + rewrite behaviorOf_app, H3.
        simpl; congruence.

    - destruct (rToLabel lbl) as [lbl2|]; simpl in *; [|eauto; fail].
      apply eq_sym, behaviorOf_cons_inv in H2.
      destruct H2 as [hll2 [tll2 ?]]; dest; subst.
      apply eq_sym in H4.
      specialize (IHHistoryMerged _ _ H1 H4).
      destruct IHHistoryMerged as [prhst [? ?]].
      exists (hll2 ++ prhst); split.
      + apply HistoryMerged_app_2; assumption.
      + rewrite behaviorOf_app, H3.
        simpl; congruence.
  Qed.

  Theorem refines_compositional:
    forall impl1 spec1 (Hspec1: InitStateValid spec1),
      Refines (steps step_m) (steps step_m) impl1 spec1 ->
      forall impl2 spec2 (Hspec2: InitStateValid spec2),
        Refines (steps step_m) (steps step_m) impl2 spec2 ->
        forall (HoidxOkI: NoDup (map obj_idx (sys_objs impl1 ++ sys_objs impl2)))
               (HmidxOkI: NoDup ((sys_minds impl1 ++ sys_minds impl2)
                                   ++ (sys_merqs impl1 ++ sys_merqs impl2)
                                   ++ (sys_merss impl1 ++ sys_merss impl2)))
               (HoidxOkS: NoDup (map obj_idx (sys_objs spec1 ++ sys_objs spec2)))
               (HmidxOkS: NoDup ((sys_minds spec1 ++ sys_minds spec2)
                                   ++ (sys_merqs spec1 ++ sys_merqs spec2)
                                   ++ (sys_merss spec1 ++ sys_merss spec2))),
          Refines (steps step_m) (steps step_m)
                  (mergeSystem impl1 impl2 HoidxOkI HmidxOkI)
                  (mergeSystem spec1 spec2 HoidxOkS HmidxOkS).
  Proof.
    intros.
    red; intros.
    inv H2.
    eapply steps_split in H3; [|apply eq_sym, mergeMState_init].
    destruct H3 as [ll1 [st12 [ll2 [st22 ?]]]]; dest.
    assert (Behavior (steps step_m) impl1 (behaviorOf ll1)).
    { econstructor; [eassumption|reflexivity]. }
    specialize (H0 _ H6).
    assert (Behavior (steps step_m) impl2 (behaviorOf ll2)).
    { econstructor; [eassumption|reflexivity]. }
    specialize (H1 _ H7).
    inv H0; rename ll0 into rll1.
    inv H1; rename ll0 into rll2.

    eapply HistoryMerged_behaviorOf_compositional in H5; [|eassumption..].
    destruct H5 as [rll [? ?]]; rewrite H5.

    econstructor.
    - rewrite mergeMState_init.
      eapply steps_composed; try eassumption.
      all: apply reachable_init.
    - reflexivity.
  Qed.

  Theorem refines_replicates:
    forall impl spec (Hspec: InitStateValid spec),
      Refines (steps step_m) (steps step_m) impl spec ->
      forall n,
        Refines (steps step_m) (steps step_m)
                (repSystem n impl) (repSystem n spec).
  Proof.
    induction n; simpl; intros.
    - apply refines_liftSystem; assumption.
    - apply refines_compositional.
      + admit.
      + apply refines_liftSystem; assumption.
      + admit.
      + assumption.
  Qed.
  
End Facts.

