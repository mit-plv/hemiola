Require Import List FMap Omega.
Require Import Common Topology IndexSupport Syntax Semantics StepM.
Require Import RqRsLang.

Require Import Ex.TopoTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Axiom cheat: forall t, t.
Ltac admit := apply cheat.

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

Section Facts.
  Context `{OStateIfc}.

  Section Lifted.
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
          assert (exists reins,
                     ValidMsgsExtIn sys reins /\ eins = liftMsgs ln reins).
          { admit. }
          destruct H0 as [reins [? ?]]; subst.
                     
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

      Admitted.

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

  End Lifted.

  Theorem refines_compositional:
    forall impl1 spec1,
      Refines (steps step_m) (steps step_m) impl1 spec1 ->
      forall impl2 spec2,
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
  Admitted.

  Theorem refines_replicates:
    forall impl spec,
      Refines (steps step_m) (steps step_m) impl spec ->
      forall n,
        Refines (steps step_m) (steps step_m)
                (repSystem n impl) (repSystem n spec).
  Proof.
    induction n; simpl; intros.
    - apply refines_liftSystem; assumption.
    - apply refines_compositional.
      + apply refines_liftSystem; assumption.
      + assumption.
  Qed.
  
End Facts.

