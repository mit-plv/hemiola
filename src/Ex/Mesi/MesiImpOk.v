Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Topology Syntax Semantics StepM SemFacts.
Require Import RqRsTopo RqRsUtil.

Require Import Ex.SpecInds Ex.Template Ex.RuleTransformOk.
Require Import Ex.Mesi.Mesi Ex.Mesi.MesiTopo Ex.Mesi.MesiImp Ex.Mesi.MesiSim.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Section MesiImpOk.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).
  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).

  Lemma NoRssChange_refl: forall orq, NoRssChange orq orq.
  Proof.
    intros; red; destruct (orq@[downRq]); auto.
  Qed.

  Lemma immRule_ImplRulesR:
    forall ridx oidx prec trs,
      RssEquivPrec prec ->
      ImplRulesR tr oidx (immRule ridx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      + repeat red in H2; repeat red.
        red in H1; dest; congruence.
      + apply H1; assumption.
      + eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      inv H0; eauto.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H0; red; intros.
      destruct mins; [exfalso; auto|discriminate].
    - red; simpl; unfold TrsMTrs; simpl; intros.
      inv H1; apply NoRssChange_refl.
  Qed.

  Lemma immUpRule_ImplRulesR:
    forall ridx msgId oidx prec trs,
      RssEquivPrec prec ->
      ImplRulesR tr oidx (immUpRule ridx msgId oidx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      + apply H1; assumption.
      + eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H0; eauto; fail.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H0; red; intros.
      destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
      destruct mins; [|discriminate].
      inv H0; dest_in; simpl; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H1; apply NoRssChange_refl; fail.
  Qed.

  Lemma immDownRule_ImplRulesR:
    forall ridx msgId cidx prec trs,
      RssEquivPrec prec ->
      forall oidx,
        ImplRulesR tr oidx (immDownRule ridx msgId cidx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      + repeat red in H4; repeat red.
        red in H1; dest; congruence.
      + apply H1; assumption.
      + eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H0; eauto; fail.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H0; red; intros.
      destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
      destruct mins; [|discriminate].
      inv H0; dest_in; simpl; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H1; apply NoRssChange_refl; fail.
  Qed.

  Lemma rqUpUpRule_ImplRulesR:
    forall ridx msgId cidx oidx prec trs,
      ImplRulesR tr oidx (rqUpUpRule ridx msgId cidx oidx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      repeat red in H3; repeat red.
      red in H0; dest; congruence.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H.
        eexists; split; [reflexivity|].
        red in H0; dest.
        red; repeat split.
        all: unfold addRq; mred.
      + inv H; eauto.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H; red; intros.
      destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
      destruct mins; [|discriminate].
      inv H; dest_in; simpl; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H0; red; unfold addRq; mred.
        apply NoRssChange_refl.
      + inv H0; apply NoRssChange_refl.
  Qed.

  Lemma rqUpUpRuleS_ImplRulesR:
    forall ridx oidx prec trs,
      ImplRulesR tr oidx (rqUpUpRuleS ridx oidx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      repeat red in H3; repeat red.
      red in H0; dest; congruence.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      inv H.
      eexists; split; [reflexivity|].
      red in H0; dest.
      red; repeat split.
      all: unfold addRqS; mred.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H; red; intros.
      destruct mins; [exfalso; auto|discriminate].
    - red; simpl; unfold TrsMTrs; simpl; intros.
      inv H0; red; unfold addRqS; mred.
      apply NoRssChange_refl.
  Qed.

  Lemma rqUpDownRule_ImplRulesR:
    forall ridx msgId cidx oidx prec trs,
      ImplRulesR tr oidx (rqUpDownRule ridx msgId cidx oidx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      repeat red in H3; repeat red.
      apply H0; assumption.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H.
        eexists; split; [reflexivity|].
        red in H0; dest.
        red; repeat split.
        all: try (unfold addRq; mred; fail).
        clear; unfold addRq; mred.
        intros; inv H; simpl.
        eexists; repeat split.
      + inv H; eauto.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H; red; intros.
      destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
      destruct mins; [|discriminate].
      inv H; dest_in; simpl; eauto.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + repeat red in H3.
        inv H0; red; unfold addRq; mred; simpl.
        apply Forall_forall; intros.
        apply in_map_iff in H0; dest; subst; reflexivity.
      + inv H0; apply NoRssChange_refl.
  Qed.

  Lemma rqUpDownRuleS_ImplRulesR:
    forall ridx oidx prec trs,
      ImplRulesR tr oidx (rqUpDownRuleS ridx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      repeat red in H3; repeat red.
      apply H0; assumption.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      inv H.
      eexists; split; [reflexivity|].
      red in H0; dest.
      red; repeat split.
      all: try (unfold addRqS; mred; fail).
      clear; unfold addRqS; mred.
      intros; inv H; simpl.
      eexists; repeat split.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H; red; intros.
      destruct mins; [exfalso; auto|discriminate].
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      repeat red in H2.
      inv H0; red; unfold addRqS; mred; simpl.
      apply Forall_forall; intros.
      apply in_map_iff in H0; dest; subst; reflexivity.
  Qed.

  Lemma rqDownDownRule_ImplRulesR:
    forall ridx msgId oidx prec trs,
      ImplRulesR tr oidx (rqDownDownRule ridx msgId oidx prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      repeat ssplit; try assumption.
      repeat red in H3; repeat red.
      apply H0; assumption.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H.
        eexists; split; [reflexivity|].
        red in H0; dest.
        red; repeat split.
        all: try (unfold addRq; mred; fail).
        clear; unfold addRq; mred.
        intros; inv H; simpl.
        eexists; repeat split.
      + inv H; eauto.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H; red; intros.
      destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
      destruct mins; [|discriminate].
      inv H; dest_in; simpl; eauto.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + repeat red in H3.
        inv H0; red; unfold addRq; mred; simpl.
        apply Forall_forall; intros.
        apply in_map_iff in H0; dest; subst; reflexivity.
      + inv H0; apply NoRssChange_refl.
  Qed.

  Ltac destruct_bind :=
    match goal with
    | |- context [bind ?o ?c] => destruct o
    | H: context [bind ?o ?c] |- _ => destruct o
    end.

  Lemma rsDownDownRule_ImplRulesR:
    forall ridx msgId rqId oidx prec trs,
      RssEquivPrec prec ->
      ImplRulesR tr oidx (rsDownDownRule ridx msgId rqId prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H1; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H3; red; congruence.
      + red in H4; red; congruence.
      + apply H8; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      unfold getUpLockMsg, getUpLockIdxBack in *.
      rewrite <-(proj1 H1).
      do 3 (destruct_bind; simpl in *; [|inv H0; eauto]).
      inv H0.
      eexists; split; [reflexivity|].
      red in H1; dest.
      red; repeat split.
      all: try (unfold removeRq; mred; fail).
    - red; simpl; unfold OPrecAnd; intros; dest.
      admit.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      unfold getUpLockMsg, getUpLockIdxBack in *.
      do 3 (destruct_bind; simpl in *; [|inv H1; apply NoRssChange_refl]).
      inv H1.
      red; unfold removeRq; mred; apply NoRssChange_refl.
  Qed.
  (** [rsDownDownRuleS] as well... *)

  Lemma rsDownRqDownRule_ImplRulesR:
    forall ridx msgId oidx rqId prec trs,
      RssEquivPrec prec ->
      ImplRulesR tr oidx (rsDownRqDownRule ridx msgId oidx rqId prec trs).
  Proof.
    intros; left.
    red; repeat ssplit.
    - red; simpl; unfold OPrecAnd; intros; dest.
      red in H1; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H3; red; congruence.
      + red in H4; red; congruence.
      + apply H8; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      unfold getUpLockMsg, getUpLockIdxBack in *.
      rewrite <-(proj1 H1).
      do 2 (destruct_bind; simpl in *; [|inv H0; eauto]).
      inv H0.
      eexists; split; [reflexivity|].
      red in H1; dest.
      red; repeat split.
      all: try (unfold addRq, removeRq; mred; fail).
      unfold addRq, removeRq; mred.
      intros; inv H3; simpl.
      eexists; repeat split.
    - red; simpl; unfold OPrecAnd; intros; dest.
      admit.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      unfold getUpLockMsg, getUpLockIdxBack in *.
      do 2 (destruct_bind; simpl in *; [|inv H1; apply NoRssChange_refl]).
      inv H1.
      red; unfold addRq, removeRq; mred.
      repeat red in H6; rewrite H6; simpl.
      apply Forall_forall; intros.
      apply in_map_iff in H1; dest; subst; reflexivity.
  Qed.

  (*! -- End of util lemmas *)

  Lemma mesi_imp_ImplRulesR:
    forall obj,
      In obj (sys_objs (MesiImp.impl Htr)) ->
      forall rule,
        In rule (obj_rules obj) ->
        ImplRulesR tr (obj_idx obj) rule.
  Proof.
    intros.
    destruct H; [subst|apply in_app_or in H; destruct H].

    - (** Main memory *)
      simpl in H0.
      unfold memRulesFromChildren in H0.
      apply concat_In in H0; dest.
      apply in_map_iff in H; dest; subst.
      dest_in.
      all: apply immDownRule_ImplRulesR; red; simpl; auto.

    - (** Li cache *)
      apply in_map_iff in H; destruct H as [oidx [? ?]]; subst; simpl in *.
      apply in_app_or in H0; destruct H0.

      + apply concat_In in H; destruct H as [crls [? ?]].
        apply in_map_iff in H; destruct H as [cidx [? ?]]; subst.
        apply Topology.subtreeChildrenIndsOf_parentIdxOf in H2;
          [|apply tree2Topo_WfDTree].
        dest_in.
        all: try (apply immDownRule_ImplRulesR; red; simpl; auto; fail).
        all: try (apply rqUpUpRule_ImplRulesR; fail).
        all: try (apply rqUpDownRule_ImplRulesR; fail).
        all: try (right; right; repeat eexists; assumption).

      + dest_in.
        all: try (apply immRule_ImplRulesR; red; simpl; auto; fail).
        all: try (apply immUpRule_ImplRulesR; red; simpl; auto; fail).
        all: try (apply rqUpUpRuleS_ImplRulesR; fail).
        all: try (apply rqDownDownRule_ImplRulesR; fail).
        all: try (apply rsDownDownRule_ImplRulesR; red; simpl; auto; fail).
        all: try (right; left; repeat eexists; fail).

        * apply rsDownDownRule_ImplRulesR.
          red; unfold getUpLockIdxBackI, getUpLockIdxBack; simpl; intros.
          red in H0; dest.
          congruence.
        * apply rsDownRqDownRule_ImplRulesR.
          red; unfold RsDownRqDownSoundPrec, getUpLockIdxBackI, getUpLockIdxBack; simpl; intros.
          red in H0; dest.
          rewrite <-H0.
          repeat split; assumption.
        * admit. (* [rsDownDownRuleS] *)

    - (** L1 cache *)
      apply in_map_iff in H; destruct H as [oidx [? ?]]; subst.
      dest_in.
      all: try (apply immUpRule_ImplRulesR; red; simpl; auto; fail).
      all: try (apply immDownRule_ImplRulesR; red; simpl; auto; fail).
      all: try (apply rqUpUpRule_ImplRulesR; fail).
      all: try (apply rqUpUpRuleS_ImplRulesR; fail).
      all: try (apply rsDownDownRule_ImplRulesR; red; simpl; auto; fail).
      + admit. (* [rsDownDownRuleS] *)
  Qed.

  Lemma mesi_imp_ImplRules: ImplRules tr (MesiImp.impl Htr).
  Proof.
  Admitted.

  Lemma mesi_SpecRulesIn: SpecRulesIn (MesiImp.impl Htr) (Mesi.impl Htr).
  Proof.
    red.
  Admitted.

  Lemma mesi_imp_mesi_ok:
    (steps step_m) # (steps step_m) |-- (MesiImp.impl Htr) ⊑ (Mesi.impl Htr).
  Proof.
    apply rss_holder_ok with (tr:= tr); try reflexivity.
    - apply mesi_imp_ImplRules.
    - apply mesi_SpecRulesIn.
    - simpl; rewrite !map_app, !map_map, !map_id.
      rewrite app_comm_cons.
      rewrite <-c_li_indices_head_rootOf by assumption.
      reflexivity.
    - apply mesi_GoodRqRsSys.
    - apply mesi_GoodExtRssSys.
  Qed.

  Local Definition spec :=
    @SpecInds.spec (c_l1_indices cifc) (tree2Topo_l1_NoPrefix tr 0).

  Theorem mesi_imp_ok:
    (steps step_m) # (steps step_m) |-- (MesiImp.impl Htr) ⊑ spec.
  Proof.
    eapply refines_trans.
    - apply mesi_imp_mesi_ok.
    - apply MesiSim.mesi_ok.
  Qed.

End MesiImpOk.
