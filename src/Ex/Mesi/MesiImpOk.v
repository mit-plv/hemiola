Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Topology Syntax Semantics StepM SemFacts.
Require Import RqRsTopo RqRsUtil.

Require Import Ex.SpecInds Ex.Template Ex.RuleTransform Ex.RuleTransformOk.
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

  Lemma UpLockDownTo_refl:
    forall orq1 orq2,
      orq1@[upRq] = orq2@[upRq] ->
      UpLockDownTo orq1 orq2.
  Proof.
    unfold UpLockDownTo; intros.
    rewrite H.
    destruct orq2@[upRq]; auto.
  Qed.
  Local Hint Extern 4 (UpLockDownTo _ _) => (apply UpLockDownTo_refl; auto).

  Lemma NoRssChange_refl:
    forall orq1 orq2,
      orq1@[downRq] = orq2@[downRq] ->
      NoRssChange orq1 orq2.
  Proof.
    unfold NoRssChange; intros.
    rewrite H.
    destruct (orq2@[downRq]); auto.
  Qed.
  Local Hint Extern 4 (NoRssChange _ _) => (apply NoRssChange_refl; auto).

  Definition RssORqEquivPrec (prec: OPrec) :=
    forall ost orq1 mins,
      prec ost orq1 mins ->
      forall orq2, RssORqEquiv orq1 orq2 -> prec ost orq2 mins.

  Lemma immRule_ImplRulesR:
    forall ridx oidx prec trs,
      RssORqEquivPrec prec ->
      ImplRulesR tr oidx (immRule ridx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H0; red; intros.
        destruct mins; [exfalso; auto|discriminate].
      + intros; repeat ssplit; try eassumption.
        * repeat red in H1; repeat red.
          red in H4; dest; congruence.
        * apply H4; assumption.
        * eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      inv H1; repeat split; auto.
      intros; eauto.
  Qed.

  Lemma immUpRule_ImplRulesR:
    forall ridx msgId oidx prec trs,
      RssORqEquivPrec prec ->
      ImplRulesR tr oidx (immUpRule ridx msgId oidx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H0; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H0; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        * apply H5; assumption.
        * eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H1; eauto; fail.
  Qed.

  Lemma immDownRule_ImplRulesR:
    forall ridx msgId cidx prec trs,
      RssORqEquivPrec prec ->
      forall oidx,
        ImplRulesR tr oidx (immDownRule ridx msgId cidx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H0; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H0; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        * repeat red in H3; repeat red.
          red in H6; dest; congruence.
        * apply H6; assumption.
        * eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H1; eauto; fail.
  Qed.

  Lemma rqUpUpRule_ImplRulesR:
    forall ridx msgId cidx oidx prec trs,
      ImplRulesR tr oidx (rqUpUpRule ridx msgId cidx oidx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        red in H4; dest; congruence.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H0; repeat split.
        * repeat red in H3; red.
          unfold addRq; mred; simpl; eauto.
        * red; unfold addRq; mred.
          apply NoRssChange_refl; auto.
        * intros; eexists; split; [reflexivity|].
          red in H0; dest.
          red; repeat split.
          all: unfold addRq; mred.
      + inv H0; eauto.
  Qed.

  Lemma rqUpUpRuleS_ImplRulesR:
    forall ridx oidx prec trs,
      ImplRulesR tr oidx (rqUpUpRuleS ridx oidx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins; [exfalso; auto|discriminate].
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        red in H3; dest; congruence.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      inv H0; repeat split.
      + repeat red in H2; red.
        unfold addRqS; mred; simpl; eauto.
      + red; unfold addRqS; mred.
        apply NoRssChange_refl; auto.
      + intros; eexists; split; [reflexivity|].
        red in H0; dest.
        red; repeat split.
        all: unfold addRqS; mred.
  Qed.

  Lemma rqUpDownRule_ImplRulesR:
    forall ridx msgId cidx oidx prec trs,
      ImplRulesR tr oidx (rqUpDownRule ridx msgId cidx oidx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        apply H4; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H0; repeat split.
        * red; unfold addRq; mred.
          apply UpLockDownTo_refl; reflexivity.
        * repeat red in H3.
          red; unfold addRq; mred; simpl.
          apply Forall_forall; intros.
          apply in_map_iff in H0; dest; subst; reflexivity.
        * intros; eexists; split; [reflexivity|].
          red in H0; dest.
          red; repeat split.
          all: unfold addRq; mred.
          eauto.
      + inv H0; eauto.
  Qed.

  Lemma rqUpDownRuleS_ImplRulesR:
    forall ridx oidx prec trs,
      ImplRulesR tr oidx (rqUpDownRuleS ridx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins; [exfalso; auto|discriminate].
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        apply H3; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      inv H0; repeat split.
      + red; unfold addRqS; mred.
        apply UpLockDownTo_refl; reflexivity.
      + repeat red in H2.
        red; unfold addRqS; mred; simpl.
        apply Forall_forall; intros.
        apply in_map_iff in H0; dest; subst; reflexivity.
      + intros; eexists; split; [reflexivity|].
        red in H0; dest.
        red; repeat split.
        all: unfold addRqS; mred.
        eauto.
  Qed.

  Lemma rqDownDownRule_ImplRulesR:
    forall ridx msgId oidx prec trs,
      ImplRulesR tr oidx (rqDownDownRule ridx msgId oidx prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        apply H4; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H0; repeat split.
        * red; unfold addRq; mred.
          apply UpLockDownTo_refl; reflexivity.
        * repeat red in H3.
          red; unfold addRq; mred; simpl.
          apply Forall_forall; intros.
          apply in_map_iff in H0; dest; subst; reflexivity.
        * intros; eexists; split; [reflexivity|].
          red in H0; dest.
          red; repeat split.
          all: unfold addRq; mred.
          eauto.
      + inv H0; eauto.
  Qed.

  Ltac destruct_bind :=
    match goal with
    | |- context [bind ?o ?c] => destruct o
    | H: context [bind ?o ?c] |- _ => destruct o
    end.

  Lemma rsDownDownRule_ImplRulesR:
    forall ridx msgId rqId oidx prec trs,
      RssORqEquivPrec prec ->
      ImplRulesR tr oidx (rsDownDownRule ridx msgId rqId prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split; [right; assumption|].
      intros; red in H7; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H2; red; congruence.
      + red in H3; red; congruence.
      + apply H8; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      repeat ssplit.
      + do 3 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold removeRq; mred.
      + do 3 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold removeRq; mred.
        apply NoRssChange_refl; reflexivity.
      + intros; unfold getUpLockMsg, getUpLockIdxBack in *.
        rewrite <-(proj1 H8).
        do 3 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1.
        eexists; split; [reflexivity|].
        red in H8; dest.
        red; repeat split.
        all: try (unfold removeRq; mred; fail).
  Qed.

  Lemma rsDownDownRuleS_ImplRulesR:
    forall ridx msgId oidx prec trs,
      RssORqEquivPrec prec ->
      ImplRulesR tr oidx (rsDownDownRuleS ridx msgId prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split; [right; assumption|].
      intros; red in H6; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H2; red; congruence.
      + apply H7; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      repeat ssplit.
      + destruct_bind; simpl in *; [|inv H1; eauto].
        inv H1; red; unfold removeRq; mred.
      + destruct_bind; simpl in *; [|inv H1; eauto].
        inv H1; red; unfold removeRq; mred.
        apply NoRssChange_refl; reflexivity.
      + destruct_bind; simpl in *; [|inv H1; eauto].
        inv H1.
        eexists; split; [reflexivity|].
        red in H1; dest.
        red; repeat split.
        all: try (unfold removeRq; mred; fail).
  Qed.

  Lemma rsDownRqDownRule_ImplRulesR:
    forall ridx msgId oidx rqId prec trs,
      RssORqEquivPrec prec ->
      ImplRulesR tr oidx (rsDownRqDownRule ridx msgId oidx rqId prec trs).
  Proof.
    intros; left.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split; [right; assumption|].
      intros; red in H7; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H2; red; congruence.
      + red in H3; red; congruence.
      + apply H8; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      repeat ssplit.
      + do 2 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold addRq, removeRq; mred.
      + do 2 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold addRq, removeRq; mred.
        repeat red in H6; rewrite H6.
        simpl; apply Forall_forall; intros.
        apply in_map_iff in H1; dest; subst; reflexivity.
      + intros; unfold getUpLockMsg, getUpLockIdxBack in *.
        rewrite <-(proj1 H8).
        do 2 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1.
        eexists; split; [reflexivity|].
        red in H8; dest.
        red; repeat split.
        all: try (unfold addRq, removeRq; mred; fail).
        unfold addRq, removeRq; mred.
        intros; inv H10; simpl; eauto.
  Qed.

  (*! -- End of util lemmas *)

  Lemma mesi_imp_ImplRules: ImplRules tr (MesiImp.impl Htr).
  Proof.
    red; intros.
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
        all: try (apply rsDownDownRuleS_ImplRulesR; red; simpl; auto; fail).
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

    - (** L1 cache *)
      apply in_map_iff in H; destruct H as [oidx [? ?]]; subst.
      dest_in.
      all: try (apply immUpRule_ImplRulesR; red; simpl; auto; fail).
      all: try (apply immDownRule_ImplRulesR; red; simpl; auto; fail).
      all: try (apply rqUpUpRule_ImplRulesR; fail).
      all: try (apply rqUpUpRuleS_ImplRulesR; fail).
      all: try (apply rsDownDownRule_ImplRulesR; red; simpl; auto; fail).
      all: try (apply rsDownDownRuleS_ImplRulesR; red; simpl; auto; fail).
  Qed.

  Lemma mesi_SpecRulesIn: SpecRulesIn (MesiImp.impl Htr) (Mesi.impl Htr).
  Proof.
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
