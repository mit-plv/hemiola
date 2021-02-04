Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Topology Syntax Semantics StepM SemFacts.
Require Import RqRsTopo RqRsUtil.

Require Import Ex.SpecInds Ex.Template Ex.RuleTransform Ex.RuleTransformOk.
Require Import Ex.Msi.Msi Ex.Msi.MsiTopo Ex.Msi.MsiImp Ex.Msi.MsiSim.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Section MsiImpOk.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).
  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).

  Lemma msi_ImplRules: ImplRules tr (MsiImp.impl Htr) (Msi.impl Htr).
  Proof.
    red; intros.
    destruct H; [subst|apply in_app_or in H; destruct H].

    - (** Main memory *)
      eexists; repeat split; [left; reflexivity|].
      red; simpl; intros.
      left; split; [|assumption].
      unfold memRulesFromChildren in H.
      apply concat_In in H; dest.
      apply in_map_iff in H; dest; subst.
      dest_in.
      all: apply immDownRule_RssEquivRule; red; simpl; auto.

    - (** Li cache *)
      apply in_map_iff in H; destruct H as [oidx [? ?]]; subst; simpl in *.
      eexists; repeat split;
        [right; apply in_or_app; left;
         apply in_map_iff; eexists; repeat split; eassumption
        |reflexivity|].

      red; intros.
      apply in_app_or in H; destruct H.

      + apply concat_In in H; destruct H as [crls [? ?]].
        apply in_map_iff in H; destruct H as [cidx [? ?]]; subst.
        pose proof (subtreeChildrenIndsOf_parentIdxOf
                      (tree2Topo_WfDTree tr 0) _ _ H2) as Hp.
        dest_in.

        Ltac li_cidx_RssEquivRule equiv_thm cidx :=
          left; split;
          [apply equiv_thm; red; simpl; auto; fail
          |apply in_or_app; left;
           apply in_concat;
           eexists; split;
           [apply in_map_iff; exists cidx; split; [reflexivity|assumption]
           |simpl; tauto]].

        all: try (li_cidx_RssEquivRule immDownRule_RssEquivRule cidx).
        all: try (li_cidx_RssEquivRule rqUpUpRule_RssEquivRule cidx).
        all: try (li_cidx_RssEquivRule rqUpDownRule_RssEquivRule cidx).
        all: try (right; right; right; repeat eexists; assumption).

      + dest_in.

        Ltac li_RssEquivRule equiv_thm :=
          left; split;
          [apply equiv_thm; red; simpl; auto; fail
          |apply in_or_app; right; simpl; tauto].

        all: try (li_RssEquivRule immRule_RssEquivRule).
        all: try (li_RssEquivRule immUpRule_RssEquivRule).
        all: try (li_RssEquivRule rqUpUpRuleS_RssEquivRule).
        all: try (li_RssEquivRule rqDownDownRule_RssEquivRule).
        all: try (li_RssEquivRule rsDownDownRule_RssEquivRule).
        all: try (li_RssEquivRule rsDownDownRuleS_RssEquivRule).
        all: try (right; left; repeat eexists;
                  apply in_or_app; right; simpl; tauto).
        all: try (right; right; left; repeat eexists;
                  apply in_or_app; right; simpl; tauto).

        * left; split.
          { apply rsDownDownRule_RssEquivRule.
            red; unfold getUpLockIdxBackI, getUpLockIdxBack; simpl; intros.
            red in H1; dest.
            congruence.
          }
          { apply in_or_app; right; simpl; tauto. }
        * left; split.
          { apply rsDownRqDownRule_RssEquivRule.
            red; unfold RsDownRqDownSoundPrec, getUpLockIdxBackI, getUpLockIdxBack; simpl; intros.
            red in H1; dest.
            rewrite <-H1.
            repeat split; assumption.
          }
          { apply in_or_app; right; simpl; tauto. }

    - (** L1 cache *)
      apply in_map_iff in H; destruct H as [oidx [? ?]]; subst.
      eexists; repeat split;
        [right; apply in_or_app; right;
         apply in_map_iff; eexists; repeat split; assumption|].
      red; intros.
      dest_in.

      Ltac l1_RssEquivRule equiv_thm :=
        left; split;
        [apply equiv_thm; red; simpl; auto; fail
        |simpl; tauto].

      all: try (l1_RssEquivRule immUpRule_RssEquivRule).
      all: try (l1_RssEquivRule immDownRule_RssEquivRule).
      all: try (l1_RssEquivRule rqUpUpRule_RssEquivRule).
      all: try (l1_RssEquivRule rqUpUpRuleS_RssEquivRule).
      all: try (l1_RssEquivRule rsDownDownRule_RssEquivRule).
      all: try (l1_RssEquivRule rsDownDownRuleS_RssEquivRule).
  Qed.

  Lemma msi_imp_msi_ok:
    (steps step_m) # (steps step_m) |-- (MsiImp.impl Htr) ⊑ (Msi.impl Htr).
  Proof.
    apply rss_holder_ok with (tr:= tr); try reflexivity.
    - apply msi_ImplRules.
    - simpl; rewrite !map_app, !map_map, !map_id.
      rewrite app_comm_cons.
      rewrite <-c_li_indices_head_rootOf by assumption.
      reflexivity.
    - apply msi_GoodRqRsSys.
    - apply msi_GoodExtRssSys.
  Qed.

  Local Definition spec :=
    @SpecInds.spec (c_l1_indices cifc) (tree2Topo_l1_NoPrefix tr 0).

  Theorem msi_imp_ok:
    (steps step_m) # (steps step_m) |-- (MsiImp.impl Htr) ⊑ spec.
  Proof.
    eapply refines_trans.
    - apply msi_imp_msi_ok.
    - apply MsiSim.msi_ok.
  Qed.

End MsiImpOk.
