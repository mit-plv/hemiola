Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector ListSupport IndexSupport.
Require Import Syntax Topology Semantics.
Require Import RqRsLangEx.

Require Import Ex.Spec Ex.SpecSv Ex.Template Ex.Mesi.
Require Import Ex.Mesi.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** TODO: to [RqRsFacts.v]; relaxed conditions *)
Section RqRsChnsOnDTree.
  Variables (dtr: DTree).
  Hypothesis (Hd: RqRsChnsOnDTree dtr).

  Lemma rqEdgeUpFrom_Some_light:
    forall oidx rqUp,
      rqEdgeUpFrom dtr oidx = Some rqUp ->
      exists rsUp down pidx,
        rsEdgeUpFrom dtr oidx = Some rsUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx.
  Proof.
    unfold rqEdgeUpFrom, upEdgesFrom; intros.
    remember (parentChnsOf oidx dtr) as pchns.
    destruct pchns as [[root pidx]|]; simpl in *; [|discriminate].
    unfold rsEdgeUpFrom, upEdgesFrom, edgeDownTo, downEdgesTo, parentIdxOf.
    apply eq_sym in Heqpchns.
    rewrite Heqpchns; simpl.
    apply Hd in Heqpchns.
    destruct Heqpchns as [rqUp' [rsUp [down ?]]]; dest; subst; simpl.
    rewrite H0, H1.
    repeat eexists.
  Qed.

  Lemma rsEdgeUpFrom_Some_light:
    forall oidx rsUp,
      rsEdgeUpFrom dtr oidx = Some rsUp ->
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx.
  Proof.
    unfold rsEdgeUpFrom, upEdgesFrom; intros.
    remember (parentChnsOf oidx dtr) as pchns.
    destruct pchns as [[root pidx]|]; simpl in *; [|discriminate].
    unfold rqEdgeUpFrom, upEdgesFrom, edgeDownTo, downEdgesTo, parentIdxOf.
    apply eq_sym in Heqpchns.
    rewrite Heqpchns; simpl.
    apply Hd in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp' [down ?]]]; dest; subst; simpl.
    rewrite H0, H1.
    repeat eexists.
  Qed.

  Lemma edgeDownTo_Some_light:
    forall oidx down,
      edgeDownTo dtr oidx = Some down ->
      exists rqUp rsUp pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        rsEdgeUpFrom dtr oidx = Some rsUp /\
        parentIdxOf dtr oidx = Some pidx.
  Proof.
    unfold edgeDownTo, downEdgesTo; intros.
    remember (parentChnsOf oidx dtr) as pchns.
    destruct pchns as [[root pidx]|]; simpl in *; [|discriminate].
    unfold rqEdgeUpFrom, rsEdgeUpFrom, upEdgesFrom, parentIdxOf.
    apply eq_sym in Heqpchns.
    rewrite Heqpchns; simpl.
    apply Hd in Heqpchns.
    destruct Heqpchns as [rqUp [rsUp [down' ?]]]; dest; subst; simpl.
    rewrite H0.
    repeat eexists.
  Qed.

End RqRsChnsOnDTree.

(** TODO: to [TopoTemplate.v] *)
Lemma tree2Topo_obj_rqUpFrom_not_in_merss:
  forall tr bidx oidx,
    In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
               ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
    ~ In (rqUpFrom oidx) (c_merss (snd (tree2Topo tr bidx))).
Proof.
  intros.
  pose proof (tree2Topo_obj_chns_minds_SubList tr bidx H).
  pose proof (tree2Topo_minds_merss_disj tr bidx).
  intro Hx.
  eapply DisjList_In_1; [eapply H1|..]; eauto.
  apply H0; simpl; tauto.
Qed.

Lemma tree2Topo_obj_rsUpFrom_not_in_merss:
  forall tr bidx oidx,
    In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
               ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
    ~ In (rsUpFrom oidx) (c_merss (snd (tree2Topo tr bidx))).
Proof.
  intros.
  pose proof (tree2Topo_obj_chns_minds_SubList tr bidx H).
  pose proof (tree2Topo_minds_merss_disj tr bidx).
  intro Hx.
  eapply DisjList_In_1; [eapply H1|..]; eauto.
  apply H0; simpl; tauto.
Qed.

Lemma tree2Topo_obj_downTo_not_in_merss:
  forall tr bidx oidx,
    In oidx ((c_li_indices (snd (tree2Topo tr bidx)))
               ++ c_l1_indices (snd (tree2Topo tr bidx))) ->
    ~ In (downTo oidx) (c_merss (snd (tree2Topo tr bidx))).
Proof.
  intros.
  pose proof (tree2Topo_obj_chns_minds_SubList tr bidx H).
  pose proof (tree2Topo_minds_merss_disj tr bidx).
  intro Hx.
  eapply DisjList_In_1; [eapply H1|..]; eauto.
  apply H0; simpl; tauto.
Qed.

Lemma rqEdgeUpFrom_rqUpFrom:
  forall tr bidx oidx midx,
    rqEdgeUpFrom (fst (tree2Topo tr bidx)) oidx = Some midx ->
    midx = rqUpFrom oidx.
Proof.
  intros.
  pose proof H.
  eapply rqEdgeUpFrom_Some_light in H; [|apply tree2Topo_RqRsChnsOnDTree].
  dest.
  pose proof (tree2Topo_TreeTopoNode tr bidx).
  specialize (H3 _ _ H2); dest.
  repeat disc_rule_minds; auto.
Qed.

Lemma rsEdgeUpFrom_rsUpFrom:
  forall tr bidx oidx midx,
    rsEdgeUpFrom (fst (tree2Topo tr bidx)) oidx = Some midx ->
    midx = rsUpFrom oidx.
Proof.
  intros.
  pose proof H.
  eapply rsEdgeUpFrom_Some_light in H; [|apply tree2Topo_RqRsChnsOnDTree].
  dest.
  pose proof (tree2Topo_TreeTopoNode tr bidx).
  specialize (H3 _ _ H2); dest.
  repeat disc_rule_minds; auto.
Qed.

Lemma edgeDownTo_downTo:
  forall tr bidx oidx midx,
    edgeDownTo (fst (tree2Topo tr bidx)) oidx = Some midx ->
    midx = downTo oidx.
Proof.
  intros.
  pose proof H.
  eapply edgeDownTo_Some_light in H; [|apply tree2Topo_RqRsChnsOnDTree].
  dest.
  pose proof (tree2Topo_TreeTopoNode tr bidx).
  specialize (H3 _ _ H2); dest.
  repeat disc_rule_minds; auto.
Qed.

(** TODO: to [RuleTemplate.v] *)

Lemma tree2Topo_immRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx prec trs ost orq ins,
    rule_precond (immRule ridx prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (immRule ridx prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest; discriminate.
Qed.

Lemma tree2Topo_immDownRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId cidx prec trs ost orq ins,
    rule_precond (immDownRule ridx msgId cidx prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (immDownRule ridx msgId cidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest.
  destruct H0.
  - dest; discriminate.
  - dest; disc_rule_conds_ex.
    apply rqEdgeUpFrom_rqUpFrom in H7; discriminate.
Qed.

Lemma tree2Topo_immUpRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (immUpRule ridx msgId oidx prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (immUpRule ridx msgId oidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest.
  destruct H0.
  - dest; discriminate.
  - dest; disc_rule_conds_ex.
    apply rqEdgeUpFrom_rqUpFrom in H6; discriminate.
Qed.

Lemma tree2Topo_rqUpDownRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx cidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (rqUpDownRule ridx msgId cidx oidx prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpDownRule ridx msgId cidx oidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest.
  destruct H0.
  - dest; discriminate.
  - dest; disc_rule_conds_ex.
    destruct (fst (trs ost x4)); [discriminate|].
    inv H1; apply rqEdgeUpFrom_rqUpFrom in H6; discriminate.
Qed.

Lemma tree2Topo_rqDownDownRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (rqDownDownRule ridx msgId oidx prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rqDownDownRule ridx msgId oidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest.
  destruct H0.
  - dest; discriminate.
  - dest; disc_rule_conds_ex.
    destruct (fst (trs ost x4)); [discriminate|].
    inv H1; apply rqEdgeUpFrom_rqUpFrom in H6; discriminate.
Qed.

Lemma tree2Topo_rsDownDownRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsDownDownRule ridx msgId rqId prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRule ridx msgId rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest.
  destruct H2.
  - dest; discriminate.
  - dest; disc_rule_conds_ex.
    clear -H5.
    apply f_equal with (f:= fun m => m@[upRq]) in H5; mred.
Qed.

Lemma tree2Topo_rsDownDownRuleS_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (rsDownDownRuleS ridx msgId prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRuleS ridx msgId prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest.
  destruct H3.
  - dest; discriminate.
  - dest; disc_rule_conds_ex.
    clear -H7.
    apply f_equal with (f:= fun m => m@[upRq]) in H7; mred.
Qed.

Lemma tree2Topo_rsUpDownRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsUpDownRule ridx msgId rqId prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpDownRule ridx msgId rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H1; dest.
  clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
  specialize (H3 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H3 _ _ _ eq_refl).
  inv H3; discriminate.
Qed.

Lemma tree2Topo_rsUpDownRuleOne_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsUpDownRuleOne ridx msgId rqId prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpDownRuleOne ridx msgId rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H1; dest.
  clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
  specialize (H3 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H3 _ _ _ eq_refl).
  inv H3; discriminate.
Qed.

Lemma tree2Topo_rsUpUpRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsUpUpRule ridx msgId rqId prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpUpRule ridx msgId rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H1; dest.
  clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
  specialize (H3 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H3 _ _ _ eq_refl).
  inv H3; discriminate.
Qed.

Lemma tree2Topo_rsUpUpRuleOne_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsUpUpRuleOne ridx msgId rqId prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpUpRuleOne ridx msgId rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H1; dest.
  clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
  specialize (H3 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H3 _ _ _ eq_refl).
  inv H3; discriminate.
Qed.

Lemma tree2Topo_rsDownRqDownRule_not_RqToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsDownRqDownRule ridx msgId oidx rqId prec trs) ost orq ins ->
    ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownRqDownRule ridx msgId oidx rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  red in H2; dest.
  clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
  specialize (H5 _ _ _ H0).
  disc_rule_conds_ex.
  specialize (H5 _ _ _ eq_refl); dest.
  destruct H2.
  - dest; discriminate.
  - dest; disc_rule_conds_ex.
    destruct (fst (snd (trs ost msg))); [discriminate|].
    inv H4; apply rqEdgeUpFrom_rqUpFrom in H10; discriminate.
Qed.


Lemma tree2Topo_immRule_not_RsToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx prec trs ost orq ins,
    rule_precond (immRule ridx prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (immRule ridx prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest; discriminate.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest; discriminate.
Qed.

Lemma tree2Topo_immDownRule_not_RsToUpRule:
  forall `{OStateIfc} tr bidx cidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (immDownRule ridx msgId cidx prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (immDownRule ridx msgId cidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    inv H5.
    apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest; discriminate.
Qed.

Lemma tree2Topo_rqUpUpRule_not_RsToUpRule:
  forall `{OStateIfc} tr bidx cidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (rqUpUpRule ridx msgId cidx oidx prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpUpRule ridx msgId cidx oidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    inv H5.
    apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H1; mred.
Qed.

Lemma tree2Topo_rqUpUpRuleS_not_RsToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx prec trs ost orq ins,
    rule_precond (rqUpUpRuleS ridx oidx prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpUpRuleS ridx oidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct ins; discriminate.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest.
    unfold addRqS in H5.
    apply f_equal with (f:= fun m => m@[upRq]) in H5; mred.
Qed.

Lemma tree2Topo_rqUpDownRule_not_RsToUpRule:
  forall `{OStateIfc} tr bidx cidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (rqUpDownRule ridx msgId cidx oidx prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpDownRule ridx msgId cidx oidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct (fst (trs ost rmsg)); [discriminate|].
    inv H5.
    apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H1; mred.
Qed.

Lemma tree2Topo_rqDownDownRule_not_RsToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (rqDownDownRule ridx msgId oidx prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqDownDownRule ridx msgId oidx prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct (fst (trs ost rmsg)); [discriminate|].
    inv H5.
    apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H1; mred.
Qed.

Lemma tree2Topo_rsDownDownRule_not_RsToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsDownDownRule ridx msgId rqId prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRule ridx msgId rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    red in H4.
    clear -H0 H4. (* [rule_precond] and [RulePostSat] *)
    specialize (H4 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H4 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H4; mred.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H3; mred.
Qed.

Lemma tree2Topo_rsDownDownRuleS_not_RsToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId prec trs ost orq ins,
    rule_precond (rsDownDownRuleS ridx msgId prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRuleS ridx msgId prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    red in H4.
    clear -H0 H4. (* [rule_precond] and [RulePostSat] *)
    specialize (H4 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H4 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H4; mred.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H4; mred.
Qed.

Lemma tree2Topo_rsDownRqDownRule_not_RsToUpRule:
  forall `{OStateIfc} tr bidx oidx ridx msgId rqId prec trs ost orq ins,
    rule_precond (rsDownRqDownRule ridx msgId oidx rqId prec trs) ost orq ins ->
    ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownRqDownRule ridx msgId oidx rqId prec trs).
Proof.
  intros; intro.
  destruct H1.
  - red in H1; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct (fst (snd (trs ost msg))); [discriminate|].
    inv H8.
    apply rsEdgeUpFrom_rsUpFrom in H4; discriminate.
  - dest.
    red in H1; dest.
    red in H1.
    clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
    specialize (H1 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H1 _ _ _ eq_refl); dest.
    apply f_equal with (f:= fun m => m@[upRq]) in H3; mred.
Qed.

Lemma map_add_remove_comm:
  forall {A} (m: M.t A) k1 v k2,
    k1 <> k2 ->
    M.remove k2 (M.add k1 v m) = M.add k1 v (M.remove k2 m).
Proof.
  intros; meq.
  M.cmp y k2; mred.
Qed.

Section System.
  Variable tr: tree.
  Hypothesis (Htr: tr <> Node nil).

  Local Notation topo := (fst (tree2Topo tr 0)).
  Local Notation cifc := (snd (tree2Topo tr 0)).
  Local Notation impl := (impl Htr).

  Hint Extern 0 (TreeTopo _) => apply tree2Topo_TreeTopo.
  Hint Extern 0 (WfDTree _) => apply tree2Topo_WfDTree.

  Lemma mesi_indices:
    map obj_idx (sys_objs impl) = c_li_indices cifc ++ c_l1_indices cifc.
  Proof.
    simpl; rewrite c_li_indices_head_rootOf at 2 by assumption.
    simpl; f_equal.
    rewrite map_app, map_map, map_id; simpl.
    rewrite map_map, map_id; reflexivity.
  Qed.
  
  Lemma mesi_GoodORqsInit: GoodORqsInit (initsOf impl).
  Proof.
    apply initORqs_GoodORqsInit.
  Qed.

  Lemma mesi_WfDTree: WfDTree topo.
  Proof.
    apply tree2Topo_WfDTree.
  Qed.

  Lemma mesi_RqRsChnsOnDTree: RqRsChnsOnDTree topo.
  Proof.
    apply tree2Topo_RqRsChnsOnDTree.
  Qed.

  Lemma mesi_RqRsChnsOnSystem: RqRsChnsOnSystem topo impl.
  Proof.
    eapply tree2Topo_RqRsChnsOnSystem with (tr0:= tr) (bidx:= [0]); try reflexivity.
    - destruct (tree2Topo _ _); reflexivity.
    - simpl.
      rewrite map_app.
      do 2 rewrite map_trans.
      do 2 rewrite map_id.
      rewrite app_comm_cons.
      rewrite <-c_li_indices_head_rootOf by assumption.
      reflexivity.
  Qed.

  Lemma mesi_ExtsOnDTree: ExtsOnDTree topo impl.
  Proof.
    eapply tree2Topo_ExtsOnDTree with (tr0:= tr) (bidx:= [0]); try reflexivity.
    destruct (tree2Topo _ _); reflexivity.
  Qed.
  
  Lemma mesi_RqRsDTree: RqRsDTree topo impl.
  Proof.
    red; repeat ssplit.
    - auto using mesi_WfDTree.
    - auto using mesi_RqRsChnsOnDTree.
    - auto using mesi_RqRsChnsOnSystem.
    - auto using mesi_ExtsOnDTree.
  Qed.

  Ltac rule_immd := left.
  Ltac rule_immu := right; left.
  Ltac rule_rquu := do 2 right; left.
  Ltac rule_rqsu := do 2 right; left.
  Ltac rule_rqud := do 2 right; left.
  Ltac rule_rqdd := do 2 right; left.
  Ltac rule_rsdd := do 3 right; left.
  Ltac rule_rsds := do 3 right; left.
  Ltac rule_rsu := do 3 right; left.
  Ltac rule_rsrq := do 4 right.

  Ltac solve_GoodRqRsRule :=
    autounfold with MesiRules;
    repeat
      match goal with
      | |- GoodRqRsRule _ _ _ _ =>
        match goal with
        | |- context[immRule] =>
          rule_immd; eapply immRule_ImmDownRule; eauto
        | |- context[immDownRule] =>
          rule_immd; eapply immDownRule_ImmDownRule; eauto
        | |- context[immUpRule] =>
          rule_immu; eapply immUpRule_ImmUpRule; eauto
        | |- context[rqUpUpRule] =>
          rule_rquu; eapply rqUpUpRule_RqFwdRule; eauto
        | |- context[rqUpUpRuleS] =>
          rule_rqsu; eapply rqUpUpRuleS_RqFwdRule; eauto
        | |- context[rqUpDownRule] =>
          rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto
        | |- context[rqDownDownRule] =>
          rule_rqdd; eapply rqDownDownRule_RqFwdRule; eauto
        | |- context[rsDownDownRule] =>
          rule_rsdd; eapply rsDownDownRule_RsBackRule; eauto
        | |- context[rsDownDownRuleS] =>
          rule_rsds; eapply rsDownDownRuleS_RsBackRule; eauto
        | |- context[rsUpDownRule] =>
          rule_rsu; eapply rsUpDownRule_RsBackRule; eauto
        | |- context[rsUpDownRuleOne] =>
          rule_rsu; eapply rsUpDownRuleOne_RsBackRule; eauto
        | |- context[rsUpUpRule] =>
          rule_rsu; eapply rsUpUpRule_RsBackRule; eauto
        | |- context[rsUpUpRuleOne] =>
          rule_rsu; eapply rsUpUpRuleOne_RsBackRule; eauto
        | |- context[rsDownRqDownRule] =>
          rule_rsrq; eapply rsDownRqDownRule_RsDownRqDownRule; eauto
        end
      | |- parentIdxOf _ _ = Some _ =>
        apply subtreeChildrenIndsOf_parentIdxOf; auto; fail
      | |- parentIdxOf _ (l1ExtOf _) = Some _ =>
        apply tree2Topo_l1_ext_parent; auto; fail
      end.

  Lemma mesi_GoodRqRsSys: GoodRqRsSys topo impl.
  Proof.
    repeat
      match goal with
      | |- GoodRqRsSys _ _ => red
      | |- GoodRqRsObj _ _ _ => red
      | |- Forall _ _ => simpl; constructor; simpl
      | |- Forall _ (_ ++ _) => apply Forall_app
      end.

    - (** Main memory *)

      assert (In (rootOf topo) (c_li_indices cifc)) as Hrin.
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }
      
      simpl.
      repeat
        match goal with
        | |- Forall _ (_ ++ _) => apply Forall_app
        | |- Forall _ (_ :: _) => constructor
        | |- Forall _ nil => constructor
        end.
      2-3: try (solve_GoodRqRsRule; fail).

      apply Forall_forall; intros.
      unfold liRulesFromChildren in H.
      apply concat_In in H; dest.
      apply in_map_iff in H; dest; subst.
      dest_in.
      all: try (solve_GoodRqRsRule; fail).

      { (* [liGetSRqUpDownME] *)
        apply subtreeChildrenIndsOf_parentIdxOf in H1; [|apply tree2Topo_WfDTree].
        pose proof (tree2Topo_li_child_li_l1 _ _ _ Hrin H1).
        rewrite <-mesi_indices in H.
        
        rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

        (** [RqUpDownSound] *)
        red; simpl; intros; dest.
        apply subtreeChildrenIndsOf_parentIdxOf in H2; [|apply tree2Topo_WfDTree].
        repeat ssplit; [discriminate| |intuition auto].
        repeat constructor; try assumption.
      }

      { (* [liGetMRqUpDownME] *)
        apply subtreeChildrenIndsOf_parentIdxOf in H1; [|apply tree2Topo_WfDTree].
        pose proof (tree2Topo_li_child_li_l1 _ _ _ Hrin H1).
        rewrite <-mesi_indices in H.
        
        rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

        (** [RqUpDownSound] *)
        red; simpl; intros; dest.
        apply subtreeChildrenIndsOf_parentIdxOf in H2; [|apply tree2Topo_WfDTree].
        repeat ssplit; [discriminate| |intuition auto].
        repeat constructor; try assumption.
      }

      { (* [liGetMRqUpDownS] *)
        apply subtreeChildrenIndsOf_parentIdxOf in H1; [|apply tree2Topo_WfDTree].
        pose proof (tree2Topo_li_child_li_l1 _ _ _ Hrin H1).
        rewrite <-mesi_indices in H.
        
        rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

        (** [RqUpDownSound] *)
        red; simpl; intros; dest.
        repeat ssplit; [assumption| |intuition auto].
        apply Forall_forall; intros.
        apply H3 in H7.
        eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
      }

    - (** Li caches *)
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; simpl.

      (* pre-register a fact: an Li cache always has a parent *)
      pose proof (c_li_l1_indices_has_parent
                    Htr _ _ (in_or_app _ _ _ (or_introl H0))).
      destruct H as [pidx ?].
      
      repeat
        match goal with
        | |- Forall _ (_ ++ _) => apply Forall_app
        | |- Forall _ (_ :: _) => constructor
        | |- Forall _ nil => constructor
        end.
      all: try (solve_GoodRqRsRule; fail).

      1: {
        apply Forall_forall; intros.
        unfold liRulesFromChildren in H1.
        apply concat_In in H1; dest.
        apply in_map_iff in H1; dest; subst.
        dest_in.
        all: try (solve_GoodRqRsRule; fail).

        { (* [liGetSRqUpDownME] *)
          apply subtreeChildrenIndsOf_parentIdxOf in H3; [|apply tree2Topo_WfDTree].
          pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H0) H3).
          rewrite <-mesi_indices in H1.
          
          rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

          (** [RqUpDownSound] *)
          red; simpl; intros; dest.
          apply subtreeChildrenIndsOf_parentIdxOf in H4; [|apply tree2Topo_WfDTree].
          repeat ssplit; [discriminate| |intuition auto].
          repeat constructor; try assumption.
        }

        { (* [liGetMRqUpDownME] *)
          apply subtreeChildrenIndsOf_parentIdxOf in H3; [|apply tree2Topo_WfDTree].
          pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H0) H3).
          rewrite <-mesi_indices in H1.
          
          rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

          (** [RqUpDownSound] *)
          red; simpl; intros; dest.
          apply subtreeChildrenIndsOf_parentIdxOf in H4; [|apply tree2Topo_WfDTree].
          repeat ssplit; [discriminate| |intuition auto].
          repeat constructor; try assumption.
        }

        { (* [liGetMRqUpDownS] *)
          apply subtreeChildrenIndsOf_parentIdxOf in H3; [|apply tree2Topo_WfDTree].
          pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H0) H3).
          rewrite <-mesi_indices in H1.
          
          rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

          (** [RqUpDownSound] *)
          red; simpl; intros; dest.
          repeat ssplit; [assumption| |intuition auto].
          apply Forall_forall; intros.
          apply H5 in H9.
          eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
        }
      }

      { (* [liDownSRqDownDownME] *)
        rule_rqdd.
        eapply rqDownDownRule_RqFwdRule; eauto.

        (** [RqDownDownSound] *)
        red; simpl; intros; dest.
        repeat ssplit; [discriminate|].
        repeat constructor.
        eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
      }

      { (* [liGetMRsDownRqDownDirS] *)
        rule_rsrq; eapply rsDownRqDownRule_RsDownRqDownRule; eauto.

        (** [RsDownRqDownSound] *)
        red; simpl; intros; dest.
        red in H1.
        destruct (orq@[upRq]) as [rqiu|]; simpl in *; auto.
        destruct H1 as [rcidx [rqUp ?]]; dest.
        pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H0) H1).
        rewrite <-mesi_indices in H8.
        intros; repeat ssplit.
        { assumption. }
        { apply Forall_forall; intros.
          apply H3 in H10.
          eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
        }
        { exists rcidx, rqUp.
          repeat split; try assumption.
        }
      }

      { (* [liDownIRqDownDownDirS] *)
        rule_rqdd.
        eapply rqDownDownRule_RqFwdRule; eauto.

        (** [RqDownDownSound] *)
        red; simpl; intros; dest.
        repeat ssplit; [assumption|].
        apply Forall_forall; intros.
        apply H2 in H4.
        eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
      }

      { (* [liDownIRqDownDownDirME] *)
        rule_rqdd.
        eapply rqDownDownRule_RqFwdRule; eauto.

        (** [RqDownDownSound] *)
        red; simpl; intros; dest.
        repeat ssplit; [discriminate|].
        repeat constructor.
        eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
      }

    - (** L1 caches *)
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; simpl.

      (* pre-register a fact: an L1 cache always has a parent *)
      pose proof (c_li_l1_indices_has_parent
                    Htr _ _ (in_or_app _ _ _ (or_intror H0))).
      destruct H as [pidx ?].
      
      repeat
        match goal with
        | |- Forall _ (_ ++ _) => apply Forall_app
        | |- Forall _ (_ :: _) => constructor
        | |- Forall _ nil => constructor
        end.
      all: try (solve_GoodRqRsRule; fail).
  Qed.

  Ltac exfalso_RqToUpRule :=
    red; intros; exfalso;
    repeat autounfold with MesiRules in *;
    match goal with
    | [H: context[RqToUpRule] |- _] =>
      match type of H with
      | context [immRule] =>
        eapply tree2Topo_immRule_not_RqToUpRule; eauto
      | context [immDownRule] =>
        eapply tree2Topo_immDownRule_not_RqToUpRule; eauto
      | context [immUpRule] =>
        eapply tree2Topo_immUpRule_not_RqToUpRule; eauto
      | context [rqUpDownRule] =>
        eapply tree2Topo_rqUpDownRule_not_RqToUpRule; eauto
      | context [rqDownDownRule] =>
        eapply tree2Topo_rqDownDownRule_not_RqToUpRule; eauto
      | context [rsDownDownRule] =>
        eapply tree2Topo_rsDownDownRule_not_RqToUpRule; eauto
      | context [rsDownDownRuleS] =>
        eapply tree2Topo_rsDownDownRuleS_not_RqToUpRule; eauto
      | context [rsUpDownRule] =>
        eapply tree2Topo_rsUpDownRule_not_RqToUpRule; eauto
      | context [rsUpDownRuleOne] =>
        eapply tree2Topo_rsUpDownRuleOne_not_RqToUpRule; eauto
      | context [rsUpUpRule] =>
        eapply tree2Topo_rsUpUpRule_not_RqToUpRule; eauto
      | context [rsUpUpRuleOne] =>
        eapply tree2Topo_rsUpUpRuleOne_not_RqToUpRule; eauto
      | context [rsDownRqDownRule] =>
        eapply tree2Topo_rsDownRqDownRule_not_RqToUpRule; eauto
      end
    end.

  Ltac exfalso_RsToUpRule :=
    red; intros; exfalso;
    repeat autounfold with MesiRules in *;
    match goal with
    | [H: context[RsToUpRule] |- _] =>
      match type of H with
      | context [immRule] =>
        eapply tree2Topo_immRule_not_RsToUpRule; eauto
      | context [immDownRule] =>
        eapply tree2Topo_immDownRule_not_RsToUpRule; eauto
      | context [rqUpUpRule] =>
        eapply tree2Topo_rqUpUpRule_not_RsToUpRule; eauto
      | context [rqUpUpRuleS] =>
        eapply tree2Topo_rqUpUpRuleS_not_RsToUpRule; eauto
      | context [rqUpDownRule] =>
        eapply tree2Topo_rqUpDownRule_not_RsToUpRule; eauto
      | context [rqDownDownRule] =>
        eapply tree2Topo_rqDownDownRule_not_RsToUpRule; eauto
      | context [rsDownDownRule] =>
        eapply tree2Topo_rsDownDownRule_not_RsToUpRule; eauto
      | context [rsDownDownRuleS] =>
        eapply tree2Topo_rsDownDownRuleS_not_RsToUpRule; eauto
      | context [rsDownRqDownRule] =>
        eapply tree2Topo_rsDownRqDownRule_not_RsToUpRule; eauto
      end
    end.

  Lemma mesi_RqUpRsUpOkSys: RqUpRsUpOkSys topo impl.
  Proof. (* SKIP_PROOF_OFF *)
    repeat
      match goal with
      | |- RqUpRsUpOkSys _ _ => red
      | |- Forall _ _ => simpl; constructor; simpl
      | |- Forall _ (_ ++ _) => apply Forall_app
      end.

    - (** The main memory: no RqUp rules *)
      red; intros.
      simpl in H; apply in_app_or in H; destruct H;
        [unfold liRulesFromChildren in H;
         apply concat_In in H; dest;
         apply in_map_iff in H; dest; subst;
         dest_in|dest_in].
      all: try (exfalso_RqToUpRule; fail).

    - (** Li cache *)
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; intros.

      simpl in H; apply in_app_or in H; destruct H;
        [unfold liRulesFromChildren in H;
         apply concat_In in H; dest;
         apply in_map_iff in H; dest; subst;
         dest_in|dest_in].
      all: try (exfalso_RqToUpRule; fail).

      + simpl in H2; apply in_app_or in H2; destruct H2;
          [unfold liRulesFromChildren in H;
           apply concat_In in H; dest;
           apply in_map_iff in H; dest; subst;
           dest_in|dest_in].
        all: try (exfalso_RsToUpRule; fail).
        all: try (clear; solve_rule_conds_ex; solve_mesi).
        { clear; solve_rule_conds_const.
          all: try (destruct H6; dest; try solve [congruence|solve_mesi]).
        }
        { clear; solve_rule_conds_const.
          { mred; rewrite Hmsg; simpl; split; [assumption|congruence]. }
          { mred; rewrite Hidx; simpl; auto. }
          { mred; simpl; rewrite Hmsg, Hidx; simpl.
            repeat split; auto; simpl; try solve [mred|solve_mesi].
            f_equal; apply map_add_remove_comm; discriminate.
          }
        }

      + simpl in H2; apply in_app_or in H2; destruct H2;
          [unfold liRulesFromChildren in H;
           apply concat_In in H; dest;
           apply in_map_iff in H; dest; subst;
           dest_in|dest_in].
        all: try (exfalso_RsToUpRule; fail).
        all: try (clear; solve_rule_conds_ex; solve_mesi).
        { clear; solve_rule_conds_const.
          all: try (destruct H6; dest; try solve [congruence|solve_mesi]).
        }
        { clear; solve_rule_conds_const.
          { mred; rewrite Hmsg; simpl; split; [assumption|congruence]. }
          { mred; rewrite Hidx; simpl; auto. }
          { mred; simpl; rewrite Hmsg, Hidx; simpl.
            repeat split; auto; simpl; try solve [mred|solve_mesi].
            f_equal; apply map_add_remove_comm; discriminate.
          }
        }

      + simpl in H2; apply in_app_or in H2; destruct H2;
          [unfold liRulesFromChildren in H;
           apply concat_In in H; dest;
           apply in_map_iff in H; dest; subst;
           dest_in|dest_in].
        all: try (exfalso_RsToUpRule; fail).
        all: try (clear; solve_rule_conds_ex; solve_mesi).
        { clear; solve_rule_conds_const; try solve_mesi.
          unfold addRqS in H0; mred.
        }
        { clear; solve_rule_conds_const; try solve_mesi.
          unfold addRqS in H0; mred.
        }
        { clear; solve_rule_conds_const.
          { unfold addRqS in Hrqi; mred. }
          { unfold addRqS in Hrqi; mred.
            rewrite Hmsg; simpl; split; [assumption|congruence].
          }
          { unfold addRqS in Hrqi; mred.
            mred; rewrite Hidx; simpl; auto.
          }
          { unfold addRqS in Hrqi; mred.
            simpl; rewrite Hmsg, Hidx; simpl.
            repeat split; auto; simpl; try solve [mred|solve_mesi].
            f_equal; apply map_add_remove_comm; discriminate.
          }
        }
        
      + simpl in H2; apply in_app_or in H2; destruct H2;
          [unfold liRulesFromChildren in H;
           apply concat_In in H; dest;
           apply in_map_iff in H; dest; subst;
           dest_in|dest_in].
        all: try (exfalso_RsToUpRule; fail).
        all: try (clear; solve_rule_conds_ex; solve_mesi).
        { clear; solve_rule_conds_const; try intuition solve_mesi.
          unfold addRqS in H0; mred.
        }
        { clear; solve_rule_conds_const; try intuition solve_mesi.
          unfold addRqS in H0; mred.
        }
        { clear; solve_rule_conds_const; try intuition solve_mesi.
          { unfold addRqS in Hrqi; mred. }
          { unfold addRqS in Hrqi; mred.
            rewrite Hmsg; simpl; split; [assumption|congruence].
          }
          { unfold addRqS in Hrqi; mred.
            mred; rewrite Hidx; simpl; auto.
          }
          { unfold addRqS in Hrqi; mred.
            simpl; rewrite Hmsg, Hidx; simpl.
            repeat split; auto; simpl; try solve [mred|intuition solve_mesi].
            f_equal; apply map_add_remove_comm; discriminate.
          }
        }

    - (** L1 cache *)
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; intros.

      phide H2; dest_in.
      all: try (exfalso_RqToUpRule; fail).

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const; solve_mesi. }
        { clear; solve_rule_conds_const. }

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const. }
        { clear; solve_rule_conds_const; solve_mesi. }

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const; try solve_mesi.
          unfold addRqS in H0; mred.
        }
        { clear; solve_rule_conds_const; try solve_mesi.
          unfold addRqS in H0; mred.
        }

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const; try solve_mesi.
          unfold addRqS in H0; mred.
        }
        { clear; solve_rule_conds_const; try solve_mesi.
          unfold addRqS in H0; mred.
        }

        (* END_SKIP_PROOF_OFF *)
  Qed.

  Ltac solve_GoodExtRssSys :=
    repeat
      match goal with
      | [H: In ?oidx (c_l1_indices _) |- In ?oidx (c_li_indices _ ++ c_l1_indices _)] =>
        apply in_or_app; auto
      | [H: In ?oidx (c_li_indices _) |- In ?oidx (c_li_indices _ ++ c_l1_indices _)] =>
        apply in_or_app; auto
      | [H: In ?oidx (tl (c_li_indices _)) |- In ?oidx (c_li_indices _ ++ c_l1_indices _)] =>
        apply tl_In in H; apply in_or_app; auto
      | [H: In ?oidx (tl (c_li_indices _)) |- In ?oidx (c_li_indices _)] =>
        apply tl_In in H; assumption

      | [H: In _ (subtreeChildrenIndsOf _ _) |- _] =>
        apply subtreeChildrenIndsOf_parentIdxOf in H; [|apply tree2Topo_WfDTree];
        eapply tree2Topo_li_child_li_l1; eauto
      | |- In (rootOf _) (c_li_indices _) =>
        rewrite c_li_indices_head_rootOf by assumption; left; reflexivity

      | [H: In (rqUpFrom _) (c_merss _) |- MRq = MRs] =>
        exfalso; eapply tree2Topo_obj_rqUpFrom_not_in_merss; eauto
      | [H: In (rsUpFrom _) (c_merss _) |- MRq = MRs] =>
        exfalso; eapply tree2Topo_obj_rsUpFrom_not_in_merss; eauto
      | [H: In (downTo _) (c_merss _) |- MRq = MRs] =>
        exfalso; eapply tree2Topo_obj_downTo_not_in_merss; eauto
      | [H: False |- _] => exfalso; auto
      end.

  Lemma mesi_GoodExtRssSys: GoodExtRssSys impl.
  Proof. (* SKIP_PROOF_OFF *)
    red; simpl.
    constructor; [|apply Forall_app].
    - (** the main memory *)
      red; simpl; apply Forall_app.
      + apply Forall_forall; intros.
        unfold memRulesFromChildren in H.
        apply concat_In in H; dest.
        apply in_map_iff in H; dest; subst.
        dest_in.
        all: try (red; simpl; disc_rule_conds_ex; solve_GoodExtRssSys; fail).
        { (* [liGetMRqUpDownS] *)
          red; simpl; disc_rule_conds_ex.
          apply in_map_iff in H2; dest; subst.
          apply H5 in H11.
          simpl in *; solve_GoodExtRssSys.
        }

      + repeat constructor.
        all: try (red; simpl; disc_rule_conds_ex; solve_GoodExtRssSys; fail).

    - (** Li cache *)
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; simpl.
      apply Forall_app.

      + apply Forall_forall; intros.
        unfold liRulesFromChildren in H.
        apply concat_In in H; dest.
        apply in_map_iff in H; dest; subst.
        dest_in.
        all: try (red; simpl; disc_rule_conds_ex; solve_GoodExtRssSys; fail).
        { (* [liGetMRqUpDownS] *)
          red; simpl; disc_rule_conds_ex.
          apply in_map_iff in H3; dest; subst.
          apply H6 in H12.
          simpl in *; solve_GoodExtRssSys.
        }

      + repeat constructor.
        all: try (red; simpl; disc_rule_conds_ex; solve_GoodExtRssSys; fail).
        { (* [liGetMRsDownRqDownDirS] *)
          red; simpl; disc_rule_conds_ex.
          apply in_map_iff in H2; dest; subst.
          apply H11 in H5.
          simpl in *; solve_GoodExtRssSys.
        }
        { (* [liDownIRqDownDownDirS] *)
          red; simpl; disc_rule_conds_ex.
          apply in_map_iff in H2; dest; subst.
          apply H4 in H7.
          simpl in *; solve_GoodExtRssSys.
        }

    - (** L1 cache *)
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; simpl.
      repeat constructor.
      all: try (red; simpl; disc_rule_conds_ex; solve_GoodExtRssSys; fail).

      (* END_SKIP_PROOF_OFF *)
  Qed.

  Lemma mesi_GoodRqRsInterfSys: GoodRqRsInterfSys topo impl.
  Proof.
    split.
    - apply mesi_RqUpRsUpOkSys.
    - apply mesi_GoodExtRssSys.
  Qed.

  Lemma mesi_RqRsSys: RqRsSys topo impl.
  Proof.
    red; repeat ssplit.
    - apply mesi_RqRsDTree.
    - apply mesi_GoodRqRsSys.
    - apply mesi_GoodRqRsInterfSys.
  Qed.  
  
End System.

Hint Resolve mesi_GoodORqsInit mesi_WfDTree mesi_RqRsDTree mesi_RqRsSys.

