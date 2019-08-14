Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector ListSupport IndexSupport.
Require Import Syntax Topology Semantics.
Require Import RqRsLang.

Require Import Ex.Spec Ex.SpecSv Ex.Template Ex.Mesi.
Require Import Ex.Mesi.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** TODO: to [ListSupport.v] *)
Lemma concat_In:
  forall {A} (a: A) (ll: list (list A)),
    In a (List.concat ll) ->
    exists l, In l ll /\ In a l.
Proof.
  induction ll; simpl; intros; [exfalso; auto|].
  apply in_app_or in H; destruct H; eauto.
  specialize (IHll H); dest; eauto.
Qed.

(** TODO: to [Topology.v] *)
Lemma subtreeChildrenIndsOf_parentIdxOf:
  forall dtr (Hwf: WfDTree dtr) cidx oidx,
    In cidx (subtreeChildrenIndsOf dtr oidx) ->
    parentIdxOf dtr cidx = Some oidx.
Proof.
  intros.
  unfold subtreeChildrenIndsOf in H.
  destruct (subtree oidx dtr) eqn:Hstr; simpl in H; [|exfalso; auto].
  pose proof (subtree_Subtree _ _ Hstr).
  unfold childrenIndsOf in H.
  apply in_map_iff in H; dest; subst.
  rewrite parentIdxOf_Subtree_eq with (str:= d); auto.
  - eapply parentIdxOf_childrenOf in H1.
    apply subtree_rootOf in Hstr; subst; assumption.
  - apply neq_sym, parent_child_not_eq; [|assumption].
    eapply Subtree_wfDTree; eauto.
  - eapply indsOf_childrenOf; [eassumption|].
    apply indsOf_root_in.
Qed.

Section System.
  Variable tr: tree.

  Local Definition topo := fst (tree2Topo tr 0).
  Local Definition cifc := snd (tree2Topo tr 0).
  Local Definition impl := impl tr.

  Hint Extern 0 (TreeTopo topo) => apply tree2Topo_TreeTopo.
  Hint Extern 0 (WfDTree topo) => apply tree2Topo_WfDTree.
  
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
    - unfold topo, Mesi.cifc; destruct (tree2Topo _ _); reflexivity.
    - simpl; rewrite map_app; f_equal.
      + induction (c_li_indices (Mesi.cifc tr)); [reflexivity|].
        simpl; congruence.
      + induction (c_l1_indices (Mesi.cifc tr)); [reflexivity|].
        simpl; congruence.
  Qed.

  Lemma mesi_ExtsOnDTree: ExtsOnDTree topo impl.
  Proof.
    eapply tree2Topo_ExtsOnDTree with (tr0:= tr) (bidx:= [0]); try reflexivity.
    unfold topo, Mesi.cifc; destruct (tree2Topo _ _); reflexivity.
  Qed.
  
  Lemma mesi_impl_RqRsDTree: RqRsDTree topo impl.
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
        | |- context[immDownRule] =>
          rule_immd; apply immDownRule_ImmDownRule; auto
        | |- context[immUpRule] =>
          rule_immu; apply immUpRule_ImmUpRule; auto
        | |- context[rqUpUpRule] =>
          rule_rquu; apply rqUpUpRule_RqFwdRule; auto
        | |- context[rqUpUpRuleS] =>
          rule_rqsu; apply rqUpUpRuleS_RqFwdRule; auto
        | |- context[rqUpDownRule] =>
          rule_rqud; apply rqUpDownRule_RqFwdRule; auto
        | |- context[rqDownDownRule] =>
          rule_rqdd; apply rqDownDownRule_RqFwdRule; auto
        | |- context[rsDownDownRule] =>
          rule_rsdd; apply rsDownDownRule_RsBackRule; auto
        | |- context[rsDownDownRuleS] =>
          rule_rsds; apply rsDownDownRuleS_RsBackRule; auto
        | |- context[rsUpDownRule] =>
          rule_rsu; apply rsUpDownRule_RsBackRule; auto
        | |- context[rsUpUpRule] =>
          rule_rsu; apply rsUpUpRule_RsBackRule; auto
        | |- context[rsDownRqDownRule] =>
          rule_rsrq; apply rsDownRqDownRule_RsDownRqDownRule; auto
        end
      | |- parentIdxOf _ _ = Some _ =>
        apply subtreeChildrenIndsOf_parentIdxOf; auto; fail
      end.

  Lemma mesi_impl_GoodRqRsSys: GoodRqRsSys topo impl.
  Proof.
    repeat
      match goal with
      | [ |- GoodRqRsSys _ _] => red
      | [ |- GoodRqRsObj _ _ _] => red
      | [ |- Forall _ _] => constructor; simpl
      end.

    apply Forall_forall; intros obj ?.
    apply in_app_or in H; destruct H.

    - (* Li caches *)
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; simpl.
      repeat
        match goal with
        | |- Forall _ (_ ++ _) => apply Forall_app
        | |- Forall _ (_ :: _) => constructor
        | |- Forall _ nil => constructor
        end; try (solve_GoodRqRsRule; fail).

      1: {
        apply Forall_forall; intros.
        unfold liRulesFromChildren in H.
        apply concat_In in H; dest.
        apply in_map_iff in H; dest; subst.
        dest_in; try (solve_GoodRqRsRule; fail).

        1: {
          rule_rquu.
          solve_GoodRqRsRule.
          eapply rqUpUpRule_RqFwdRule; eauto.
          
        
      }
          

    - (* L1 caches *)
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; simpl.
      repeat
        match goal with
        | |- Forall _ (_ ++ _) => apply Forall_app
        | |- Forall _ (_ :: _) => constructor
        | |- Forall _ nil => constructor
        end; try (solve_GoodRqRsRule; fail).
      
  Admitted.

End System.

