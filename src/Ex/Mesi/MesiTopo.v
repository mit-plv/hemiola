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

Section System.
  Variable tr: tree.
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).
  Let impl := impl Htr.

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

  Lemma mesi_GoodRqRsSys: GoodRqRsSys topo impl.
  Proof.
    repeat
      match goal with
      | [ |- GoodRqRsSys _ _] => red
      | [ |- GoodRqRsObj _ _ _] => red
      | [ |- Forall _ _] => simpl; constructor; simpl
      end.

    - (* Main memory, the root *)
      admit.

    - apply Forall_forall; intros obj ?.
      apply in_app_or in H; destruct H.

      + (* Li caches *)
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
            apply c_li_indices_tail_has_parent in H0; [|assumption].
            dest.
            eapply rqUpUpRule_RqFwdRule; eauto.
            apply subtreeChildrenIndsOf_parentIdxOf; auto.
          }
          3: {
            rule_rquu.
            solve_GoodRqRsRule.
            apply c_li_indices_tail_has_parent in H0; [|assumption].
            dest.
            eapply rqUpUpRule_RqFwdRule; eauto.
            apply subtreeChildrenIndsOf_parentIdxOf; auto.
          }
          all: admit.
        }
        all: admit.

      + (* L1 caches *)
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

  Lemma mesi_GoodRqRsInterfSys: GoodRqRsInterfSys topo impl.
  Proof.
  Admitted.

  Lemma mesi_RqRsSys: RqRsSys topo impl.
  Proof.
    red; repeat ssplit.
    - apply mesi_RqRsDTree.
    - apply mesi_GoodRqRsSys.
    - apply mesi_GoodRqRsInterfSys.
  Qed.  
  
End System.

Hint Resolve mesi_GoodORqsInit mesi_WfDTree mesi_RqRsDTree mesi_RqRsSys.

