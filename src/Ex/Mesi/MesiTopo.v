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

  Local Definition topo := fst (tree2Topo tr 0).
  Local Definition cifc := snd (tree2Topo tr 0).
  Local Definition impl := impl tr.

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
    match goal with
    | |- GoodRqRsRule _ _ _ _ =>
      match goal with
      (* | |- context[rqUpDownRule] *)
      (* | |- context[rqDownDownRule] *)
      (* | |- context[rsDownRqDownRule] *)
      | |- context[immDownRule] => rule_immd; auto
      | |- context[immUpRule] => rule_immu; auto
      | |- context[rqUpUpRule] => rule_rquu; auto
      | |- context[rqUpUpRuleS] => rule_rqsu; auto
      | |- context[rsDownDownRule] => rule_rsdd; auto
      | |- context[rsDownDownRuleS] => rule_rsds; auto
      | |- context[rsUpDownRule] => rule_rsu; auto
      | |- context[rsUpUpRule] => rule_rsu; auto
      end
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
      all: admit.

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

