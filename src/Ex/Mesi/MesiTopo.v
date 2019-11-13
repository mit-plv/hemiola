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

