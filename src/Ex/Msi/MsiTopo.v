Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport IndexSupport.
Require Import Syntax Topology Semantics Invariant.
Require Import RqRsLang.

Require Import Ex.Spec Ex.SpecInds Ex.Template Ex.Msi.
Require Import Ex.Msi.Msi Ex.Msi.MsiObjInv.

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

  Lemma msi_indices:
    map obj_idx (sys_objs impl) = c_li_indices cifc ++ c_l1_indices cifc.
  Proof.
    simpl; rewrite c_li_indices_head_rootOf at 2 by assumption.
    simpl; f_equal.
    rewrite map_app, map_map, map_id; simpl.
    rewrite map_map, map_id; reflexivity.
  Qed.

  Lemma msi_GoodORqsInit: GoodORqsInit (initsOf impl).
  Proof.
    apply initORqs_GoodORqsInit.
  Qed.

  Lemma msi_WfDTree: WfDTree topo.
  Proof.
    apply tree2Topo_WfDTree.
  Qed.

  Lemma msi_RqRsChnsOnDTree: RqRsChnsOnDTree topo.
  Proof.
    apply tree2Topo_RqRsChnsOnDTree.
  Qed.

  Lemma msi_RqRsChnsOnSystem: RqRsChnsOnSystem topo impl.
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

  Lemma msi_ExtsOnDTree: ExtsOnDTree topo impl.
  Proof.
    eapply tree2Topo_ExtsOnDTree with (tr0:= tr) (bidx:= [0]); try reflexivity.
    destruct (tree2Topo _ _); reflexivity.
  Qed.

  Lemma msi_RqRsDTree: RqRsDTree topo impl.
  Proof.
    red; repeat ssplit.
    - auto using msi_WfDTree.
    - auto using msi_RqRsChnsOnDTree.
    - auto using msi_RqRsChnsOnSystem.
    - auto using msi_ExtsOnDTree.
  Qed.

  Ltac solve_GoodRqRsRule_unfold ::= autounfold with MsiRules.

  Lemma msi_GoodRqRsSys: GoodRqRsSys topo impl.
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

      apply Forall_forall; intros.
      unfold liRulesFromChildren in H.
      apply concat_In in H; dest.
      apply in_map_iff in H; dest; subst.
      dest_in.
      all: try (solve_GoodRqRsRule; fail).

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

        { (* [liGetSRqUpDownM] *)
          apply subtreeChildrenIndsOf_parentIdxOf in H3; [|apply tree2Topo_WfDTree].
          pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H0) H3).
          rewrite <-msi_indices in H1.

          rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

          (** [RqUpDownSound] *)
          red; simpl; intros; dest.
          apply subtreeChildrenIndsOf_parentIdxOf in H4; [|apply tree2Topo_WfDTree].
          repeat ssplit; [discriminate| |intuition auto].
          repeat constructor; try assumption.
        }

        { (* [liGetMRqUpDownM] *)
          apply subtreeChildrenIndsOf_parentIdxOf in H3; [|apply tree2Topo_WfDTree].
          pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H0) H3).
          rewrite <-msi_indices in H1.

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
          rewrite <-msi_indices in H1.

          rule_rqud; eapply rqUpDownRule_RqFwdRule; eauto.

          (** [RqUpDownSound] *)
          red; simpl; intros; dest.
          repeat ssplit.
          { assumption. }
          { apply Forall_forall; intros.
            apply in_remove in H9.
            apply H4 in H9.
            eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
          }
          { apply remove_In. }
        }
      }

      { (* [liDownSRqDownDownM] *)
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
        unfold getUpLockIdxBackI, getUpLockIdxBack in *.
        destruct (orq@[upRq]) as [rqiu|]; simpl in *; auto.
        destruct H1 as [rcidx [rqUp ?]]; dest.
        pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H0) H1).
        rewrite <-msi_indices in H9.
        intros; rewrite H11 in *.
        repeat ssplit.
        { assumption. }
        { apply Forall_forall; intros.
          apply in_remove in H12.
          apply H3 in H12.
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

      { (* [liDownIRqDownDownDirM] *)
        rule_rqdd.
        eapply rqDownDownRule_RqFwdRule; eauto.

        (** [RqDownDownSound] *)
        red; simpl; intros; dest.
        repeat ssplit; [discriminate|].
        repeat constructor.
        eapply subtreeChildrenIndsOf_parentIdxOf; eauto.
      }

      { (* [liDownIRqDownDownDirMS] *)
        rule_rqdd.
        eapply rqDownDownRule_RqFwdRule; eauto.

        (** [RqDownDownSound] *)
        red; simpl; intros; dest.
        repeat ssplit; [assumption|].
        apply Forall_forall; intros.
        apply H2 in H4.
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

  Ltac exfalso_RqToUpRule_unfold ::= repeat autounfold with MsiRules in *.
  Ltac exfalso_RsToUpRule_unfold ::= repeat autounfold with MsiRules in *.
  Ltac disc_rule_custom ::= disc_msi_obj_invs.

  Lemma msi_RqUpRsUpOkSys: RqUpRsUpOkSys topo impl (MsiObjInvs topo).
  Proof. (* SKIP_PROOF_ON
    repeat
      match goal with
      | |- RqUpRsUpOkSys _ _ _ => red
      | |- Forall _ _ => simpl; constructor; simpl
      | |- Forall _ (_ ++ _) => apply Forall_app
      end.

    - (** The main memory: no RqUp rules *)
      red; intros.
      simpl in H; unfold liRulesFromChildren in H.
      apply concat_In in H; dest.
      apply in_map_iff in H; dest; subst.
      dest_in.
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
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; auto.
          { destruct H17; dest; try solve [congruence|solve_msi]. }
          { destruct H17; dest; try solve [congruence|solve_msi]. }
        }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; auto.
          { solve_msi. }
          { f_equal; apply M.add_remove_comm; discriminate. }
        }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; auto.
          { solve_msi. }
          { f_equal; apply M.add_remove_comm; discriminate. }
        }

      + simpl in H2; apply in_app_or in H2; destruct H2;
          [unfold liRulesFromChildren in H;
           apply concat_In in H; dest;
           apply in_map_iff in H; dest; subst;
           dest_in|dest_in].
        all: try (exfalso_RsToUpRule; fail).

        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex.
          all: try (destruct H17; dest; try solve [congruence|solve_msi]).
        }
        { clear; solve_rule_conds_ex.
          all: try (destruct H17; dest; try solve [congruence|solve_msi]).
        }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; try solve_msi.
          f_equal; apply M.add_remove_comm; discriminate.
        }
        { clear; solve_rule_conds_ex; try solve_msi. }
        { clear; solve_rule_conds_ex; try solve_msi.
          f_equal; apply M.add_remove_comm; discriminate.
        }

      + simpl in H2; apply in_app_or in H2; destruct H2;
          [unfold liRulesFromChildren in H;
           apply concat_In in H; dest;
           apply in_map_iff in H; dest; subst;
           dest_in|dest_in].
        all: try (exfalso_RsToUpRule; fail).

        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_const; try solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_const; try solve_msi.
          all: rewrite invalidate_I; solve_msi.
        }
        { clear; solve_rule_conds_const; try solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }

      + simpl in H2; apply in_app_or in H2; destruct H2;
          [unfold liRulesFromChildren in H;
           apply concat_In in H; dest;
           apply in_map_iff in H; dest; subst;
           dest_in|dest_in].
        all: try (exfalso_RsToUpRule; fail).

        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_const; try intuition solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_const; try intuition solve_msi.
          rewrite invalidate_I; [|solve_msi].
          intuition solve_msi.
        }
        { clear; solve_rule_conds_const; try intuition solve_msi. }
        { clear; solve_rule_conds_ex; solve_msi. }
        { clear; solve_rule_conds_ex; try intuition solve_msi. }
        { clear; solve_rule_conds_ex; try intuition solve_msi. }

    - (** L1 cache *)
      apply Forall_forall; intros.
      apply in_map_iff in H.
      destruct H as [oidx [? ?]]; subst.
      red; intros.

      phide H2; dest_in.
      all: try (exfalso_RqToUpRule; fail).

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const; solve_msi. }
        { clear; solve_rule_conds_const; auto. }
        { clear; solve_rule_conds_const; auto. }

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const. }
        { clear; solve_rule_conds_const; solve_msi. }
        { clear; solve_rule_conds_const; solve_msi. }

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const; try solve_msi. }
        { clear; solve_rule_conds_const.
          all: rewrite invalidate_I; solve_msi.
        }
        { clear; solve_rule_conds_const; try solve_msi. }

      + preveal H4; dest_in.
        all: try (exfalso_RsToUpRule; fail).
        { clear; solve_rule_conds_const; try solve_msi. }
        { clear; solve_rule_conds_const.
          rewrite invalidate_I; solve_msi.
        }
        { clear; solve_rule_conds_const.
          rewrite invalidate_I; solve_msi.
        }

        END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma msi_GoodExtRssSys: GoodExtRssSys impl.
  Proof. (* SKIP_PROOF_ON
    red; simpl.
    constructor; [|apply Forall_app].
    - (** the main memory *)
      red; simpl.
      apply Forall_forall; intros.
      unfold memRulesFromChildren in H.
      apply concat_In in H; dest.
      apply in_map_iff in H; dest; subst.
      dest_in.
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
          apply in_remove in H12.
          apply H5 in H12.
          simpl in *; solve_GoodExtRssSys.
        }

      + repeat constructor.
        all: try (red; simpl; disc_rule_conds_ex; solve_GoodExtRssSys; fail).
        { (* [liGetMRsDownRqDownDirS] *)
          red; simpl; disc_rule_conds_ex.
          apply in_map_iff in H2; dest; subst.
          apply in_remove in H5.
          apply H11 in H5.
          simpl in *; solve_GoodExtRssSys.
        }
        { (* [liDownIRqDownDownDirS] *)
          red; simpl; disc_rule_conds_ex.
          apply in_map_iff in H2; dest; subst.
          apply H4 in H7.
          simpl in *; solve_GoodExtRssSys.
        }
        { (* [liDownIRqDownDownDirMS] *)
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

      END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma msi_GoodRqRsInterfSys: GoodRqRsInterfSys topo impl (MsiObjInvs topo).
  Proof.
    split.
    - apply msi_RqUpRsUpOkSys.
    - apply msi_GoodExtRssSys.
  Qed.

  Lemma msi_RqRsSys: RqRsSys topo impl (MsiObjInvs topo).
  Proof.
    red; repeat ssplit.
    - apply msi_RqRsDTree.
    - apply msi_GoodRqRsSys.
    - apply msi_GoodRqRsInterfSys.
  Qed.

End System.

#[global] Hint Resolve msi_GoodORqsInit msi_WfDTree msi_RqRsDTree msi_RqRsSys.
