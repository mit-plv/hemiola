Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector ListSupport Syntax Topology Semantics.
Require Import RqRsLang.

Require Import Spec SpecSv Msi MsiSv.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Lemma msiSv_topo_wf: WfDTree topo.
Proof.
  split.
  - compute; repeat constructor; firstorder.
  - compute; repeat constructor; firstorder.
Qed.

Lemma msiSv_impl_RqRsChnsOnDTree: RqRsChnsOnDTree topo.
Proof.
  red; intros.
  pose proof (parentChnsOf_Some_in_tree msiSv_topo_wf _ _ H).
  dest_in; try (inv H; eauto).
Qed.
  
Lemma msiSv_impl_RqRsChnsOnSystem: RqRsChnsOnSystem topo impl.
Proof.
  red; intros.
  dest_in.
  - inv H0; split; try (red; intros; dest_in; simpl; tauto).
  - inv H0; split; try (red; intros; dest_in; simpl; tauto).
  - inv H0; split; try (red; intros; dest_in; simpl; tauto).
Qed.

Lemma msiSv_impl_ExtsOnDTree: ExtsOnDTree topo impl.
Proof.
  split.
  - red; intros; dest_in.
    + exists ext1Idx; reflexivity.
    + exists ext2Idx; reflexivity.
  - red; intros; dest_in.
    + exists ext1Idx; reflexivity.
    + exists ext2Idx; reflexivity.
Qed.
  
Lemma msiSv_impl_RqRsDTree: RqRsDTree topo impl.
Proof.
  red; repeat ssplit.
  - auto using msiSv_topo_wf.
  - auto using msiSv_impl_RqRsChnsOnDTree.
  - auto using msiSv_impl_RqRsChnsOnSystem.
  - auto using msiSv_impl_ExtsOnDTree.
Qed.

Local Hint Unfold upRq downRq : RuleConds.

Lemma msiSv_impl_GoodExtRssSys: GoodExtRssSys impl.
Proof.
  repeat constructor;
    try (red; intros; solve_rule_conds_const;
         repeat
           (try match goal with
                | [H: _ \/ _ |- _] => destruct H
                end;
            simpl in *; subst; try discriminate; auto); fail).
Qed.

Lemma msiSv_impl_RqUpRsUpOkSys: RqUpRsUpOkSys topo impl.
Proof.
  repeat
    match goal with
    | [ |- RqUpRsUpOkSys _ _] => red
    | [ |- RqUpRsUpOkObj _ _] => red
    | [ |- Forall _ _] => constructor; simpl
    end.

  - intros; red; intros.
    phide H1.
    dest_in;
      try (exfalso; phide_clear; clear H2 H5 rsUpRule; solve_rule_conds_ex; fail).
    + preveal H6.
      dest_in;
        try (exfalso; clear H0 H3 H4;
               match goal with
               | [H: rule_precond ?r ?ost ?orq ?ins |- _] =>
                 let trs := fresh "trs" in
                 let Htrs := fresh "Htrs" in
                 let nost := fresh "nost" in
                 let norq := fresh "norq" in
                 let outs := fresh "outs" in
                 remember (rule_trs r ost orq ins) as trs eqn:Htrs;
                   destruct trs as [[nost norq] outs];
                   apply eq_sym in Htrs
               end;
               destruct H2; solve_rule_conds_ex; fail).
      * exfalso; solve_rule_conds_const.
        rewrite H18 in H14.
        unfold msiI, msiS in H14; omega.
      * solve_rule_conds_const.

    + preveal H6.
      dest_in;
        try (exfalso; clear H0 H3 H4;
               match goal with
               | [H: rule_precond ?r ?ost ?orq ?ins |- _] =>
                 let trs := fresh "trs" in
                 let Htrs := fresh "Htrs" in
                 let nost := fresh "nost" in
                 let norq := fresh "norq" in
                 let outs := fresh "outs" in
                 remember (rule_trs r ost orq ins) as trs eqn:Htrs;
                   destruct trs as [[nost norq] outs];
                   apply eq_sym in Htrs
               end;
               destruct H2; solve_rule_conds_ex; fail).
      * solve_rule_conds_const.
      * solve_rule_conds_const.

    + preveal H6.
      dest_in;
        try (exfalso; clear H0 H3 H4;
               match goal with
               | [H: rule_precond ?r ?ost ?orq ?ins |- _] =>
                 let trs := fresh "trs" in
                 let Htrs := fresh "Htrs" in
                 let nost := fresh "nost" in
                 let norq := fresh "norq" in
                 let outs := fresh "outs" in
                 remember (rule_trs r ost orq ins) as trs eqn:Htrs;
                   destruct trs as [[nost norq] outs];
                   apply eq_sym in Htrs
               end;
               destruct H2; solve_rule_conds_ex; fail).
      * solve_rule_conds_const.
      * solve_rule_conds_const.

  - intros; red; intros.
    phide H1.
    dest_in;
      try (exfalso; phide_clear; clear H2 H5 rsUpRule; solve_rule_conds_ex; fail).
    + preveal H6.
      dest_in;
        try (exfalso; clear H0 H3 H4;
               match goal with
               | [H: rule_precond ?r ?ost ?orq ?ins |- _] =>
                 let trs := fresh "trs" in
                 let Htrs := fresh "Htrs" in
                 let nost := fresh "nost" in
                 let norq := fresh "norq" in
                 let outs := fresh "outs" in
                 remember (rule_trs r ost orq ins) as trs eqn:Htrs;
                   destruct trs as [[nost norq] outs];
                   apply eq_sym in Htrs
               end;
               destruct H2; solve_rule_conds_ex; fail).
      * solve_rule_conds_const.
        rewrite H18 in H14.
        unfold msiI, msiS in H14; omega.
      * solve_rule_conds_const.

    + preveal H6.
      dest_in;
        try (exfalso; clear H0 H3 H4;
               match goal with
               | [H: rule_precond ?r ?ost ?orq ?ins |- _] =>
                 let trs := fresh "trs" in
                 let Htrs := fresh "Htrs" in
                 let nost := fresh "nost" in
                 let norq := fresh "norq" in
                 let outs := fresh "outs" in
                 remember (rule_trs r ost orq ins) as trs eqn:Htrs;
                   destruct trs as [[nost norq] outs];
                   apply eq_sym in Htrs
               end;
               destruct H2; solve_rule_conds_ex; fail).
      * solve_rule_conds_const.
      * solve_rule_conds_const.

    + preveal H6.
      dest_in;
        try (exfalso; clear H0 H3 H4;
               match goal with
               | [H: rule_precond ?r ?ost ?orq ?ins |- _] =>
                 let trs := fresh "trs" in
                 let Htrs := fresh "Htrs" in
                 let nost := fresh "nost" in
                 let norq := fresh "norq" in
                 let outs := fresh "outs" in
                 remember (rule_trs r ost orq ins) as trs eqn:Htrs;
                   destruct trs as [[nost norq] outs];
                   apply eq_sym in Htrs
               end;
               destruct H2; solve_rule_conds_ex; fail).
      * solve_rule_conds_const.
      * solve_rule_conds_const.

  - intros; red; intros.
    phide H1.
    dest_in;
      try (exfalso; phide_clear; clear H2 H5 rsUpRule; solve_rule_conds_ex; fail).
Qed.

Local Hint Unfold RulePrecSat RulePostSat : RuleConds.

Lemma msiSv_impl_GoodRqRsSys: GoodRqRsSys topo impl.
Proof.
  repeat
    match goal with
    | [ |- GoodRqRsSys _ _] => red
    | [ |- GoodRqRsObj _ _ _] => red
    | [ |- Forall _ _] => constructor; simpl
    end.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= ext1Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext1Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds_const.

  - rule_immu; solve_rule_conds_const.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= ext1Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext1Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds_const.

  - rule_immu; solve_rule_conds_const.

  - rule_rquu; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext1Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds_const.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= ext2Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext2Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds_const.

  - rule_immu; solve_rule_conds_const.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= ext2Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext2Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds_const.

  - rule_immu; solve_rule_conds_const.

  - rule_rquu; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext2Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds_const.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= child1Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + instantiate (1:= child2Idx) in H; discriminate.
    + reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= child1Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + instantiate (1:= child2Idx) in H; discriminate.
    + reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= child1Idx).
    all:reflexivity.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= child2Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + right; left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + instantiate (1:= child1Idx) in H; discriminate.
    + reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= child2Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds_const.
    + intros; destruct (hd_error mins); simpl; auto.
    + right; left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + instantiate (1:= child1Idx) in H; discriminate.
    + reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_immd; solve_rule_conds_const.
    instantiate (1:= child2Idx).
    all:reflexivity.

  - rule_rsu; solve_rule_conds_const.

  - rule_rsu; solve_rule_conds_const.
Qed.

Theorem msiSv_impl_RqRsSys: RqRsSys topo impl.
Proof.
  red; repeat ssplit.
  - auto using msiSv_impl_RqRsDTree.
  - auto using msiSv_impl_GoodRqRsSys.
  - split.
    + auto using msiSv_impl_RqUpRsUpOkSys.
    + auto using msiSv_impl_GoodExtRssSys.
Qed.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

