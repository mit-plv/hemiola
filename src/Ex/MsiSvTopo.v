Require Import Bool Vector List String Peano_dec Omega.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo RqRsLang RqRsFacts.

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
  Common.dest_in; try (inv H; eauto).
Qed.
  
Lemma msiSv_impl_RqRsChnsOnSystem: RqRsChnsOnSystem topo impl.
Proof.
  red; intros.
  Common.dest_in.
  - inv H0; split; try (red; intros; Common.dest_in; simpl; tauto).
  - inv H0; split; try (red; intros; Common.dest_in; simpl; tauto).
  - inv H0; split; try (red; intros; Common.dest_in; simpl; tauto).
Qed.

Lemma msiSv_impl_ExtsOnDTree: ExtsOnDTree topo impl.
Proof.
  split.
  - red; intros; Common.dest_in.
    + exists ext1Idx; reflexivity.
    + exists ext2Idx; reflexivity.
  - red; intros; Common.dest_in.
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

Hint Unfold upRq downRq : RuleConds.

Ltac solve_rule_conds_step :=
  repeat autounfold with RuleConds in *; intros;
  try
    match goal with
    | [H: context [match msg_value ?msg with
                   | VNat _ => True
                   | _ => _
                   end] |- _] =>
      let Hmsg := fresh "Hmsg" in
      destruct (msg_value msg) eqn:Hmsg; try (exfalso; auto; fail); simpl in *
    | [H: ?orq@[?i] <> None |- _] =>
      let rqi := fresh "rqi" in
      let Horq := fresh "Horq" in
      destruct (orq@[i]) as [rqi|] eqn:Horq;
      [clear H; simpl in *|exfalso; auto]
    | [H: context [(?orq@[?i]) >>=[False] (fun _ => _)] |- _] =>
      let rqiu := fresh "rqiu" in
      let Horq := fresh "Horq" in
      destruct (orq@[i]) as [rqiu|] eqn:Horq;
      [simpl in *|exfalso; auto]
    | [H1: ?t = _, H2: context[?t] |- _] =>
      match type of t with
      | option _ => rewrite H1 in H2; simpl in H2
      | Value => rewrite H1 in H2; simpl in H2
      end
                                                                            
    | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
    | [H: rule_precond _ _ _ _ |- _] => progress simpl in H
    | [H: rule_trs _ _ _ _ = _ |- _] => progress simpl in H
    | [H: (_, _) = (_, _) |- _] => inv H
    | [H: idsOf ?rins = [_]%list |- _] =>
      let rin := fresh "rin" in
      let rmsg := fresh "rmsg" in
      destruct rins as [|[rin rmsg] [|]]; try discriminate;
      simpl in H; inv H
    | [H: idsOf [_] = [_]%list |- _] => simpl in H; inv H
    | [H: map msg_id (valsOf ?rins) = [_]%list |- _] =>
      let rin := fresh "rin" in
      let rmsg := fresh "rmsg" in
      destruct rins as [|[rin rmsg] [|]]; try discriminate;
      simpl in H; inv H
    | [H: map msg_id (valsOf [_]%list) = [_]%list |- _] => simpl in H; inv H
    | [H: map _ [_]%list = [_]%list |- _] => progress simpl in H
    | [H: context [hd_error [_]%list] |- _] => progress simpl in H
    | [H: [_]%list = [_]%list |- _] => inv H
    | [H: Forall _ [_]%list |- _] => inv H
    | [H: Forall _ nil |- _] => clear H
    | [ |- rule_precond _ _ _ _] => progress simpl
    | [ |- (_ /\oprec _) _ _ _] => split
    | [ |- _ /\ _] => split
    | [ |- _ ->oprec _] => red; intros
    | [ |- Forall _ _] => constructor
    | [ |- exists _, _] => eexists
    end;
  simpl in *;
  try first [assumption
            |reflexivity
            |discriminate
            |congruence
            |(mred; fail)].

Ltac solve_rule_conds := repeat solve_rule_conds_step.

Ltac rule_immd := left.
Ltac rule_immu := right; left.
Ltac rule_rquu := do 2 right; left; split; [|left].
Ltac rule_rqud := do 2 right; left; split; [|right; left].
Ltac rule_rqdd := do 2 right; left; split; [|right; right].
Ltac rule_rsdd := do 3 right; left; split; [left|].
Ltac rule_rsu := do 3 right; left; split; [right|].
Ltac rule_rsrq := do 4 right.

Lemma msiSv_impl_GoodExtRssSys: GoodExtRssSys impl.
Proof.
  repeat constructor;
    try (red; intros; disc_rule_conds; solve_rule_conds;
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
    Common.dest_in;
      try (exfalso; phide_clear;
             clear H2 H5 rsUpRule;
             repeat (autounfold with RuleConds in *; dest);
             disc_rule_conds; dest;
             solve_rule_conds;
             fail).
    + preveal H6.
      Common.dest_in;
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
               destruct H2;
               try (repeat (autounfold with RuleConds in *; dest);
                      repeat (disc_rule_conds; dest; solve_rule_conds));
               fail).
      * solve_rule_conds.
        rewrite H11 in H7.
        unfold msiI, msiS in H7; omega.
      * solve_rule_conds.

    + preveal H6.
      Common.dest_in;
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
               destruct H2;
               try (repeat (autounfold with RuleConds in *; dest);
                      repeat (disc_rule_conds; dest; solve_rule_conds));
               fail).
      * solve_rule_conds.
      * solve_rule_conds.

    + preveal H6.
      Common.dest_in;
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
               destruct H2;
               try (repeat (autounfold with RuleConds in *; dest);
                      repeat (disc_rule_conds; dest; solve_rule_conds));
               fail).
      * solve_rule_conds.
      * solve_rule_conds.

  - intros; red; intros.
    phide H1.
    Common.dest_in;
      try (exfalso; phide_clear;
             clear H2 H5 rsUpRule;
             repeat (autounfold with RuleConds in *; dest);
             disc_rule_conds; dest;
             solve_rule_conds;
             fail).
    + preveal H6.
      Common.dest_in;
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
               destruct H2;
               try (repeat (autounfold with RuleConds in *; dest);
                      repeat (disc_rule_conds; dest; solve_rule_conds));
               fail).
      * solve_rule_conds.
        rewrite H11 in H7.
        unfold msiI, msiS in H7; omega.
      * solve_rule_conds.

    + preveal H6.
      Common.dest_in;
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
               destruct H2;
               try (repeat (autounfold with RuleConds in *; dest);
                      repeat (disc_rule_conds; dest; solve_rule_conds));
               fail).
      * solve_rule_conds.
      * solve_rule_conds.

    + preveal H6.
      Common.dest_in;
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
               destruct H2;
               try (repeat (autounfold with RuleConds in *; dest);
                      repeat (disc_rule_conds; dest; solve_rule_conds));
               fail).
      * solve_rule_conds.
      * solve_rule_conds.

  - intros; red; intros.
    phide H1.
    Common.dest_in;
      try (exfalso; phide_clear;
             clear H2 H5 rsUpRule;
             repeat (autounfold with RuleConds in *; dest);
             disc_rule_conds; dest;
             solve_rule_conds;
             fail).
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

  - rule_immd; solve_rule_conds.
    instantiate (1:= ext1Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext1Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds.

  - rule_immu; solve_rule_conds.

  - rule_immd; solve_rule_conds.
    instantiate (1:= ext1Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext1Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds.

  - rule_immu; solve_rule_conds.

  - rule_rquu; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext1Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds.

  - rule_immd; solve_rule_conds.
    instantiate (1:= ext2Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext2Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds.

  - rule_immu; solve_rule_conds.

  - rule_immd; solve_rule_conds.
    instantiate (1:= ext2Idx).
    all:reflexivity.

  - rule_rquu; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext2Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds.

  - rule_immu; solve_rule_conds.

  - rule_rquu; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + instantiate (1:= ext2Idx).
      reflexivity.
    + reflexivity.
    + reflexivity.

  - rule_rsdd; solve_rule_conds.

  (* the parent *)
      
  - rule_immd; solve_rule_conds.
    instantiate (1:= child1Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + discriminate.
    + reflexivity.
    + repeat constructor.
      exists child2Idx.
      repeat split.
      discriminate.

  - rule_immd; solve_rule_conds.
    instantiate (1:= child1Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + discriminate.
    + reflexivity.
    + repeat constructor.
      exists child2Idx.
      repeat split.
      discriminate.

  - rule_immd; solve_rule_conds.
    instantiate (1:= child1Idx).
    all:reflexivity.

  - rule_immd; solve_rule_conds.
    instantiate (1:= child2Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + right; left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + discriminate.
    + reflexivity.
    + repeat constructor.
      exists child1Idx.
      repeat split.
      discriminate.

  - rule_immd; solve_rule_conds.
    instantiate (1:= child2Idx).
    all:reflexivity.

  - rule_rqud; solve_rule_conds.
    + intros; destruct (hd_error mins); simpl; auto.
    + right; left; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + discriminate.
    + reflexivity.
    + repeat constructor.
      exists child1Idx.
      repeat split.
      discriminate.

  - rule_immd; solve_rule_conds.
    instantiate (1:= child2Idx).
    all:reflexivity.

  - rule_rsu; solve_rule_conds.

  - rule_rsu; solve_rule_conds.

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

