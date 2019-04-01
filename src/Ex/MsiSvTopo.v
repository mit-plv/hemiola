Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.

Require Import Spec SpecSv Msi MsiSv.

Lemma msiSv_topo_wf: WfDTree topo.
Proof.
  split.
  - compute; repeat constructor; firstorder.
  - compute; repeat constructor; firstorder.
Qed.

Lemma msiSv_impl_RqRsChnsOnDTree: RqRsChnsOnDTree topo impl.
Proof.
  (** TODO: extensionality for [DTree] w.r.t. [oidx] *)
Admitted.

Lemma msiSv_impl_RqRsDTree: RqRsDTree topo impl.
Proof.
  split.
  - auto using msiSv_topo_wf.
  - auto using msiSv_impl_RqRsChnsOnDTree.
Qed.

Ltac solve_rule_conds :=
  repeat
    (autounfold with RuleConds in *; intros;
     match goal with
     | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
     | [H: rule_precond _ _ _ _ |- _] => simpl in H
     | [H: rule_trs _ _ _ _ = _ |- _] => simpl in H
     | [H: (_, _) = (_, _) |- _] => inv H
     | [H: idsOf ?rins = [_]%list |- _] =>
       let rin := fresh "rin" in
       let rmsg := fresh "rmsg" in
       destruct rins as [|[rin rmsg] [|]]; try discriminate;
       simpl in H; inv H
     | [H: map _ _ = [_]%list |- _] => simpl in H; inv H
     | [H: context [hd_error [_]%list] |- _] => simpl in H

     | [ |- rule_precond _ _ _ _] => simpl
     | [ |- (_ /\oprec _) _ _ _] => split
     | [ |- _ /\ _] => split
     | [ |- _ ->oprec _] => red; intros
     | [ |- Forall _ _] => constructor
     | [ |- exists _, _] => eexists
     end;
     simpl in *;
     try assumption; try reflexivity; try congruence).

Ltac rule_immd := left.
Ltac rule_immu := right; left.
Ltac rule_rquu := do 2 right; left; split; [|left].
Ltac rule_rqud := do 2 right; left; split; [|right; left].
Ltac rule_rqdd := do 2 right; left; split; [|right; right].
Ltac rule_rsdd := do 3 right; left; split; [left|].
Ltac rule_rsu := do 3 right; left; split; [right|].
Ltac rule_rsrq := do 4 right.

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

Admitted.

Lemma msiSv_impl_RqUpRsUpOkSys: RqUpRsUpOkSys topo impl.
Proof.
  repeat
    match goal with
    | [ |- RqUpRsUpOkSys _ _] => red
    | [ |- RqUpRsUpOkObj _ _] => red
    | [ |- Forall _ _] => constructor; simpl
    end.

Admitted.

Theorem msiSv_impl_RqRsSys: RqRsSys topo impl.
Proof.
  red; repeat ssplit.
  - auto using msiSv_impl_RqRsDTree.
  - auto using msiSv_impl_GoodRqRsSys.
  - auto using msiSv_impl_RqUpRsUpOkSys.
Qed.

