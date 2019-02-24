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

Lemma msiSv_impl_GoodRqRsSys: GoodRqRsSys topo impl.
Proof.
  repeat
    match goal with
    | [ |- GoodRqRsSys _ _] => red
    | [ |- Forall _ _] => constructor; simpl
    | [ |- GoodRqRsObj _ _ _] => red
    end.

  - left.
    repeat
      (match goal with
       | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
       | [H: rule_precond _ _ _ _ |- _] => simpl in H
       | [H: rule_trs _ _ _ _ = _ |- _] => simpl in H
       | [H: (_, _) = (_, _) |- _] => inv H

       | [ |- RulePrecSat _ _] => red
       | [ |- RulePostSat _ _] => red; intros
       | [ |- RsReleasing _] => red
       | [ |- FootprintSilent _] => red
       | [ |- ImmDownRule _ _ _] => red
       | [ |- ImmDownOk _ _ _ _ _ _ _ _] => red

       | [ |- _ /\ _] => split
       | [ |- _ ->oprec _] => red; intros
       | [ |- Forall _ _] => constructor
       end; try assumption; try reflexivity).

    red in H.
    destruct rins as [|[midx msg] [|]]; try discriminate.
    inv H.
    
    exists ext1Idx; do 4 eexists; repeat ssplit; try reflexivity.
  - 
    
Admitted.

Lemma msiSv_impl_RqUpRsUpOkSys: RqUpRsUpOkSys topo impl.
Proof.
Admitted.

Theorem msiSv_impl_RqRsSys: RqRsSys topo impl.
Proof.
  red; repeat ssplit.
  - auto using msiSv_impl_RqRsDTree.
  - auto using msiSv_impl_GoodRqRsSys.
  - auto using msiSv_impl_RqUpRsUpOkSys.
Qed.

