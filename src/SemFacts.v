Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Theorem refines_refl:
  forall step sys, step # step |-- sys ⊑[id] sys.
Proof.
  unfold Refines; intros.
  replace (map id hst) with hst; [assumption|].
  clear; induction hst; simpl; auto.
  f_equal; auto.
Qed.

Theorem refines_trans:
  forall step1 step2 step3 s1 s2 s3 p q,
    step1 # step2 |-- s1 ⊑[p] s2 ->
    step2 # step3 |-- s2 ⊑[q] s3 ->
    step1 # step3 |-- s1 ⊑[fun l => q (p l)] s3.
Proof.
  unfold Refines; intros.
  specialize (H0 _ (H _ H1)).
  replace (map _ hst) with (map q (map p hst)); [assumption|].
  clear; induction hst; simpl; auto.
  f_equal; auto.
Qed.
  
