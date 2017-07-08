Require Import List String Peano_dec.
Require Import FnMap Language SingleValue.

Ltac inv H := inversion H; subst; clear H.
Ltac dest_in :=
  repeat
    match goal with
    | [H: In _ _ |- _] => inv H
    end.

Lemma parent_sequential:
  forall hst,
    HistoryOf (existT (fun st => Object SingleValueMsg st) ParentState parent :: nil) hst ->
    Sequential hst.
Proof.
  unfold HistoryOf; intros.
  destruct H as [oss [oims ?]].
Admitted.
  
Lemma parent_linear:
  Linear (existT (fun st => Object SingleValueMsg st) ParentState parent :: nil).
Proof.
  unfold Linear; intros.
  exists (complete hst); split; auto.
  - admit. (* HistoryOf hst -> HistoryOf (complete hst) *)
  - unfold Linearlizable'; split; auto.
    apply sequential_complete.
    apply parent_sequential; auto.
Admitted.

Lemma child_linear: forall i,
    Linear (existT (fun st => Object SingleValueMsg st) ChildState (child i) :: nil).
Proof.
Admitted.

Theorem impl_linear: ExtLinear impl.
Proof.
  apply extLinear_local.
  intros; dest_in.
  - apply parent_linear.
  - apply child_linear.
  - apply child_linear.
Qed.  

