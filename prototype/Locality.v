Require Import Bool List String Peano_dec.
Require Import FMap Language Transaction Monotone.

Section Facts.
  Context {MsgT ValT StateT: Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).
  Hypothesis (valT_dec : forall v1 v2 : ValT, {v1 = v2} + {v1 <> v2}).

  Local Notation System := (System MsgT ValT StateT).

  Theorem linear_sequential_compositional:
    forall sys: System,
      MonotoneSys msgT_dec sys ->
      Forall (fun obj => SequentialSys msgT_dec valT_dec (obj :: nil)) sys ->
      Linear msgT_dec valT_dec sys.
  Proof.
  Admitted.

  Corollary disjoint_linear:
    forall sys: System,
      MonotoneSys msgT_dec sys ->
      Forall (LocallyDisjoint msgT_dec) sys ->
      Linear msgT_dec valT_dec sys.
  Proof.
    intros; apply linear_sequential_compositional; auto.
    apply Forall_impl with (P:= LocallyDisjoint msgT_dec); auto.
    intros; apply locally_disjoint_sequential; auto.
  Qed.

  Theorem prioritized_interf_linear_compositional:
    forall sys: System,
      MonotoneSys msgT_dec sys ->
      Forall (fun obj => Linear msgT_dec valT_dec (obj :: nil)) sys ->
      Forall (PInterfering msgT_dec) sys ->
      Linear msgT_dec valT_dec sys.
  Proof.
  Admitted.

End Facts.

