Require Import List String Peano_dec.
Require Import FnMap Language.

Set Implicit Arguments.

Section Reduction.
  Context {MsgT IStateT SStateT: Type}.
  Context {MvalT: MsgT -> RqRs -> Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).

  Local Notation MsgId := (MsgId MsgT).
  Local Notation Label := (Label MvalT).

  Definition Reduced (from to: list Label) (lbl1 lbl2: Label) :=
    exists hst1 hst2,
      from = hst1 ++ lbl1 :: lbl2 :: hst2 /\
      to = hst1 ++ lbl2 :: lbl1 :: hst2.

End Reduction.
        
