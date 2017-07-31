Require Import List String Peano_dec.
Require Import FnMap Language.

Set Implicit Arguments.

Section Reduction.
  Variable MsgT StateT: Type.

  Local Notation MsgId := (MsgId MsgT).
  Local Notation Label := (Label MsgT).

  Definition Reduced (from to: list Label) (lbl1 lbl2: Label) :=
    exists hst1 hst2,
      from = hst1 ++ lbl1 :: lbl2 :: hst2 /\
      to = hst1 ++ lbl2 :: lbl1 :: hst2.

End Reduction.
        
