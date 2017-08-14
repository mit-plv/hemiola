Require Import Bool List String Peano_dec.
Require Import FunctionalExtensionality.
Require Import Tactics FMap Language.

Section Facts.
  Variable MsgT: Type.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).
  Variable ValT: Type.
  Hypothesis (valT_dec: forall m1 m2: ValT, {m1 = m2} + {m1 <> m2}).
  Variable StateT: Type.

  Local Notation Msg := (Msg MsgT ValT).
  Local Notation Label := (Label MsgT ValT).
  Local Notation step_sys := (step_sys msgT_dec valT_dec).
  Local Notation System := (System MsgT ValT StateT).

  Definition ValidLabel (l: Label) :=
    match lbl_hdl l with
    | Some hdl => lbl_ins l = nil /\ ValidOuts (msgTo (msg_id hdl)) (lbl_outs l)
    | None => lbl_outs l = nil
    end.

  Lemma step_sys_validLabel:
    forall (sys: System) st1 l st2, step_sys sys st1 l st2 -> ValidLabel l.
  Proof.
  Admitted.

End Facts.

