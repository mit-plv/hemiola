Require Import Bool List String Peano_dec.
Require Import FnMap Language Transaction.

Section History.
  Variables MsgT StateT: Type.

  Local Notation MsgId := (MsgId MsgT).
  Local Notation Object := (Object MsgT StateT).
  Local Notation System := (System MsgT StateT).

  (* Inductive TrsSeq: list MsgId -> Prop := *)

End History.

