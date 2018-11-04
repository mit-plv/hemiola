Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

(** Message Ids *)

Definition getRq: IdxT := 0.
Definition getRs: IdxT := 1.
Definition setRq: IdxT := 2.
Definition setRs: IdxT := 3.
Definition specNumMsgIds := 4.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

