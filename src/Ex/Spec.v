Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Set Implicit Arguments.

(** Message Ids *)

Definition getRq: IdxT := 0.
Definition getRs: IdxT := 1.
Definition setRq: IdxT := 2.
Definition setRs: IdxT := 3.
Definition evictRq: IdxT := 4.
Definition evictRs: IdxT := 5.
Definition specNumMsgIds := 6.

