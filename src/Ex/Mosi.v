Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition mosiRqS: IdxT := specNumMsgIds + 0.
Definition mosiRsS: IdxT := specNumMsgIds + 1.
Definition mosiDownRqS: IdxT := specNumMsgIds + 2.
Definition mosiDownRsS: IdxT := specNumMsgIds + 3.

Definition mosiRqM: IdxT := specNumMsgIds + 4.
Definition mosiRsM: IdxT := specNumMsgIds + 5.
Definition mosiDownRqM: IdxT := specNumMsgIds + 6.
Definition mosiDownRsM: IdxT := specNumMsgIds + 7.

Definition mosiRqI: IdxT := specNumMsgIds + 8.
Definition mosiRsI: IdxT := specNumMsgIds + 9.

(** Cache Status *)

Definition mosiM := 3.
Definition mosiO := 2.
Definition mosiS := 1.
Definition mosiI := 0.

