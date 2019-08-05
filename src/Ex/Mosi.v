Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition mosiMsgBase: IdxT := 0.

Definition mosiRqS: IdxT := mosiMsgBase~>0.
Definition mosiRsS: IdxT := mosiMsgBase~>1.

Definition mosiDownRqS: IdxT := mosiMsgBase~>3.
Definition mosiDownRsS: IdxT := mosiMsgBase~>4.

Definition mosiRqM: IdxT := mosiMsgBase~>5.
Definition mosiRsM: IdxT := mosiMsgBase~>6.
Definition mosiDownRqI: IdxT := mosiMsgBase~>7.
Definition mosiDownRsI: IdxT := mosiMsgBase~>8.

Definition mosiRqI: IdxT := mosiMsgBase~>9.
Definition mosiRsI: IdxT := mosiMsgBase~>10.

(** Cache Status *)

Notation MOSI := nat (only parsing).
Definition mosiM: MOSI := 3.
Definition mosiO: MOSI := 2.
Definition mosiS: MOSI := 1.
Definition mosiI: MOSI := 0.

