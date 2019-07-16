Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition mesiMsgBase: IdxT := 0.

Definition mesiRqS: IdxT := mesiMsgBase~>0.
Definition mesiRsS: IdxT := mesiMsgBase~>1.
Definition mesiRsE: IdxT := mesiMsgBase~>2.

Definition mesiDownRqS: IdxT := mesiMsgBase~>3.
Definition mesiDownRsS: IdxT := mesiMsgBase~>4.

Definition mesiRqM: IdxT := mesiMsgBase~>5.
Definition mesiRsM: IdxT := mesiMsgBase~>6.
Definition mesiDownRqI: IdxT := mesiMsgBase~>7.
Definition mesiDownRsI: IdxT := mesiMsgBase~>8.

Definition mesiRqI: IdxT := mesiMsgBase~>9.
Definition mesiRsI: IdxT := mesiMsgBase~>10.

(** Cache Status *)

Notation MESI := nat (only parsing).
Definition mesiM: MESI := 3.
Definition mesiE: MESI := 2.
Definition mesiS: MESI := 1.
Definition mesiI: MESI := 0.

