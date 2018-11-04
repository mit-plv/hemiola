Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Spec.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

(** Message Ids *)

Definition msiRqS: IdxT := specNumMsgIds + 0.
Definition msiRsS: IdxT := specNumMsgIds + 1.
Definition msiDownRqS: IdxT := specNumMsgIds + 2.
Definition msiDownRsS: IdxT := specNumMsgIds + 3.

Definition msiRqM: IdxT := specNumMsgIds + 4.
Definition msiRsM: IdxT := specNumMsgIds + 5.
Definition msiDownRqM: IdxT := specNumMsgIds + 6.
Definition msiDownRsM: IdxT := specNumMsgIds + 7.

Definition msiRqI: IdxT := specNumMsgIds + 8.
Definition msiRsI: IdxT := specNumMsgIds + 9.

(** Cache Status *)

Definition msiM := 2.
Definition msiS := 1.
Definition msiI := 0.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

